//! **The closing edge** (N2): the place graph's modulus. An open ray widens; a path of `n` places, a ring,
//! a twisted (Möbius) ring, a weighted closing, a Solinas closing and coprime rings each close the graph, and
//! every reduction onto them returns its **winding**, the whole turns the carries made round the closing
//! circuit, so nothing wraps silently.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

use super::value::{Digits, Section, Value};
use super::{refuse, Grain, Result, Width};

/// **A closing edge** of the place graph (the record's §2.2 table).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Closing {
    /// The open ray: the integer, which widens.
    Ray,
    /// A path of `n` places, `Z/2^n`: the carry that leaves its top place is its winding.
    Path(u32),
    /// A ring of `n` places, `Z/(2^n − 1)`: the top carry enters the bottom place (the end-around carry).
    Ring(u32),
    /// A twisted ring, `Z/(2^n + 1)`: the top carry enters the bottom place with its sign turned.
    Twist(u32),
    /// A closing weight `c`, `Z/(2^n − c)`.
    Weighted(u32, u64),
    /// Two or more closing edges, `Z/(2^n − Σ_r 2^r)` (the Solinas form; `2^n − 2^m − 1` has returns `[m, 0]`).
    Solinas(u32, Vec<u32>),
    /// Residues on rings of the given lengths, which must be pairwise coprime: lane by lane with no carry
    /// between them, the mixed-radix reconstruction their only carry.
    Rings(Vec<u32>),
}

impl Closing {
    /// The modulus the closing edge sets (`None` for the open ray and for coprime rings, read lane by lane).
    pub(crate) fn modulus(&self) -> Option<BigInt> {
        let two = |n: u32| BigInt::one() << n as usize;
        match self {
            Closing::Ray | Closing::Rings(_) => None,
            Closing::Path(n) => Some(two(*n)),
            Closing::Ring(n) => Some(two(*n) - 1),
            Closing::Twist(n) => Some(two(*n) + 1),
            Closing::Weighted(n, c) => Some(two(*n) - BigInt::from(*c)),
            Closing::Solinas(n, returns) => Some(two(*n) - returns.iter().map(|&r| two(r)).sum::<BigInt>()),
        }
    }

    /// The width a residue on this closing occupies in the low section.
    pub(crate) fn residue_width(&self) -> Option<Width> {
        self.modulus().map(|m| Width::new((m - 1u32).bits() as u32))
    }
}

/// **A winding**: the whole turns a reduction made round its closing circuit, `⌊x / m⌋`, on the open ray.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Winding(pub Value);

/// **A residue** on a closing edge: the low representative in `[0, m)` (or, on coprime rings, each ring's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Residue {
    pub closing: Closing,
    /// The residue's value in the low section at grain one (or each ring's, on coprime rings).
    pub lanes: Vec<Value>,
}

fn ray(digits: BigInt) -> Result<Value> {
    let digits = Digits::from_big(digits);
    let w = digits.places_in(Section::TwosComplement).max(1);
    Value::of(Grain::new(0), Width::new(w), Section::TwosComplement, digits)
}

fn low(digits: BigInt, width: Width) -> Result<Value> {
    Value::of(Grain::new(0), width, Section::Low, Digits::from_big(digits))
}

impl Residue {
    /// **The reduction onto a closing edge**: a value at grain one read on the closing, with its winding. On
    /// coprime rings the winding is each ring's, lane by lane.
    pub fn of(value: &Value, closing: &Closing) -> Result<(Residue, Vec<Winding>)> {
        if value.grain().lo() != 0 {
            return refuse("a reduction reads a value at grain one; release or scale it there first");
        }
        let x = value.digits.big();
        match closing {
            Closing::Ray => Ok((Residue { closing: Closing::Ray, lanes: vec![value.clone()] }, vec![Winding(ray(BigInt::zero())?)])),
            Closing::Rings(lengths) => {
                for (i, &a) in lengths.iter().enumerate() {
                    for &b in &lengths[i + 1..] {
                        if a.gcd(&b) != 1 {
                            return refuse("coprime rings need pairwise coprime lengths");
                        }
                    }
                }
                let mut lanes = Vec::with_capacity(lengths.len());
                let mut windings = Vec::with_capacity(lengths.len());
                for &n in lengths {
                    let m = (BigInt::one() << n as usize) - 1;
                    let (q, r) = x.div_mod_floor(&m);
                    lanes.push(low(r, Width::new(n))?);
                    windings.push(Winding(ray(q)?));
                }
                Ok((Residue { closing: closing.clone(), lanes }, windings))
            }
            _ => {
                let m = closing.modulus().ok_or(super::NumberError::Refused("a closing without a modulus"))?;
                if m <= BigInt::zero() {
                    return refuse("a closing whose modulus is not positive");
                }
                let (q, r) = x.div_mod_floor(&m);
                let width = closing.residue_width().unwrap_or(Width::new(1)).max(Width::new(1));
                Ok((Residue { closing: closing.clone(), lanes: vec![low(r, width)?] }, vec![Winding(ray(q)?)]))
            }
        }
    }

    /// The sum of two residues on one closing, reduced, with the winding the sum made.
    pub fn add(&self, other: &Residue) -> Result<(Residue, Vec<Winding>)> {
        self.combine(other, |a, b| a + b)
    }

    /// The product of two residues on one closing, reduced, with its winding.
    pub fn mul(&self, other: &Residue) -> Result<(Residue, Vec<Winding>)> {
        self.combine(other, |a, b| a * b)
    }

    fn combine(&self, other: &Residue, op: impl Fn(BigInt, BigInt) -> BigInt) -> Result<(Residue, Vec<Winding>)> {
        if self.closing != other.closing || self.lanes.len() != other.lanes.len() {
            return refuse("residues on different closings");
        }
        match &self.closing {
            Closing::Rings(lengths) => {
                let mut lanes = Vec::with_capacity(lengths.len());
                let mut windings = Vec::with_capacity(lengths.len());
                for ((a, b), &n) in self.lanes.iter().zip(&other.lanes).zip(lengths) {
                    let m = (BigInt::one() << n as usize) - 1;
                    let (q, r) = op(a.digits.big(), b.digits.big()).div_mod_floor(&m);
                    lanes.push(low(r, Width::new(n))?);
                    windings.push(Winding(ray(q)?));
                }
                Ok((Residue { closing: self.closing.clone(), lanes }, windings))
            }
            closing => {
                let raw = op(self.lanes[0].digits.big(), other.lanes[0].digits.big());
                Residue::of(&ray(raw)?, closing)
            }
        }
    }

    /// **The mixed-radix reconstruction** of residues on coprime rings: the one carry between their lanes,
    /// the class in `[0, Π m_i)`.
    pub fn reconstruct(&self) -> Result<Value> {
        match &self.closing {
            Closing::Rings(lengths) => {
                let mut x = BigInt::zero();
                let mut m = BigInt::one();
                for (lane, &n) in self.lanes.iter().zip(lengths) {
                    let mi = (BigInt::one() << n as usize) - 1;
                    // x ≡ x (mod m), x ≡ r (mod mi): x += m · ((r − x) · m⁻¹ mod mi).
                    let r = lane.digits.big();
                    let inv = mod_inverse(&(&m % &mi), &mi).ok_or(super::NumberError::Refused("rings that are not coprime"))?;
                    let t = ((r - &x) * inv).mod_floor(&mi);
                    x += &m * t;
                    m *= mi;
                }
                let width = Width::new((&m - 1u32).bits() as u32);
                low(x, width.max(Width::new(1)))
            }
            Closing::Ray => Ok(self.lanes[0].clone()),
            _ => Ok(self.lanes[0].clone()),
        }
    }
}

/// The inverse of `a` modulo `m` by Euclid's shear word, `None` where they share a factor.
pub(crate) fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let e = a.extended_gcd(m);
    if e.gcd != BigInt::one() {
        return None;
    }
    Some(e.x.mod_floor(m))
}
