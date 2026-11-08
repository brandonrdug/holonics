//! **A value in its canonical fibre form** (N1, N3, N4): a class on the open ray of places, read at its
//! grain, with the width its operations derived and the section it reads.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::{refuse, Count, Grain, Result, Width};

/// **A section**: which representative of each class a value reads (the record's §2.4: `u64` and `i64` are
/// one ring with two sections).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Section {
    /// `[0, 2^w)`: the low representatives.
    Low,
    /// `[−2^(w−1), 2^(w−1))`: the top place carries weight `−2^(w−1)` (the 2-adic tail of ones summed into
    /// one place).
    TwosComplement,
    /// `(−2^(w−1), 2^(w−1)]` on a ring, the residue nearest zero; on the ray, as [`Section::TwosComplement`]
    /// with the top representative.
    Balanced,
    /// A half-turn state beside the magnitude's `w − 1` places: two zeros, `2^w − 1` values.
    SignMagnitude,
}

impl Section {
    /// Whether the section holds negative representatives.
    pub fn signed(self) -> bool {
        !matches!(self, Section::Low)
    }

    /// The section a sum, difference or product of two values reads: low only where both are low and the
    /// operation keeps sign.
    fn join(self, other: Section) -> Section {
        if self == Section::Low && other == Section::Low {
            Section::Low
        } else {
            Section::TwosComplement
        }
    }
}

/// The digits' realization inside the owner: a machine word pair where the class fits it, wider limbs beyond.
/// Nothing outside the owner sees it.
#[derive(Clone, Debug)]
pub(crate) enum Digits {
    Small(i128),
    Big(BigInt),
}

impl Digits {
    pub(crate) fn zero() -> Self {
        Digits::Small(0)
    }

    pub(crate) fn from_big(v: BigInt) -> Self {
        match v.to_i128() {
            Some(s) => Digits::Small(s),
            None => Digits::Big(v),
        }
    }

    pub(crate) fn big(&self) -> BigInt {
        match self {
            Digits::Small(s) => BigInt::from(*s),
            Digits::Big(b) => b.clone(),
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        match self {
            Digits::Small(s) => *s == 0,
            Digits::Big(b) => b.is_zero(),
        }
    }

    pub(crate) fn negative(&self) -> bool {
        match self {
            Digits::Small(s) => *s < 0,
            Digits::Big(b) => b.is_negative(),
        }
    }

    pub(crate) fn add(&self, other: &Digits) -> Digits {
        match (self, other) {
            (Digits::Small(a), Digits::Small(b)) => a.checked_add(*b).map_or_else(|| Digits::from_big(BigInt::from(*a) + BigInt::from(*b)), Digits::Small),
            _ => Digits::from_big(self.big() + other.big()),
        }
    }

    pub(crate) fn sub(&self, other: &Digits) -> Digits {
        match (self, other) {
            (Digits::Small(a), Digits::Small(b)) => a.checked_sub(*b).map_or_else(|| Digits::from_big(BigInt::from(*a) - BigInt::from(*b)), Digits::Small),
            _ => Digits::from_big(self.big() - other.big()),
        }
    }

    pub(crate) fn neg(&self) -> Digits {
        match self {
            Digits::Small(a) => a.checked_neg().map_or_else(|| Digits::from_big(-BigInt::from(*a)), Digits::Small),
            Digits::Big(b) => Digits::from_big(-b.clone()),
        }
    }

    pub(crate) fn mul(&self, other: &Digits) -> Digits {
        match (self, other) {
            (Digits::Small(a), Digits::Small(b)) => a.checked_mul(*b).map_or_else(|| Digits::from_big(BigInt::from(*a) * BigInt::from(*b)), Digits::Small),
            _ => Digits::from_big(self.big() * other.big()),
        }
    }

    /// `self · 2^k`.
    pub(crate) fn shl(&self, k: u32) -> Digits {
        match self {
            Digits::Small(a) if k < 127 && (a.unsigned_abs().leading_zeros() > k + 1) => Digits::Small(a << k),
            _ => Digits::from_big(self.big() << k as usize),
        }
    }

    /// `⌊self / 2^k⌋` and the remainder `self − 2^k ⌊self / 2^k⌋` in `[0, 2^k)`.
    pub(crate) fn floor_split(&self, k: u32) -> (Digits, Digits) {
        match self {
            Digits::Small(a) if k < 127 => {
                let q = a >> k;
                (Digits::Small(q), Digits::Small(a - (q << k)))
            }
            Digits::Small(a) => {
                // k ≥ 127: every i128 lies in [−2^127, 2^127), so the floor is 0 or −1.
                if *a < 0 {
                    let one = BigInt::one() << k as usize;
                    (Digits::Small(-1), Digits::from_big(BigInt::from(*a) + one))
                } else {
                    (Digits::Small(0), Digits::Small(*a))
                }
            }
            Digits::Big(b) => {
                let q: BigInt = b >> k as usize;
                let r = b - (&q << k as usize);
                (Digits::from_big(q), Digits::from_big(r))
            }
        }
    }

    /// The places the class occupies in a section: the least `w` with the digits inside it.
    pub(crate) fn places_in(&self, section: Section) -> u32 {
        if let Digits::Small(s) = *self {
            // The word's own count of places, with no limb built (the inline realization's cost law).
            let bits = |m: u128| u128::BITS - m.leading_zeros();
            return match section {
                Section::Low if s < 0 => u32::MAX,
                Section::Low => bits(s as u128),
                // −s − 1 is !s: its places, plus the sign's.
                Section::TwosComplement | Section::Balanced if s < 0 => bits(!s as u128) + 1,
                Section::TwosComplement | Section::Balanced => bits(s as u128) + 1,
                Section::SignMagnitude => bits(s.unsigned_abs()) + 1,
            };
        }
        let b = self.big();
        match section {
            Section::Low => {
                if b.is_negative() {
                    u32::MAX
                } else {
                    b.bits() as u32
                }
            }
            Section::TwosComplement | Section::Balanced => {
                // The least w with −2^(w−1) ≤ b < 2^(w−1).
                if b.is_negative() {
                    let m: BigInt = -b - 1;
                    m.bits() as u32 + 1
                } else {
                    b.bits() as u32 + 1
                }
            }
            Section::SignMagnitude => b.abs().bits() as u32 + 1,
        }
    }

    pub(crate) fn cmp(&self, other: &Digits) -> std::cmp::Ordering {
        match (self, other) {
            (Digits::Small(a), Digits::Small(b)) => a.cmp(b),
            _ => self.big().cmp(&other.big()),
        }
    }
}

/// **A value on the open ray** (the integer of the theory, which widens): its grain, its width (a need its
/// operations derived), its section and its digits. Its value is `digits · 2^lo`. It has no public constructor
/// from a native integer: natives enter through a [`super::Register`] preset's declared read.
#[derive(Clone, Debug)]
pub struct Value {
    pub(crate) grain: Grain,
    pub(crate) width: Width,
    pub(crate) section: Section,
    pub(crate) digits: Digits,
}

impl Value {
    pub(crate) fn of(grain: Grain, width: Width, section: Section, digits: Digits) -> Result<Self> {
        if digits.places_in(section) > width.places() {
            return refuse("a value's digits outside its width in its section");
        }
        Ok(Self { grain, width, section, digits })
    }

    /// The zero at a grain, one place wide.
    pub fn zero(grain: Grain) -> Self {
        Self { grain, width: Width::new(1), section: Section::Low, digits: Digits::zero() }
    }

    pub fn grain(&self) -> Grain {
        self.grain
    }

    pub fn width(&self) -> Width {
        self.width
    }

    pub fn section(&self) -> Section {
        self.section
    }

    pub fn is_zero(&self) -> bool {
        self.digits.is_zero()
    }

    pub fn is_negative(&self) -> bool {
        self.digits.negative()
    }

    /// The places the class actually uses at its grain in its section (its measured need, beside its width).
    pub fn used(&self) -> Width {
        Width::new(self.digits.places_in(self.section))
    }

    /// A value whose fit the operation's width law (N3) already proves: the constructor's check is a guard
    /// in debug builds, not a cost each operation pays.
    fn needed(grain: Grain, width: Width, section: Section, digits: Digits) -> Value {
        debug_assert!(digits.places_in(section) <= width.places(), "an operation's width law did not hold");
        Value { grain, width, section, digits }
    }

    /// The places the value needs read in a signed section: its width where its section is signed, one more
    /// where it is low (a low class of `w` places needs `w + 1` two's-complement places).
    fn signed_places(&self) -> u32 {
        if self.section == Section::Low {
            self.width.places() + 1
        } else {
            self.width.places()
        }
    }

    /// The same class read at a finer grain `lo ≤ self.lo`: the digits move up `self.lo − lo` places and the
    /// width with them (no information enters or leaves).
    pub fn at_grain(&self, grain: Grain) -> Result<Value> {
        let k = i64::from(self.grain.lo()) - i64::from(grain.lo());
        if k < 0 {
            return refuse("a value read at a coarser grain needs a release");
        }
        let k = u32::try_from(k).map_err(|_| super::NumberError::Refused("a grain change past its count"))?;
        if k == 0 {
            return Ok(self.clone());
        }
        Ok(Value::needed(grain, Width::new(self.width.places() + k), self.section, self.digits.shl(k)))
    }

    /// The two values at their common (finer) grain.
    fn aligned(&self, other: &Value) -> Result<(Value, Value)> {
        let lo = Grain::new(self.grain.lo().min(other.grain.lo()));
        Ok((self.at_grain(lo)?, other.at_grain(lo)?))
    }

    /// The width a sum or difference of two values needs (N3): the wider plus one where both are low (a sum)
    /// or both read one section kind, and the wider of their signed places plus one where they mix.
    fn of_pair(a: &Value, b: &Value, both_low: bool) -> Width {
        if both_low {
            Width::new(a.width.places().max(b.width.places()) + 1)
        } else if a.section.signed() == b.section.signed() {
            Width::new(a.width.places().max(b.width.places()) + 1)
        } else {
            Width::new(a.signed_places().max(b.signed_places()) + 1)
        }
    }

    /// The sum: at the common grain, its width the law's need (N3).
    pub fn add(&self, other: &Value) -> Result<Value> {
        if self.grain == other.grain {
            let section = self.section.join(other.section);
            let width = Value::of_pair(self, other, section == Section::Low);
            return Ok(Value::needed(self.grain, width, section, self.digits.add(&other.digits)));
        }
        let (a, b) = self.aligned(other)?;
        a.add(&b)
    }

    /// The difference: signed, its width the law's need (N3).
    pub fn sub(&self, other: &Value) -> Result<Value> {
        if self.grain == other.grain {
            let both_low = self.section == Section::Low && other.section == Section::Low;
            let width = Value::of_pair(self, other, both_low);
            return Ok(Value::needed(self.grain, width, Section::TwosComplement, self.digits.sub(&other.digits)));
        }
        let (a, b) = self.aligned(other)?;
        a.sub(&b)
    }

    /// The negation: signed, one place wider.
    pub fn neg(&self) -> Result<Value> {
        Ok(Value::needed(self.grain, Width::new(self.width.places() + 1), Section::TwosComplement, self.digits.neg()))
    }

    /// The product: at grain `lo_a + lo_b`, width `w_a + w_b` (N3), in every pair of sections.
    pub fn mul(&self, other: &Value) -> Result<Value> {
        let grain = Grain::new(self.grain.lo().checked_add(other.grain.lo()).ok_or(super::NumberError::Refused("a product's grain past its count"))?);
        Ok(Value::needed(grain, Width::of_product(self.width, other.width), self.section.join(other.section), self.digits.mul(&other.digits)))
    }

    /// Multiplication by `2^k` moves the grain, never the digits: a shift moves places.
    pub fn scaled(&self, k: i32) -> Result<Value> {
        let lo = self.grain.lo().checked_add(k).ok_or(super::NumberError::Refused("a shift's grain past its count"))?;
        Ok(Value::needed(Grain::new(lo), self.width, self.section, self.digits.clone()))
    }

    /// The sum of many values, in any order (integer addition is associative, so every bracketing gives the
    /// same class): its width the widest term's plus `⌈log₂ n⌉` (N3), the widest read in signed places where
    /// any term is signed.
    pub fn sum(values: &[Value]) -> Result<Value> {
        let Some(first) = values.first() else { return refuse("a sum of no values has no grain") };
        let lo = Grain::new(values.iter().map(|v| v.grain.lo()).min().unwrap_or(first.grain.lo()));
        let mut digits = Digits::zero();
        let (mut widest, mut widest_signed) = (1u32, 1u32);
        let mut section = Section::Low;
        for v in values {
            let a = v.at_grain(lo)?;
            widest = widest.max(a.width.places());
            widest_signed = widest_signed.max(a.signed_places());
            section = section.join(a.section);
            digits = digits.add(&a.digits);
        }
        let need = if section == Section::Low { widest } else { widest_signed };
        Ok(Value::needed(lo, Width::of_terms(Width::new(need), Count::new(values.len() as u64)), section, digits))
    }

    /// The same class in another section (N8's section change), refused where the class lies outside it.
    pub fn in_section(&self, section: Section) -> Result<Value> {
        let width = Width::new(self.width.places().max(self.digits.places_in(section)));
        if self.digits.places_in(section) == u32::MAX {
            return refuse("a negative class in the low section");
        }
        Value::of(self.grain, width, section, self.digits.clone())
    }

    /// Class equality: the same number, whatever the grains, widths and sections that read it.
    pub fn same(&self, other: &Value) -> bool {
        match self.aligned(other) {
            Ok((a, b)) => a.digits.cmp(&b.digits) == std::cmp::Ordering::Equal,
            Err(_) => false,
        }
    }

    /// The order of two classes.
    pub fn order(&self, other: &Value) -> Result<std::cmp::Ordering> {
        let (a, b) = self.aligned(other)?;
        Ok(a.digits.cmp(&b.digits))
    }
}

impl PartialEq for Value {
    /// Equal as values of the theory: the same class at the same grain, width and section.
    fn eq(&self, other: &Self) -> bool {
        self.grain == other.grain && self.width == other.width && self.section == other.section && self.digits.cmp(&other.digits) == std::cmp::Ordering::Equal
    }
}

impl Eq for Value {}
