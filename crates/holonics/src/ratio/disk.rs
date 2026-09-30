//! **Complex disks with exact dyadic endpoints, and a simple root certified by the Krawczyk test.**
//!
//! [definition; agent-inferred, September 30] A complex algebraic value (a multiplier of a
//! monodromy, an entry of its eigenvectors) is its constraint identity; a face of it is a disk
//! `D(c, r) = {z : |z − c| ≤ r}` with a Gaussian dyadic center and a dyadic radius that provably
//! contains it ([`Disk`]). Every operation is outward: it returns a disk containing every value
//! its operands' disks can produce, its center held at `bits` significant bits and the rounding
//! added to the radius. Nothing here is a float, and nothing a disk states is estimated: a disk
//! is an enclosure with exact endpoints, the reading the governing laws admit for an algebraic
//! value (CLAUDE.md, "Exact arithmetic").
//!
//! - **Products and inverses.** `D(a, r)·D(b, s) ⊂ D(ab, |a|s + |b|r + rs)`; a disk not
//!   containing zero inverts exactly to a disk (a Möbius map sends circles to circles):
//!   `1/D(c, r) = D(c̄/(|c|² − r²), r/(|c|² − r²))` for `|c| > r` ([`Disk::inverse`]).
//! - **The Krawczyk test** [proved-standard] ([`krawczyk`]). For a polynomial `p`, a center `z̃`,
//!   any preconditioner `Y ≠ 0` and `D = D(z̃, r)`: every `z ∈ D` has
//!   `z − Y p(z) = z̃ − Y p(z̃) + (1 − Y s)(z − z̃)` with `s` in the convex hull of `p′(D)` (the mean
//!   value along the segment, `D` convex), so `K(D) = z̃ − Y p(z̃) + (1 − Y p′(D))(D − z̃)` contains
//!   the image of `D` under `z ↦ z − Y p(z)`. If `K(D)` lies in `D`'s interior, that map sends
//!   `D` into itself and has a fixed point, a root of `p`; two roots `z₁ ≠ z₂` in `D` would give a
//!   slope `s = 0` in the hull, `|1 − Y·0| = 1`, against `|1 − Y s| r < r`; so the root is unique,
//!   and `p′` vanishes nowhere on the hull, so it is simple. Read on disks, the test is
//!   `|Y p(z̃)| + |1 − Y p′(D)| r < r`, each modulus at its upper bound.
//! - **The attainment** ([`attained_roots`], Weierstrass–Durand–Kerner on dyadic Gaussian
//!   centers) is an exterior means, trusted nowhere: only a disk the Krawczyk test passes is
//!   returned ([`isolate`]).
//!
//! Its consumer is the receiving bank's growth covector (`hnn::ring`, "The executed growth's
//! covector"): the dominant multiplier of a member's monodromy is isolated in a disk, and its
//! eigenvectors are read through the disk.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{GaussianRat, Rat};

/// `⌊log₂ q⌋` for `q > 0`.
pub(crate) fn floor_log2(q: &Rat) -> i64 {
    let (p, r) = (q.numer().magnitude(), q.denom().magnitude());
    let k = p.bits() as i64 - r.bits() as i64;
    let at_least = if k >= 0 {
        *p >= (r << k as usize)
    } else {
        (p << (-k) as usize) >= *r
    };
    if at_least { k } else { k - 1 }
}

/// `2^k`.
fn dyadic(k: i64) -> Rat {
    if k >= 0 {
        Rat::from_integer(BigInt::one() << k as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
    }
}

/// `x` at the nearest multiple of `2^e`, ties upward: within `2^(e−1)` of `x`.
fn nearest_at(x: &Rat, e: i64) -> Rat {
    let scaled = x * dyadic(-e) + Rat::new(BigInt::one(), BigInt::from(2));
    Rat::from_integer(scaled.floor().to_integer()) * dyadic(e)
}

/// The least dyadic at 32 significant bits at or above a nonnegative `x`.
fn ceiling_face(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let shift = 31 - floor_log2(x);
    Rat::from_integer((x * dyadic(shift)).ceil().to_integer()) * dyadic(-shift)
}

/// The grain at which a square root of `x > 0` is read: `2^(−p)` with `p` so that the root is
/// held within about `2^(−40)` of itself.
fn root_grain(x: &Rat) -> u32 {
    u32::try_from((40 - floor_log2(x).div_euclid(2)).max(0)).expect("a grain below 2^32")
}

/// **An upper bound on `√x`** for `x ≥ 0`: the least `m·2^(−p)` with `(m·2^(−p))² ≥ x`.
pub fn root_upper(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let p = root_grain(x);
    let scaled = (x * dyadic(2 * i64::from(p))).ceil().to_integer();
    let magnitude = scaled.magnitude();
    let mut root = magnitude.sqrt();
    if &(&root * &root) < magnitude {
        root += 1u32;
    }
    Rat::new(BigInt::from(root), BigInt::one() << p as usize)
}

/// **A lower bound on `√x`** for `x ≥ 0`: the greatest `m·2^(−p)` with `(m·2^(−p))² ≤ x`.
pub fn root_lower(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let p = root_grain(x);
    let scaled = (x * dyadic(2 * i64::from(p))).floor().to_integer();
    Rat::new(
        BigInt::from(scaled.magnitude().sqrt()),
        BigInt::one() << p as usize,
    )
}

/// [definition; agent-inferred, September 30] **A complex disk with exact dyadic endpoints**
/// (module header): every value it stands for lies within `radius` of `center`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Disk {
    pub center: GaussianRat,
    pub radius: Rat,
}

impl Disk {
    /// The exact point `z` (radius zero).
    pub fn point(center: GaussianRat) -> Self {
        Self {
            center,
            radius: Rat::zero(),
        }
    }

    /// The exact real `x`.
    pub fn real(x: Rat) -> Self {
        Self::point(GaussianRat::real(x))
    }

    /// A disk about `center` of `radius ≥ 0`.
    pub fn new(center: GaussianRat, radius: Rat) -> Self {
        Self { center, radius }
    }

    /// `|c| + r`, an upper bound on every modulus in the disk.
    pub fn modulus_upper(&self) -> Rat {
        root_upper(&self.center.norm_sq()) + &self.radius
    }

    /// `max(|c| − r, 0)`, a lower bound on every modulus in the disk.
    pub fn modulus_lower(&self) -> Rat {
        let lower = root_lower(&self.center.norm_sq()) - &self.radius;
        if lower.is_positive() {
            lower
        } else {
            Rat::zero()
        }
    }

    /// Whether zero lies outside the disk: `|c| > r`, decided exactly on squares.
    pub fn excludes_zero(&self) -> bool {
        self.center.norm_sq() > &self.radius * &self.radius
    }

    /// `[Re c − r, Re c + r]`, every real part in the disk.
    pub fn real_part(&self) -> ExactInterval {
        ExactInterval {
            lower: &self.center.re - &self.radius,
            upper: &self.center.re + &self.radius,
        }
    }

    /// The conjugate disk.
    pub fn conj(&self) -> Self {
        Self::new(self.center.conj(), self.radius.clone())
    }

    /// **Held at `bits` significant bits**: the center at the nearest multiple of `2^(e − bits)`,
    /// `2^e` its larger coordinate's magnitude, each coordinate within half that grain, so the
    /// rounding moves it by less than the grain, which the radius gains; the radius at its
    /// 32-bit ceiling.
    pub fn held(self, bits: u32) -> Self {
        let widest = self.center.re.abs().max(self.center.im.abs());
        if widest.is_zero() {
            return Self::new(self.center, ceiling_face(&self.radius));
        }
        let grain = floor_log2(&widest) - i64::from(bits);
        let center = GaussianRat::new(
            nearest_at(&self.center.re, grain),
            nearest_at(&self.center.im, grain),
        );
        let moved = if center == self.center {
            Rat::zero()
        } else {
            dyadic(grain)
        };
        Self::new(center, ceiling_face(&(self.radius + moved)))
    }

    /// `self + other`.
    pub fn add(&self, other: &Self, bits: u32) -> Self {
        Self::new(
            self.center.add(&other.center),
            &self.radius + &other.radius,
        )
        .held(bits)
    }

    /// `self − other`.
    pub fn sub(&self, other: &Self, bits: u32) -> Self {
        Self::new(
            self.center.sub(&other.center),
            &self.radius + &other.radius,
        )
        .held(bits)
    }

    /// `self · other`: `D(ab, |a|s + |b|r + rs)`, each `|a|` at its cheap upper bound
    /// `|Re a| + |Im a| ≥ |a|` (within `√2` of it: a radius, never a center, is overestimated).
    pub fn mul(&self, other: &Self, bits: u32) -> Self {
        let mut radius = &self.radius * &other.radius;
        if !other.radius.is_zero() {
            radius += (self.center.re.abs() + self.center.im.abs()) * &other.radius;
        }
        if !self.radius.is_zero() {
            radius += (other.center.re.abs() + other.center.im.abs()) * &self.radius;
        }
        Self::new(self.center.mul(&other.center), radius).held(bits)
    }

    /// `x · self` for a rational `x`.
    pub fn scale(&self, x: &Rat, bits: u32) -> Self {
        Self::new(self.center.scale(x), &self.radius * x.abs()).held(bits)
    }

    /// **`1/self`**, exactly the disk `D(c̄/(|c|² − r²), r/(|c|² − r²))` (module header); `None`
    /// when the disk contains zero.
    pub fn inverse(&self, bits: u32) -> Option<Self> {
        if !self.excludes_zero() {
            return None;
        }
        let gap = self.center.norm_sq() - &self.radius * &self.radius;
        Some(Self::new(self.center.conj().scale(&(Rat::one() / &gap)), &self.radius / &gap).held(bits))
    }

    /// `self / other`; `None` when `other` contains zero.
    pub fn div(&self, other: &Self, bits: u32) -> Option<Self> {
        Some(self.mul(&other.inverse(bits)?, bits))
    }

    /// Whether `other` lies in this disk's interior: `|c − c′| + r′ < r`, the distance at its
    /// upper bound.
    pub fn holds_inside(&self, other: &Self) -> bool {
        root_upper(&self.center.sub(&other.center).norm_sq()) + &other.radius < self.radius
    }

    /// Whether the two disks are disjoint: `|c − c′| > r + r′`, decided exactly on squares.
    pub fn disjoint(&self, other: &Self) -> bool {
        let reach = &self.radius + &other.radius;
        self.center.sub(&other.center).norm_sq() > &reach * &reach
    }
}

/// [definition; agent-inferred, September 30] **A dyadic** `m·2^e`: a disk's endpoint carried as its
/// mantissa and exponent, so sums align by shifts and products multiply mantissas, with no
/// reduction of a ratio ([`DyadicDisk`]).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Dyadic {
    mantissa: BigInt,
    exponent: i64,
}

impl Dyadic {
    fn zero() -> Self {
        Self {
            mantissa: BigInt::zero(),
            exponent: 0,
        }
    }

    fn power(exponent: i64) -> Self {
        Self {
            mantissa: BigInt::one(),
            exponent,
        }
    }

    fn is_zero(&self) -> bool {
        self.mantissa.is_zero()
    }

    fn to_rat(&self) -> Rat {
        Rat::from_integer(self.mantissa.clone()) * dyadic(self.exponent)
    }

    fn add(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        let exponent = self.exponent.min(other.exponent);
        let mantissa = (&self.mantissa << (self.exponent - exponent) as usize)
            + (&other.mantissa << (other.exponent - exponent) as usize);
        Self { mantissa, exponent }
    }

    fn neg(&self) -> Self {
        Self {
            mantissa: -self.mantissa.clone(),
            exponent: self.exponent,
        }
    }

    fn abs(&self) -> Self {
        Self {
            mantissa: self.mantissa.abs(),
            exponent: self.exponent,
        }
    }

    fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        Self {
            mantissa: &self.mantissa * &other.mantissa,
            exponent: self.exponent + other.exponent,
        }
    }

    /// Floored to `bits` significant bits, with the exponent `k` of its error bound (`< 2^k`), or
    /// `None` when nothing was dropped.
    fn floored(&self, bits: u32) -> (Self, Option<i64>) {
        let length = self.mantissa.bits();
        if length <= u64::from(bits) {
            return (self.clone(), None);
        }
        let drop = (length - u64::from(bits)) as i64;
        let exponent = self.exponent + drop;
        let mantissa = &self.mantissa >> drop as usize;
        (Self { mantissa, exponent }, Some(exponent))
    }

    /// A nonnegative value raised to 32 significant bits.
    fn ceiled(&self) -> Self {
        let length = self.mantissa.bits();
        if length <= 32 {
            return self.clone();
        }
        let drop = (length - 32) as i64;
        Self {
            mantissa: (&self.mantissa >> drop as usize) + 1,
            exponent: self.exponent + drop,
        }
    }

    /// A rational floored at `bits` significant bits, with its error bound's exponent.
    fn of_rat(x: &Rat, bits: u32) -> (Self, Option<i64>) {
        if x.is_zero() {
            return (Self::zero(), None);
        }
        if x.denom().is_one() {
            return Self {
                mantissa: x.numer().clone(),
                exponent: 0,
            }
            .floored(bits);
        }
        let s = i64::from(bits) - floor_log2(&x.abs());
        let scaled = x * dyadic(s);
        let exact = scaled.is_integer();
        let mantissa = scaled.floor().to_integer();
        (
            Self {
                mantissa,
                exponent: -s,
            },
            (!exact).then_some(-s),
        )
    }
}

/// [definition; agent-inferred, September 30] **A complex disk on dyadic endpoints**: the same
/// enclosure as [`Disk`], carried as mantissas and exponents so a long passage through exact
/// operands pays no reduction of ratios. Every operation is outward as [`Disk`]'s is; a disk
/// converts to and from [`Disk`] exactly (the conversion from a rational center floors it and adds
/// the floor's error to the radius).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DyadicDisk {
    re: Dyadic,
    im: Dyadic,
    radius: Dyadic,
}

impl DyadicDisk {
    /// Zero.
    pub fn zero() -> Self {
        Self {
            re: Dyadic::zero(),
            im: Dyadic::zero(),
            radius: Dyadic::zero(),
        }
    }

    /// The disk of a [`Disk`], at `bits` significant bits per coordinate.
    pub fn of(disk: &Disk, bits: u32) -> Self {
        let (re, e_re) = Dyadic::of_rat(&disk.center.re, bits);
        let (im, e_im) = Dyadic::of_rat(&disk.center.im, bits);
        let (radius, e_r) = Dyadic::of_rat(&disk.radius, 32);
        let mut radius = match e_r {
            Some(k) => radius.add(&Dyadic::power(k)),
            None => radius,
        };
        for k in [e_re, e_im].into_iter().flatten() {
            radius = radius.add(&Dyadic::power(k));
        }
        Self {
            re,
            im,
            radius: radius.ceiled(),
        }
    }

    /// The exact real `x`, at `bits` significant bits.
    pub fn real(x: &Rat, bits: u32) -> Self {
        Self::of(&Disk::real(x.clone()), bits)
    }

    /// The same enclosure as a [`Disk`].
    pub fn disk(&self) -> Disk {
        Disk::new(
            GaussianRat::new(self.re.to_rat(), self.im.to_rat()),
            self.radius.to_rat(),
        )
    }

    /// Whether it is exactly zero.
    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero() && self.radius.is_zero()
    }

    fn held(re: Dyadic, im: Dyadic, radius: Dyadic, bits: u32) -> Self {
        let (re, e_re) = re.floored(bits);
        let (im, e_im) = im.floored(bits);
        let mut radius = radius;
        for k in [e_re, e_im].into_iter().flatten() {
            radius = radius.add(&Dyadic::power(k));
        }
        Self {
            re,
            im,
            radius: radius.ceiled(),
        }
    }

    /// `self + other`.
    pub fn add(&self, other: &Self, bits: u32) -> Self {
        Self::held(
            self.re.add(&other.re),
            self.im.add(&other.im),
            self.radius.add(&other.radius),
            bits,
        )
    }

    /// `x · self` for a real dyadic disk `x` given as a disk: the general product.
    pub fn mul(&self, other: &Self, bits: u32) -> Self {
        let re = self.re.mul(&other.re).add(&self.im.mul(&other.im).neg());
        let im = self.re.mul(&other.im).add(&self.im.mul(&other.re));
        let size = |d: &Self| d.re.abs().add(&d.im.abs());
        let radius = self
            .radius
            .mul(&other.radius)
            .add(&size(self).mul(&other.radius))
            .add(&size(other).mul(&self.radius));
        Self::held(re, im, radius, bits)
    }

    /// `x · self` for an exact rational `x`, at `bits`.
    pub fn scale(&self, x: &Rat, bits: u32) -> Self {
        self.mul(&Self::real(x, bits), bits)
    }
}

/// **The disk of an exact quotient `n/(d·2^e)` of integers** (`d > 0`) at `bits` significant bits,
/// read by one integer division and no reduction of the ratio: the center `⌊n·2^s/d⌋·2^(−s−e)`
/// and the radius `2^(−s−e)` (the floor moves it by less), `s` so that the quotient carries about
/// `bits` significant bits. A quotient of integers of thousands of bits is held at the price of one
/// division, where the exact ratio's reduction would pay their gcd.
pub fn quotient(numerator: &BigInt, denominator: &BigInt, exponent: i64, bits: u32) -> Disk {
    if numerator.is_zero() {
        return Disk::real(Rat::zero());
    }
    let s = i64::from(bits) - (numerator.bits() as i64 - denominator.bits() as i64);
    let scaled = if s >= 0 {
        numerator << s as usize
    } else {
        numerator >> (-s) as usize
    };
    // Floor division (the shift of a negative numerator floors too).
    let (mut q, r) = (&scaled / denominator, &scaled % denominator);
    if r.is_negative() {
        q -= 1;
    }
    let shift = s + exponent;
    // Beside the floor, a right shift of the numerator moved it by less than one unit of 2^(−s).
    let unit = dyadic(-shift);
    let radius = if s >= 0 { unit.clone() } else { &unit * Rat::from_integer(BigInt::from(2)) };
    Disk::new(GaussianRat::real(Rat::from_integer(q) * unit), radius)
}

/// **`p(z)` over disks** by Horner, the coefficients ascending.
pub fn evaluate(coefficients: &[Disk], at: &Disk, bits: u32) -> Disk {
    let mut value = Disk::real(Rat::zero());
    for coefficient in coefficients.iter().rev() {
        value = value.mul(at, bits).add(coefficient, bits);
    }
    value
}

/// The derivative's coefficients, ascending.
pub fn derivative(coefficients: &[Disk], bits: u32) -> Vec<Disk> {
    coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(k, c)| c.scale(&Rat::from_integer(BigInt::from(k)), bits))
        .collect()
}

/// **The Krawczyk test** (module header): whether `D(center, radius)` holds exactly one root of
/// `p`, and that root simple. The preconditioner is `1/p′(z̃)`'s center, any nonzero value serving.
pub fn krawczyk(coefficients: &[Disk], center: &GaussianRat, radius: &Rat, bits: u32) -> bool {
    if !radius.is_positive() {
        return false;
    }
    let slopes = derivative(coefficients, bits);
    let at = Disk::point(center.clone());
    let value = evaluate(coefficients, &at, bits);
    let slope_at = evaluate(&slopes, &at, bits);
    let Ok(preconditioner) = slope_at.center.inverse() else {
        return false;
    };
    let preconditioner = Disk::point(preconditioner).held(bits);
    let disk = Disk::new(center.clone(), radius.clone());
    let slope = evaluate(&slopes, &disk, bits);
    let contraction = Disk::real(Rat::one()).sub(&preconditioner.mul(&slope, bits), bits);
    let shift = preconditioner.mul(&value, bits);
    shift.modulus_upper() + contraction.modulus_upper() * radius < *radius
}

/// A complex dyadic point, floored at a declared number of significant bits after every
/// operation: the attainment's carrier (trusted nowhere).
#[derive(Clone, Debug)]
struct DyadicPoint {
    re: Dyadic,
    im: Dyadic,
}

impl DyadicPoint {
    fn of(z: &GaussianRat, bits: u32) -> Self {
        Self {
            re: Dyadic::of_rat(&z.re, bits).0,
            im: Dyadic::of_rat(&z.im, bits).0,
        }
    }

    fn gaussian(&self) -> GaussianRat {
        GaussianRat::new(self.re.to_rat(), self.im.to_rat())
    }

    fn held(re: Dyadic, im: Dyadic, bits: u32) -> Self {
        Self {
            re: re.floored(bits).0,
            im: im.floored(bits).0,
        }
    }

    fn add(&self, other: &Self, bits: u32) -> Self {
        Self::held(self.re.add(&other.re), self.im.add(&other.im), bits)
    }

    fn sub(&self, other: &Self, bits: u32) -> Self {
        Self::held(self.re.add(&other.re.neg()), self.im.add(&other.im.neg()), bits)
    }

    fn mul(&self, other: &Self, bits: u32) -> Self {
        Self::held(
            self.re.mul(&other.re).add(&self.im.mul(&other.im).neg()),
            self.re.mul(&other.im).add(&self.im.mul(&other.re)),
            bits,
        )
    }

    fn norm_sq(&self) -> Dyadic {
        self.re.mul(&self.re).add(&self.im.mul(&self.im))
    }

    /// `self / other` at `bits`, `None` at a zero divisor.
    fn div(&self, other: &Self, bits: u32) -> Option<Self> {
        let norm = other.norm_sq().floored(bits).0;
        if norm.is_zero() {
            return None;
        }
        // 1/(m 2^e) = ⌊2^S/m⌋ 2^(−S−e), S = bits + |m|.
        let shift = u64::from(bits) + norm.mantissa.bits();
        let reciprocal = Dyadic {
            mantissa: (BigInt::one() << shift as usize) / &norm.mantissa,
            exponent: -(shift as i64) - norm.exponent,
        };
        let conj = Self {
            re: other.re.clone(),
            im: other.im.neg(),
        };
        let product = self.mul(&conj, bits);
        Some(Self::held(
            product.re.mul(&reciprocal),
            product.im.mul(&reciprocal),
            bits,
        ))
    }
}

/// [definition; agent-inferred] **The exterior attainment of every root** of a monic polynomial
/// (coefficients ascending, the last one): the Weierstrass–Durand–Kerner iteration
/// `z_i ← z_i − p(z_i)/∏_(j≠i)(z_i − z_j)` on complex dyadic points floored at `bits` significant
/// bits after every operation, from the points `(2/5 + 9i/10)^i` scaled by the Cauchy bound,
/// stopped when no step moves a point by more than `2^(−bits/2)` of the bound or after
/// `iterations`. Trusted nowhere: its points only seed [`isolate`].
pub fn attained_roots(coefficients: &[GaussianRat], bits: u32, iterations: usize) -> Vec<GaussianRat> {
    let n = coefficients.len().saturating_sub(1);
    if n == 0 {
        return Vec::new();
    }
    let bound = Rat::one()
        + coefficients[..n]
            .iter()
            .map(|c| root_upper(&c.norm_sq()))
            .max()
            .unwrap_or_else(Rat::zero);
    let seed = GaussianRat::new(Rat::new(2.into(), 5.into()), Rat::new(9.into(), 10.into()));
    let points: Vec<DyadicPoint> = coefficients
        .iter()
        .map(|c| DyadicPoint::of(c, bits))
        .collect();
    let mut roots: Vec<DyadicPoint> = (0..n)
        .map(|i| DyadicPoint::of(&seed.pow(i as u32 + 1).scale(&bound), bits))
        .collect();
    let horner = |z: &DyadicPoint| -> DyadicPoint {
        points.iter().rev().fold(
            DyadicPoint {
                re: Dyadic::zero(),
                im: Dyadic::zero(),
            },
            |value, c| value.mul(z, bits).add(c, bits),
        )
    };
    let still = Dyadic::of_rat(&(bound * dyadic(-i64::from(bits / 2))), bits).0;
    let still_sq = still.mul(&still);
    let nudge = DyadicPoint {
        re: still.clone(),
        im: still.clone(),
    };
    for _ in 0..iterations {
        let mut settled = true;
        for i in 0..n {
            let mut product = DyadicPoint {
                re: Dyadic::power(0),
                im: Dyadic::zero(),
            };
            for j in 0..n {
                if j != i {
                    product = product.mul(&roots[i].sub(&roots[j], bits), bits);
                }
            }
            let Some(step) = horner(&roots[i]).div(&product, bits) else {
                // Two points met: move this one off by the stopping grain.
                roots[i] = roots[i].add(&nudge, bits);
                settled = false;
                continue;
            };
            if step.norm_sq().to_rat() > still_sq.to_rat() {
                settled = false;
            }
            roots[i] = roots[i].sub(&step, bits);
        }
        if settled {
            break;
        }
    }
    roots.iter().map(DyadicPoint::gaussian).collect()
}

/// **A root isolated about an attained point**: Newton's steps on the disks' centers from `seed`,
/// then the first radius of the ladder `2^k r₀` (from the last step's size, or the center's
/// grain) whose disk passes [`krawczyk`]; a `real` seed is held on the real axis, so its disk is
/// symmetric under conjugation and the unique root it holds is real. `None` when no radius of
/// the ladder passes.
pub fn isolate(coefficients: &[Disk], seed: &GaussianRat, real: bool, bits: u32) -> Option<Disk> {
    let slopes = derivative(coefficients, bits);
    let mut center = if real {
        GaussianRat::real(seed.re.clone())
    } else {
        seed.clone()
    };
    let mut step_sq = Rat::zero();
    for _ in 0..8 {
        let at = Disk::point(center.clone());
        let value = evaluate(coefficients, &at, bits).center;
        let slope = evaluate(&slopes, &at, bits).center;
        let Ok(step) = value.div(&slope) else {
            break;
        };
        let step = if real {
            GaussianRat::real(step.re)
        } else {
            step
        };
        step_sq = step.norm_sq();
        center = Disk::point(center.sub(&step)).held(bits).center;
        if step_sq.is_zero() {
            break;
        }
    }
    let magnitude = root_upper(&center.norm_sq()).max(dyadic(-i64::from(bits)));
    let floor = magnitude * dyadic(-i64::from(bits) / 2);
    let mut radius = (Rat::from_integer(BigInt::from(4)) * root_upper(&step_sq)).max(floor);
    for _ in 0..(bits / 2 + 8) {
        if krawczyk(coefficients, &center, &radius, bits) {
            return Some(Disk::new(center, radius));
        }
        radius *= Rat::from_integer(BigInt::from(2));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn poly(roots: &[GaussianRat]) -> Vec<GaussianRat> {
        // ∏ (z − r_i), ascending.
        let mut coefficients = vec![GaussianRat::one()];
        for root in roots {
            let mut next = vec![GaussianRat::zero(); coefficients.len() + 1];
            for (k, c) in coefficients.iter().enumerate() {
                next[k + 1] = next[k + 1].add(c);
                next[k] = next[k].sub(&c.mul(root));
            }
            coefficients = next;
        }
        coefficients
    }

    fn disks(coefficients: &[GaussianRat]) -> Vec<Disk> {
        coefficients.iter().cloned().map(Disk::point).collect()
    }

    #[test]
    fn the_disk_arithmetic_holds_every_product_and_inverse() {
        let a = Disk::new(GaussianRat::new(rat(3, 2), rat(-1, 3)), rat(1, 100));
        let b = Disk::new(GaussianRat::new(rat(-2, 7), rat(5, 4)), rat(1, 50));
        let product = a.mul(&b, 64);
        // Every corner of the operands' disks lands in the product's disk.
        for (da, db) in [(rat(1, 100), rat(1, 50)), (rat(-1, 100), rat(1, 50)), (rat(1, 100), rat(-1, 50))] {
            let x = a.center.add(&GaussianRat::new(da.clone(), Rat::zero()));
            let y = b.center.add(&GaussianRat::new(Rat::zero(), db.clone()));
            assert!(product.holds_inside(&Disk::point(x.mul(&y))) || product.radius > Rat::zero());
            let distance = product.center.sub(&x.mul(&y)).norm_sq();
            assert!(distance <= &product.radius * &product.radius);
        }
        let inverse = b.inverse(64).expect("zero outside");
        let back = inverse.mul(&b, 64);
        let distance = back.center.sub(&GaussianRat::one()).norm_sq();
        assert!(distance <= &back.radius * &back.radius);
        assert!(Disk::new(GaussianRat::one(), integer(2)).inverse(64).is_none());
    }

    #[test]
    fn dyadic_disks_hold_every_product_and_sum() {
        let a = GaussianRat::new(rat(3, 7), rat(-5, 11));
        let b = GaussianRat::new(rat(-13, 17), rat(2, 3));
        let x = rat(22, 7);
        let (da, db) = (
            DyadicDisk::of(&Disk::point(a.clone()), 64),
            DyadicDisk::of(&Disk::point(b.clone()), 64),
        );
        let checks = [
            (da.mul(&db, 64), a.mul(&b)),
            (da.add(&db, 64), a.add(&b)),
            (da.scale(&x, 64), a.scale(&x)),
            (da.mul(&db, 64).mul(&da, 64).add(&db, 64), a.mul(&b).mul(&a).add(&b)),
        ];
        for (disk, exact) in checks {
            let disk = disk.disk();
            let distance = disk.center.sub(&exact).norm_sq();
            assert!(distance <= &disk.radius * &disk.radius, "{disk:?} {exact:?}");
            assert!(disk.radius < rat(1, 1 << 50), "{disk:?}");
        }
    }

    #[test]
    fn root_bounds_bracket_the_square_root() {
        for x in [rat(2, 1), rat(1, 3), rat(10_000_019, 7), rat(1, 1 << 40)] {
            let (lower, upper) = (root_lower(&x), root_upper(&x));
            assert!(&lower * &lower <= x && x <= &upper * &upper);
            assert!(&upper - &lower <= &upper * dyadic(-38));
        }
    }

    #[test]
    fn krawczyk_isolates_simple_roots_real_and_paired() {
        // (z − 3/2)(z − (1/2 + 3i/4))(z − (1/2 − 3i/4))(z + 1/5): real coefficients.
        let roots = [
            GaussianRat::real(rat(3, 2)),
            GaussianRat::new(rat(1, 2), rat(3, 4)),
            GaussianRat::new(rat(1, 2), rat(-3, 4)),
            GaussianRat::real(rat(-1, 5)),
        ];
        let coefficients = poly(&roots);
        let attained = attained_roots(&coefficients, 128, 200);
        assert_eq!(attained.len(), 4);
        let exact = disks(&coefficients);
        for root in &roots {
            let seed = attained
                .iter()
                .min_by(|a, b| a.sub(root).norm_sq().cmp(&b.sub(root).norm_sq()))
                .expect("a seed");
            let disk = isolate(&exact, seed, root.is_real(), 128).expect("isolated");
            assert!(disk.center.sub(root).norm_sq() <= &disk.radius * &disk.radius);
            assert!(disk.radius < rat(1, 1 << 20));
        }
        // A disk holding two roots fails the test.
        assert!(!krawczyk(&exact, &GaussianRat::new(rat(1, 2), Rat::zero()), &integer(1), 128));
    }

    #[test]
    fn a_double_root_is_never_certified() {
        let coefficients = poly(&[
            GaussianRat::real(rat(1, 2)),
            GaussianRat::real(rat(1, 2)),
            GaussianRat::real(integer(2)),
        ]);
        let exact = disks(&coefficients);
        for k in 1..40 {
            assert!(!krawczyk(&exact, &GaussianRat::real(rat(1, 2)), &dyadic(-k), 128));
        }
    }
}
