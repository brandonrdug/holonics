//! Supported realizer populations on an elliptic quartic, exactly, with a float-free independence
//! certificate.
//!
//! The standing demand this owner serves is the fourth slot of §11 — *an exactly computed positive
//! form on a supported realizer population, with a certified remainder and a reopening rule keyed
//! to the receiver family*. On an elliptic curve the realizers are rational points, the form is the
//! Néron–Tate height pairing, and its rank is the Mordell–Weil rank. **The positive form is not
//! computed here and is not needed here**: it is transcendental at the archimedean place, so every
//! implementation of it is a float, and a float may not decide independence. Independence is
//! decided instead by *reduction at declared prime receivers*, which is exact, finite, and returns
//! its own aperture.
//!
//! ## The construction
//!
//! Mestre's completed square. For a monic `p` of degree `2k` there is a unique monic `g` of degree
//! `k` with `deg(g^2 - p) < k`; write `r = g^2 - p`. At every root `a` of `p`, `r(a) = g(a)^2` is a
//! square, so `y^2 = r(x)` carries `2k` rational points by construction. When `deg r = 4` the
//! curve is elliptic and the points are supported realizers of its Mordell–Weil lattice.
//!
//! Taking the `2k` roots as `{a_i ± T}` for six values `a_i` and a parameter `T`, `deg r ≤ 5`
//! always, and `deg r = 4` — the elliptic case — exactly when
//!
//! ```text
//!     e_1 = 0     and     2 e_5 = e_2 e_3
//! ```
//!
//! on the six values. That pair of symmetric identities is the whole of what the literature
//! carries as "Mestre `(u, v)` families": those parametrisations are one rational surface inside
//! the solution variety, which is three-dimensional projectively. [`RealizerSextuple::found`]
//! refuses anything off the variety and says which identity failed, so the condition is a typed
//! boundary rather than a convention.
//!
//! Measured 2026-08-26 against the ICARM rank leaderboard: the sextuples published for curves
//! #159 (rank 17), #161 (rank 18), #275 and #280 (rank 19) all satisfy both identities exactly,
//! and rebuilding each family here reproduces the published curve's `j`-invariant and its minimal
//! naive height to every digit.
//!
//! ## What the construction cannot do, measured rather than assumed
//!
//! The forced realizers satisfy exactly one relation, `div(y - g(x)) = Σ P_i - k∞₊ - k∞₋`, so `2k`
//! roots give rank `2k - 1` and `k = 6` gives Mestre's eleven. Pushing `k` higher needs
//! `r_5 = … = r_{k-1} = 0`, which is `k - 5` conditions; a naive count calls the solution variety
//! five-dimensional for every `k`, but that count is about `ℂ`-points and says nothing arithmetic —
//! over `ℂ` each fibre is a torus and `2k` points summing to `kκ` costs nothing. The one cheap
//! rational solution at higher `k`, negation symmetry, makes `r` even in `x` and so forces the
//! involution `ι(P) = c - P`, which pairs the realizers and **halves** the rank. `k = 6` is
//! therefore the ceiling of this construction, and rank beyond eleven comes from realizers that
//! are not forced — which is what [`crate::cuda_realizer_search`] goes looking for.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Why a proposed sextuple is not a realizer family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SextupleRefusal {
    /// `e_1 ≠ 0`: the paired remainder then has degree five and the model is not elliptic.
    TraceNotZero { trace: BigRational },
    /// `2 e_5 ≠ e_2 e_3`: the degree-five coefficient of the remainder does not vanish.
    RemainderObstruction { residual: BigRational },
    /// Two values coincide, so the paired root population is not `2k` distinct roots.
    RepeatedValue { value: BigRational },
}

/// Six values on the variety `e_1 = 0`, `2 e_5 = e_2 e_3`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealizerSextuple {
    pub(super) values: [BigRational; 6],
}

/// The elementary symmetric functions `e_0 … e_n` of a value population.
pub fn elementary_symmetric(values: &[BigRational]) -> Vec<BigRational> {
    let mut e = vec![BigRational::zero(); values.len() + 1];
    e[0] = BigRational::one();
    for (index, value) in values.iter().enumerate() {
        for j in (1..=index + 1).rev() {
            let carried = e[j - 1].clone() * value;
            e[j] += carried;
        }
    }
    e
}

impl RealizerSextuple {
    /// Admit six values, or refuse with the identity that failed.
    pub fn found(values: [BigRational; 6]) -> Result<Self, SextupleRefusal> {
        for i in 0..6 {
            for j in i + 1..6 {
                if values[i] == values[j] {
                    return Err(SextupleRefusal::RepeatedValue {
                        value: values[i].clone(),
                    });
                }
            }
        }
        let e = elementary_symmetric(&values);
        if !e[1].is_zero() {
            return Err(SextupleRefusal::TraceNotZero {
                trace: e[1].clone(),
            });
        }
        let residual = &e[5] * BigRational::from_integer(BigInt::from(2)) - &e[2] * &e[3];
        if !residual.is_zero() {
            return Err(SextupleRefusal::RemainderObstruction { residual });
        }
        Ok(Self { values })
    }

    /// Translate an arbitrary six values to trace zero, then admit. Translation moves `x` and
    /// leaves the curve, so this is a rebase with zero remainder rather than a repair.
    pub fn found_after_centring(values: [BigRational; 6]) -> Result<Self, SextupleRefusal> {
        let six = BigRational::from_integer(BigInt::from(6));
        let mean = values.iter().fold(BigRational::zero(), |a, b| a + b) / six;
        let centred: Vec<BigRational> = values.iter().map(|v| v - &mean).collect();
        Self::found([
            centred[0].clone(),
            centred[1].clone(),
            centred[2].clone(),
            centred[3].clone(),
            centred[4].clone(),
            centred[5].clone(),
        ])
    }

    pub fn values(&self) -> &[BigRational; 6] {
        &self.values
    }
}

// ---------------------------------------------------------------------------------------------
// polynomials over the rationals, ascending coefficients
// ---------------------------------------------------------------------------------------------

pub(super) fn poly_mul(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, y) in b.iter().enumerate() {
            let term = x * y;
            out[i + j] += term;
        }
    }
    out
}

/// The unique monic `g` of degree `half` with `deg(g^2 - p) < half`, for monic `p` of degree
/// `2·half`. Matching coefficients downward is a triangular solve and needs no division beyond the
/// leading `2`.
pub(super) fn monic_square_root_remainder(p: &[BigRational], half: usize) -> Vec<BigRational> {
    let two = BigRational::from_integer(BigInt::from(2));
    let mut g = vec![BigRational::zero(); half + 1];
    g[half] = BigRational::one();
    for m in 1..=half {
        let index = 2 * half - m;
        let mut sum = BigRational::zero();
        for i in (half - m + 1)..=half {
            let j = index.checked_sub(i);
            if let Some(j) = j {
                if j <= half {
                    let term = &g[i] * &g[j];
                    sum += term;
                }
            }
        }
        g[half - m] = (&p[index] - sum) / &two;
    }
    g
}

pub(super) fn poly_eval(p: &[BigRational], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * x + c;
    }
    acc
}

/// The elliptic quartic a family returns at one specialization, with its forced realizers.
#[derive(Debug, Clone)]
pub struct RemainderQuartic {
    /// `r_0 … r_4`, ascending.
    pub coefficient: [BigRational; 5],
    /// The `2k` points `(a_i ± T, g(a_i ± T))` on `y^2 = r(x)`.
    pub forced_realizers: Vec<(BigRational, BigRational)>,
}

impl RealizerSextuple {
    /// The completed-square remainder at one specialization of the pairing parameter.
    pub fn remainder_at(&self, parameter: &BigRational) -> RemainderQuartic {
        let mut product = vec![BigRational::one()];
        for a in self.values.iter() {
            // (x - a)^2 - T^2  as ascending coefficients
            let quadratic = vec![a * a - parameter * parameter, -(a + a), BigRational::one()];
            product = poly_mul(&product, &quadratic);
        }
        let g = monic_square_root_remainder(&product, 6);
        let square = poly_mul(&g, &g);
        let mut remainder = vec![BigRational::zero(); square.len().max(product.len())];
        for (i, c) in square.iter().enumerate() {
            remainder[i] += c;
        }
        for (i, c) in product.iter().enumerate() {
            remainder[i] -= c;
        }
        let mut forced = Vec::with_capacity(12);
        for a in self.values.iter() {
            for signed in [a + parameter, a - parameter] {
                let value = poly_eval(&g, &signed);
                forced.push((signed, value));
            }
        }
        let coefficient = [
            remainder[0].clone(),
            remainder[1].clone(),
            remainder[2].clone(),
            remainder[3].clone(),
            remainder[4].clone(),
        ];
        debug_assert!(remainder.iter().skip(5).all(|c| c.is_zero()));
        RemainderQuartic {
            coefficient,
            forced_realizers: forced,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the integral model
// ---------------------------------------------------------------------------------------------

pub(super) fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.abs();
    let mut b = b.abs();
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a
}

pub(super) fn lcm(a: &BigInt, b: &BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::zero();
    }
    (a * b).abs() / gcd(a, b)
}

/// A quartic with integer coefficients, ascending, with every square factor of the content divided
/// out. Removing a square from the content rescales `y` and leaves the curve; it is the one
/// reduction that costs nothing and it is what makes the search window meaningful.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegralQuartic {
    pub coefficient: [BigInt; 5],
    /// `y_integral = scale · y_rational`, retained so a found realizer maps back exactly.
    pub scale: BigRational,
}

impl RemainderQuartic {
    pub fn integral(&self, small_primes: &[u64]) -> IntegralQuartic {
        let mut denominator = BigInt::one();
        for c in self.coefficient.iter() {
            denominator = lcm(&denominator, c.denom());
        }
        let square = &denominator * &denominator;
        let mut integral: Vec<BigInt> = self
            .coefficient
            .iter()
            .map(|c| (c * BigRational::from_integer(square.clone())).to_integer())
            .collect();
        let mut content = BigInt::zero();
        for c in integral.iter() {
            content = gcd(&content, c);
        }
        let mut removed = BigInt::one();
        if content > BigInt::one() {
            let mut residual = content.clone();
            for &p in small_primes {
                let prime = BigInt::from(p);
                if &prime * &prime > residual {
                    break;
                }
                let mut exponent = 0u32;
                while (&residual % &prime).is_zero() {
                    residual /= &prime;
                    exponent += 1;
                }
                for _ in 0..exponent / 2 {
                    removed *= &prime;
                }
            }
            if removed > BigInt::one() {
                let square_removed = &removed * &removed;
                for c in integral.iter_mut() {
                    *c /= &square_removed;
                }
            }
        }
        IntegralQuartic {
            coefficient: [
                integral[0].clone(),
                integral[1].clone(),
                integral[2].clone(),
                integral[3].clone(),
                integral[4].clone(),
            ],
            scale: BigRational::new(denominator, removed),
        }
    }
}

impl IntegralQuartic {
    /// The classical invariants of a binary quartic. The Jacobian of `y^2 = q(x)` is
    /// `Y^2 = X^3 - 27 I X - 27 J`, so `c4 = 1296 I` and `c6 = 23328 J`.
    pub fn invariants(&self) -> (BigInt, BigInt) {
        let e = &self.coefficient[0];
        let d = &self.coefficient[1];
        let c = &self.coefficient[2];
        let b = &self.coefficient[3];
        let a = &self.coefficient[4];
        let i = BigInt::from(12) * a * e - BigInt::from(3) * b * d + c * c;
        let j = BigInt::from(72) * a * c * e + BigInt::from(9) * b * c * d
            - BigInt::from(27) * a * d * d
            - BigInt::from(27) * e * b * b
            - BigInt::from(2) * c * c * c;
        (BigInt::from(1296) * i, BigInt::from(23328) * j)
    }
}

/// A minimal Weierstrass model, carried by its invariants and the rescale that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinimalModel {
    pub c4: BigInt,
    pub c6: BigInt,
    pub discriminant: BigInt,
    /// The integer `u` with `c4_before = u^4 · c4`, `c6_before = u^6 · c6`. A winding, exhibited.
    pub rescale: BigInt,
    pub a_invariants: [BigInt; 5],
}

/// Kraus's criterion: `(c4, c6)` come from an integral model exactly when `v_3(c6) ≠ 2` and, at
/// two, either `c6 ≡ 3 (mod 4)` or `16 | c4` with `c6 ≡ 0` or `8 (mod 32)`.
fn kraus_admits(c4: &BigInt, c6: &BigInt) -> bool {
    let nine = BigInt::from(9);
    let twenty_seven = BigInt::from(27);
    if (c6 % &nine).is_zero() && !(c6 % &twenty_seven).is_zero() {
        return false;
    }
    let four = BigInt::from(4);
    let mut residue = c6 % &four;
    if residue.is_negative() {
        residue += &four;
    }
    if residue == BigInt::from(3) {
        return true;
    }
    if !(c4 % BigInt::from(16)).is_zero() {
        return false;
    }
    let thirty_two = BigInt::from(32);
    let mut residue = c6 % &thirty_two;
    if residue.is_negative() {
        residue += &thirty_two;
    }
    residue.is_zero() || residue == BigInt::from(8)
}

/// Divide out every admissible `u`. The prime family is the aperture and is the caller's.
pub fn minimalise(c4: &BigInt, c6: &BigInt, small_primes: &[u64]) -> MinimalModel {
    let mut c4 = c4.clone();
    let mut c6 = c6.clone();
    let mut rescale = BigInt::one();
    let mut discriminant = (&c4 * &c4 * &c4 - &c6 * &c6) / BigInt::from(1728);
    for &p in small_primes {
        let prime = BigInt::from(p);
        let p4 = prime.pow(4);
        let p6 = prime.pow(6);
        let p12 = prime.pow(12);
        loop {
            if !(&c4 % &p4).is_zero() || !(&c6 % &p6).is_zero() || !(&discriminant % &p12).is_zero()
            {
                break;
            }
            let next4 = &c4 / &p4;
            let next6 = &c6 / &p6;
            if !kraus_admits(&next4, &next6) {
                break;
            }
            c4 = next4;
            c6 = next6;
            discriminant /= &p12;
            rescale *= &prime;
        }
    }
    let a_invariants = a_invariants_from(&c4, &c6);
    MinimalModel {
        c4,
        c6,
        discriminant,
        rescale,
        a_invariants,
    }
}

/// The classical recovery of `[a1, a2, a3, a4, a6]` from admissible `(c4, c6)`.
fn a_invariants_from(c4: &BigInt, c6: &BigInt) -> [BigInt; 5] {
    // Kraus forces `-c6 mod 12` into `{0, 1, 4, 5, 8, 9}`, and the *reduced* model — the one with
    // `a1, a3 ∈ {0, 1}` and `a2 ∈ {-1, 0, 1}` — needs `b2 ∈ {-4, -3, 0, 1, 4, 5}`. Taking the
    // representative in `[0, 12)` instead returns a translate: still minimal, still the same curve,
    // and not the model anyone publishes. Measured against leaderboard curve #159, that choice put
    // `a4` off by exactly one.
    let twelve = BigInt::from(12);
    let mut b2 = (-c6) % &twelve;
    if b2.is_negative() {
        b2 += &twelve;
    }
    if b2 > BigInt::from(5) {
        b2 -= &twelve;
    }
    let b4 = (&b2 * &b2 - c4) / BigInt::from(24);
    let b6 = (-(&b2 * &b2 * &b2) + BigInt::from(36) * &b2 * &b4 - c6) / BigInt::from(216);
    let two = BigInt::from(2);
    let a1 = ((&b2 % &two) + &two) % &two;
    let a2 = (&b2 - &a1 * &a1) / BigInt::from(4);
    let a3 = ((&b6 % &two) + &two) % &two;
    let a4 = (&b4 - &a1 * &a3) / &two;
    let a6 = (&b6 - &a3 * &a3) / BigInt::from(4);
    [a1, a2, a3, a4, a6]
}

impl MinimalModel {
    /// `max(|c4|^3, c6^2)`, the naive height **before** any logarithm. Records are compared on this
    /// integer: the leaderboard's `log` is a receiver face and taking it loses exactness for
    /// nothing, since the ordering is the same.
    pub fn naive_height_key(&self) -> BigInt {
        let a = (&self.c4).abs().pow(3);
        let b = (&self.c6) * (&self.c6);
        if a > b { a } else { b }
    }
}

/// Primes up to a bound, the one sieve every receiver family here draws from.
pub fn primes_upto(bound: u64) -> Vec<u64> {
    if bound < 2 {
        return Vec::new();
    }
    let n = bound as usize;
    let mut sieve = vec![true; n + 1];
    sieve[0] = false;
    sieve[1] = false;
    let mut i = 2usize;
    while i * i <= n {
        if sieve[i] {
            let mut j = i * i;
            while j <= n {
                sieve[j] = false;
                j += i;
            }
        }
        i += 1;
    }
    (2..=n).filter(|&i| sieve[i]).map(|i| i as u64).collect()
}
