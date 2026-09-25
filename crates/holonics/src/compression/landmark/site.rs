//! **Site kinds: a navigator site is a rotation, a null lock, a boost, a reflection or
//! degenerate, read from its trace and determinant.**
//!
//! [definition] A navigator site is a two-state material `M` read through its two conserved faces,
//! the trace `a = tr M` and the determinant `q = det M` ([`SiteFactor`]; its factor is
//! `1 − aT + qT²`). Phase carriage conserves both, so the kind is a class function
//! (Lean `Compression/Landmark/SiteKind.carried_site_kind`):
//!
//! ```text
//! q < 0                reflection   orientation-reversing: two real roots of opposite sign (the Swing)
//! q = 0                degenerate   a singular site: one root is zero
//! q > 0, a² < 4q       rotation     the form x² − axy + qy² is definite; no real root of 1 − aT + qT²
//! q > 0, a² = 4q       null         the traceless part is nilpotent; for a companion site, a shear
//! q > 0, a² > 4q       boost        two real roots of one sign
//! (M − (a/2)·1)² = (a² − 4q)/4 · 1                                   the traceless square
//! γ² = a²/(4q),  (γβ)² = γ² − 1 = (a² − 4q)/(4q)                     projective Lorentz faces
//! ```
//!
//! [proved-derived; implemented-exact] **The kinds are read from the eigenvalues.** The
//! characteristic polynomial is `λ² − aλ + q` (Lean `det_sub_eq`): a rotation has no real
//! eigenvalue, a boost two distinct real eigenvalues of one sign, a reflection two of opposite
//! signs, and a degenerate site the eigenvalue `0` (Lean `rotation_iff_no_real_eigenvalue`,
//! `boost_iff_two_real_eigenvalues`, `reflection_iff_opposite_eigenvalues`,
//! `degenerate_iff_zero_eigenvalue`); for `q > 0` exactly one of rotation, null and boost holds
//! (`site_trichotomy`). The Swing `[[0, 1], [1, 0]]` is a reflection (`swing_is_reflection`).
//!
//! [proved-derived; implemented-exact] **`γ = tr/2` holds only at `q = 1`.** The Lorentz factor of
//! a site is read projectively, `γ² = tr²/(4 det)`, which is invariant under scaling the material
//! (Lean `lorentz_factor_sq_smul`; `FixedPoint.velocity_is_boost`); `tr/2` would give `γ = 1` for
//! every velocity-addition navigator `[[1, v], [v, 1]]`. `γ` itself is rational exactly when `γ²`
//! is a rational square. Only a null site (`γ² = 1`) or a boost (`γ² > 1`) has a Lorentz face: a
//! rotation's `tr²/(4 det)` is `cos²θ < 1`, and a reflection or degenerate site has no positive
//! determinant, so [`lorentz_factor_squared`] refuses all three.
//!
//! [proved-derived; implemented-exact] **The boost's counts and its Doppler ratio.** The closed-word
//! counts `t_n = tr Mⁿ` obey the integer recurrence `t_{n+2} = a t_{n+1} − q t_n`
//! ([`SiteFactor::trace_sequence`]; Lean `trace_pow_eq`). At `q = 1` a boost's **Doppler ratio**
//! `k` is the root of `k² − ak + 1 = 0` with `|k| > 1`, carried as its constraint in
//! `ℚ(√(a² − 4))` ([`DopplerRatio`]), never as a real: `t_n = kⁿ + k⁻ⁿ = 2·Re(kⁿ)`, and for
//! `a ≥ 2` the exact sandwich `kⁿ ≤ t_n ≤ 2kⁿ` holds (Lean `boost_counts_are_doppler_powers`,
//! `boost_counts_sandwich`), so the growth rate is exactly the rapidity, `(1/n) log t_n → log k`
//! (`boost_count_rate`). This owner carries the sandwich and evaluates no logarithm. The counts
//! have two readings: `t_n` closed walks of a nonnegative adjacency (the graph or shift, whose
//! entropy is `log k`), and `|det(Mⁿ − 1)|` period-`n` points of a torus automorphism
//! ([`torus_fixed_points`]), with the same rate (`torus_count_rate`).
//!
//! [definition; agent-inferred] **Where this owner is sharper than the Lean.** Lean states
//! `det(Mⁿ − 1) = 2 − t_n` at `q = 1` (`det_pow_sub_one`); [`torus_fixed_points`] uses
//! `det(Mⁿ − 1) = qⁿ − t_n + 1` for every integer site, from `det(N − 1) = det N − tr N + 1`, and
//! its test counts the torus points by brute force. [proved-standard] An integer site is the pair
//! of faces of an integer material, an endomorphism of the torus `ℝ²/ℤ²` (an automorphism at
//! `q = ±1`), and the points `x` with
//! `Mⁿx = x` are the kernel of `Mⁿ − 1` on the torus, of order `|det(Mⁿ − 1)|` when that is nonzero
//! (the index of `(Mⁿ − 1)ℤ²` in `ℤ²`). When it is zero the fixed points are not isolated: the
//! quarter-turn `(0, 1)` has `M⁴ = 1`, so every point has period dividing four, and the count is
//! returned as `None`, not `0`. A non-integer site has no torus reading and a zero period counts
//! nothing; both are refused. That this absolute value counts the period-`n` points (the Lefschetz
//! reading) is owed in #62 ("the Lefschetz count of torus periodic points").
//!
//! | Lean `Compression/Landmark/SiteKind` | Rust |
//! |---|---|
//! | `discriminant`, `traceless_sq` | [`SiteFactor::discriminant`], [`traceless_square`] |
//! | `Kind`, `siteKind`, `siteKind_of_{neg,zero,pos}`, `siteKind_eq_{reflection,degenerate,rotation,null,boost}_iff`, `swing_is_reflection` | [`SiteFactor::kind`], [`SiteKind`] (owned by `navigator::trace`) |
//! | `det_sub_eq`, `rotation_iff_no_real_eigenvalue`, `boost_iff_two_real_eigenvalues`, `reflection_iff_opposite_eigenvalues`, `degenerate_iff_zero_eigenvalue`, `site_trichotomy` | tests |
//! | `rotation_iff_no_real_root` (`q > 0`), `rotation_iff_definite`, `null_iff_traceless_nilpotent`, `companion_traceless_ne_zero`, `identity_and_shear_are_both_null` | tests |
//! | `carried_site_kind`, `companion_siteKind`, `siteKind_neg`, `hasse_site_is_rotation` | tests |
//! | `lorentz_factor_sq_smul`, `boost_doppler_ratio` (`q = 1`), `rational_doppler_three`, `catMap_boost` | [`lorentz_factor_squared`], [`DopplerRatio`] |
//! | `trace_neg`, `boost_counts_grow`, `bounded_iff_not_boost`, `boost_counts_are_doppler_powers`, `boost_counts_sandwich`, `boost_count_rate` | [`DopplerRatio::power`], tests |
//! | `trace_pow_eq`, `det_pow_sub_one` (`q = 1`), `torus_count_rate` | [`torus_fixed_points`] |

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};

use crate::compression::landmark::LandmarkError;
use crate::compression::landmark::quadratic::QuadraticSurd;
use crate::navigator::trace::{SiteFactor, SiteKind};
use crate::ratio::polynomial::RationalPolynomial;
use crate::ratio::{Rat, integer};

/// A two-state material, row-major.
pub type Material2 = [[Rat; 2]; 2];

/// The two faces `(tr M, det M)` of a two-state material.
pub fn material_site(material: &Material2) -> SiteFactor {
    SiteFactor::new(
        &material[0][0] + &material[1][1],
        &material[0][0] * &material[1][1] - &material[0][1] * &material[1][0],
    )
}

/// The product of two two-state materials.
pub fn multiply(left: &Material2, right: &Material2) -> Material2 {
    let entry = |row: usize, column: usize| {
        &left[row][0] * &right[0][column] + &left[row][1] * &right[1][column]
    };
    [[entry(0, 0), entry(0, 1)], [entry(1, 0), entry(1, 1)]]
}

/// The traceless part `M − (tr M/2)·1`.
pub fn traceless_part(material: &Material2) -> Material2 {
    let half = (&material[0][0] + &material[1][1]) / integer(2);
    [
        [&material[0][0] - &half, material[0][1].clone()],
        [material[1][0].clone(), &material[1][1] - &half],
    ]
}

/// **The traceless square** `(M − (tr M/2)·1)²`, which is `(a² − 4q)/4 · 1` (Lean `traceless_sq`).
pub fn traceless_square(material: &Material2) -> Material2 {
    let traceless = traceless_part(material);
    multiply(&traceless, &traceless)
}

/// **The projective Lorentz factor** `γ² = a²/(4q)`, invariant under scaling the material (Lean
/// `lorentz_factor_sq_smul`). Refused unless the site is null (`γ² = 1`) or a boost (`γ² > 1`): a
/// rotation's `a²/(4q)` is `cos²θ < 1`, and a reflection or degenerate site has none.
pub fn lorentz_factor_squared(site: &SiteFactor) -> Result<Rat, LandmarkError> {
    let kind = site.kind();
    if !matches!(kind, SiteKind::Null | SiteKind::Boost) {
        return Err(LandmarkError::NoLorentzFace { kind });
    }
    Ok(site.trace() * site.trace() / (integer(4) * site.determinant()))
}

/// **The number of period-`n` points of an integer site as a torus endomorphism**,
/// `|det(Mⁿ − 1)| = |qⁿ − t_n + 1|`; at `q = 1` it is `|t_n − 2|` (Lean `det_pow_sub_one`), not the
/// closed-walk count `t_n`. `None` when `det(Mⁿ − 1) = 0`, where the fixed points of `Mⁿ` are not
/// isolated (a rotation of order dividing `n` fixes every point). A non-integer site and a zero
/// period are refused.
pub fn torus_fixed_points(
    site: &SiteFactor,
    period: usize,
) -> Result<Option<BigUint>, LandmarkError> {
    if !site.trace().is_integer() || !site.determinant().is_integer() {
        return Err(LandmarkError::NotAnIntegerSite {
            trace: site.trace().clone(),
            determinant: site.determinant().clone(),
        });
    }
    if period == 0 {
        return Err(LandmarkError::ZeroPeriod);
    }
    let counts = site.trace_sequence(period);
    let power = (0..period).fold(Rat::one(), |power, _| power * site.determinant());
    let determinant = power - &counts[period] + Rat::one();
    Ok((!determinant.is_zero()).then(|| determinant.numer().magnitude().clone()))
}

/// [definition] **The Doppler ratio of a unit boost**: the root `k` of `k² − ak + 1 = 0` with
/// `|k| > 1`, carried in `ℚ(√(a² − 4))`. Only a boost of determinant one has one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DopplerRatio {
    site: SiteFactor,
    ratio: QuadraticSurd,
}

impl DopplerRatio {
    /// The Doppler ratio of a site; refused unless `q = 1` and `a² > 4`.
    pub fn of_site(site: &SiteFactor) -> Result<Self, LandmarkError> {
        if !site.determinant().is_one() || site.kind() != SiteKind::Boost {
            return Err(LandmarkError::NotAUnitBoost {
                trace: site.trace().clone(),
                determinant: site.determinant().clone(),
            });
        }
        let half = site.trace() / integer(2);
        let branch = if site.trace().is_negative() {
            -(Rat::one() / integer(2))
        } else {
            Rat::one() / integer(2)
        };
        let ratio = QuadraticSurd::new(half, branch, site.discriminant())?;
        Ok(Self {
            site: site.clone(),
            ratio,
        })
    }

    /// The site.
    pub fn site(&self) -> &SiteFactor {
        &self.site
    }

    /// `k`, in its quadratic field.
    pub fn ratio(&self) -> &QuadraticSurd {
        &self.ratio
    }

    /// **The constraint** `X² − aX + 1`, whose root `k` is.
    pub fn constraint(&self) -> RationalPolynomial {
        RationalPolynomial::new(vec![Rat::one(), -self.site.trace().clone(), Rat::one()])
    }

    /// `kⁿ` in the field.
    pub fn power(&self, exponent: u32) -> Result<QuadraticSurd, LandmarkError> {
        self.ratio.power(exponent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::polynomial::distinct_real_root_count;
    use crate::ratio::primality::is_prime;
    use crate::ratio::rat;
    use num_traits::Zero;
    use std::cmp::Ordering;

    fn site(a: i64, q: i64) -> SiteFactor {
        SiteFactor::new(integer(a), integer(q))
    }

    fn material(entries: [[i64; 2]; 2]) -> Material2 {
        entries.map(|row| row.map(integer))
    }

    fn scalar(value: Rat) -> Material2 {
        [[value.clone(), Rat::zero()], [Rat::zero(), value]]
    }

    /// Lean `traceless_sq`: the traceless part squares to a quarter of the discriminant, for
    /// materials of every kind, including reflections and singular ones.
    #[test]
    fn the_traceless_part_squares_to_the_discriminant() {
        for entries in [
            [[2, 1], [1, 1]],
            [[0, 1], [1, 0]],
            [[1, 1], [0, 1]],
            [[3, -2], [5, 7]],
            [[1, 0], [0, 0]],
            [[0, -1], [1, 0]],
        ] {
            let material = material(entries);
            assert_eq!(
                traceless_square(&material),
                scalar(material_site(&material).discriminant() / integer(4))
            );
        }
    }

    /// Lean `siteKind_eq_reflection_iff`, `siteKind_eq_degenerate_iff`, `swing_is_reflection`: **a
    /// negative determinant is a reflection and a zero one is degenerate**, never a boost or a null
    /// lock. The Swing `[[0, 1], [1, 0]]` (`z ↦ 1/z`) has `a² − 4q = 4 > 0`
    /// yet is a reflection; `(a, q) = (0, 0)` has `a² = 4q` yet is degenerate.
    #[test]
    fn the_swing_is_a_reflection_not_a_boost() {
        let swing = material_site(&material([[0, 1], [1, 0]]));
        assert!(swing.discriminant().is_positive());
        assert_eq!(swing.kind(), SiteKind::Reflection);
        assert_eq!(site(0, 0).kind(), SiteKind::Degenerate);
        assert_eq!(site(3, 0).kind(), SiteKind::Degenerate);
        assert_eq!(site(1, -6).kind(), SiteKind::Reflection);
        assert!(lorentz_factor_squared(&swing).is_err());
    }

    /// Lean `siteKind_eq_{rotation,null,boost}_iff` at `q > 0` and `rotation_iff_no_real_root`: a
    /// positive-determinant site is a rotation exactly when its factor `1 − aT + qT²` has no real
    /// root, counted by Sturm.
    #[test]
    fn a_rotation_has_no_real_root() {
        for a in -7i64..=7 {
            for q in 1i64..=9 {
                let factor = RationalPolynomial::new(vec![integer(1), integer(-a), integer(q)]);
                let roots = distinct_real_root_count(&factor).unwrap();
                let kind = site(a, q).kind();
                assert_eq!(kind == SiteKind::Rotation, roots == 0);
                assert_eq!(kind == SiteKind::Null, roots == 1);
                assert_eq!(kind == SiteKind::Boost, roots == 2);
            }
        }
    }

    /// Lean `det_sub_eq`, `rotation_iff_no_real_eigenvalue`, `boost_iff_two_real_eigenvalues`,
    /// `reflection_iff_opposite_eigenvalues`, `degenerate_iff_zero_eigenvalue`, `site_trichotomy`:
    /// **every kind is read from the eigenvalues**, the roots of `λ² − aλ + q`, for determinants of
    /// every sign. The positive roots are counted by Sturm as the nonzero real roots of `p(μ²)`, in
    /// pairs `±μ`, and the negative ones through `p(−μ²)`; nothing is approximated.
    #[test]
    fn every_kind_is_read_from_the_eigenvalues() {
        let square = RationalPolynomial::new(vec![integer(0), integer(0), integer(1)]);
        for a in -7i64..=7 {
            for q in -9i64..=9 {
                let characteristic =
                    RationalPolynomial::new(vec![integer(q), integer(-a), integer(1)]);
                let zero = u32::from(q == 0);
                let real = distinct_real_root_count(&characteristic).unwrap();
                let signed = |inner: &RationalPolynomial| {
                    (distinct_real_root_count(&characteristic.composed_with(inner)).unwrap() - zero)
                        / 2
                };
                let positive = signed(&square);
                let negative = signed(&square.negated());
                assert_eq!(positive + negative + zero, real);
                let kind = site(a, q).kind();
                assert_eq!(kind == SiteKind::Rotation, real == 0);
                assert_eq!(kind == SiteKind::Boost, positive == 2 || negative == 2);
                assert_eq!(kind == SiteKind::Reflection, positive == 1 && negative == 1);
                assert_eq!(kind == SiteKind::Degenerate, zero == 1);
                assert_eq!(kind == SiteKind::Null, real == 1 && zero == 0);
            }
        }
    }

    /// Lean `null_iff_traceless_nilpotent`, `companion_traceless_ne_zero`,
    /// `identity_and_shear_are_both_null`: a null site's traceless part is nilpotent; a null
    /// companion is a shear (nonzero traceless part), while the identity and the unipotent shear share
    /// their faces and are both null: the kind is a class function, not an action certificate.
    #[test]
    fn a_null_companion_is_a_shear() {
        for (a, q) in [(2, 1), (4, 4), (-6, 9)] {
            let site = site(a, q);
            assert_eq!(site.kind(), SiteKind::Null);
            let companion = site.companion();
            assert_eq!(traceless_square(&companion), scalar(Rat::zero()));
            assert_ne!(traceless_part(&companion), scalar(Rat::zero()));
        }
        let identity = material([[1, 0], [0, 1]]);
        let shear = material([[1, 1], [0, 1]]);
        assert_eq!(material_site(&identity), material_site(&shear));
        assert_eq!(material_site(&shear).kind(), SiteKind::Null);
        assert_eq!(traceless_part(&identity), scalar(Rat::zero()));
        assert_ne!(traceless_part(&shear), scalar(Rat::zero()));
    }

    /// Lean `carried_site_kind`, `companion_siteKind`: conjugation `S⁻¹PS` conserves the kind, and a
    /// companion has its factor's kind.
    #[test]
    fn phase_carriage_conserves_the_kind() {
        let carrier = [[integer(2), integer(1)], [integer(5), integer(3)]];
        let inverse = [[integer(3), integer(-1)], [integer(-5), integer(2)]];
        assert_eq!(multiply(&carrier, &inverse), scalar(Rat::one()));
        for (a, q) in [(1, 1), (2, 1), (3, 1), (0, -1), (5, 0), (-3, 2)] {
            let site = site(a, q);
            let carried = multiply(&multiply(&inverse, &site.companion()), &carrier);
            assert_eq!(material_site(&carried).kind(), site.kind());
            assert_eq!(material_site(&site.companion()).kind(), site.kind());
        }
    }

    /// Lean `hasse_site_is_rotation`: an integer trace at a prime determinant within the Hasse
    /// interval `a² ≤ 4p` is a rotation, never null.
    #[test]
    fn a_hasse_site_is_a_rotation() {
        for p in (2u64..60).filter(|p| is_prime(*p)) {
            let p = i64::try_from(p).unwrap();
            for a in (-2 * p)..=(2 * p) {
                if a * a <= 4 * p {
                    assert_eq!(site(a, p).kind(), SiteKind::Rotation);
                }
            }
        }
    }

    /// Lean `lorentz_factor_sq_smul`, `velocity_is_boost`: **`γ² = tr²/(4 det)`**, not `tr/2`. The
    /// velocity navigator `[[1, 3/5], [3/5, 1]]` has `tr/2 = 1` but `γ² = 25/16`, `γ = 5/4`; scaling
    /// the material leaves `γ²` unchanged; at `det = 1`, `γ = tr/2` (Lean `boost_doppler_ratio`).
    #[test]
    fn the_lorentz_factor_is_projective() {
        let velocity = [[integer(1), rat(3, 5)], [rat(3, 5), integer(1)]];
        let face = material_site(&velocity);
        assert_eq!(face.trace() / integer(2), integer(1));
        assert_eq!(lorentz_factor_squared(&face).unwrap(), rat(25, 16));
        let scaled = velocity
            .clone()
            .map(|row| row.map(|entry| entry * integer(7)));
        assert_eq!(
            lorentz_factor_squared(&material_site(&scaled)).unwrap(),
            rat(25, 16)
        );
        let unit = site(3, 1);
        assert_eq!(
            lorentz_factor_squared(&unit).unwrap(),
            (unit.trace() / integer(2)) * (unit.trace() / integer(2))
        );
    }

    /// Lean `rational_doppler_three`, `catMap_boost`: `companion(10/3, 1)` has the rational Doppler
    /// ratio `k = 3`, `γ = 5/3`, `β = 4/5`; the cat map `[[2, 1], [1, 1]]` has `γ = 3/2` and
    /// `(γβ)² = 5/4`, not a rational square, so its ratio `k = (3 + √5)/2` stays a constraint.
    #[test]
    fn a_doppler_ratio_is_rational_only_on_a_square() {
        let three = DopplerRatio::of_site(&SiteFactor::new(rat(10, 3), integer(1))).unwrap();
        assert_eq!(three.ratio().as_rational(), Some(&integer(3)));
        let gamma_squared = lorentz_factor_squared(three.site()).unwrap();
        assert_eq!(gamma_squared, rat(25, 9));
        let beta_squared = (&gamma_squared - Rat::one()) / &gamma_squared;
        assert_eq!(beta_squared, rat(16, 25));
        let cat = material_site(&material([[2, 1], [1, 1]]));
        let doppler = DopplerRatio::of_site(&cat).unwrap();
        assert_eq!(doppler.ratio().as_rational(), None);
        assert_eq!(
            lorentz_factor_squared(&cat).unwrap() - Rat::one(),
            rat(5, 4)
        );
        assert_eq!(
            crate::compression::landmark::quadratic::rational_square_root(&rat(5, 4)),
            None
        );
        let k = doppler.ratio();
        let constraint = k
            .mul(k)
            .unwrap()
            .sub(&k.scaled(cat.trace()))
            .unwrap()
            .shifted(&Rat::one());
        assert_eq!(constraint, QuadraticSurd::rational(Rat::zero()));
        assert!(DopplerRatio::of_site(&site(1, 1)).is_err());
        assert!(DopplerRatio::of_site(&site(5, 2)).is_err());
    }

    /// Lean `boost_counts_are_doppler_powers`, `boost_counts_sandwich`: the integer counts are
    /// `t_n = kⁿ + k⁻ⁿ`, twice the rational part of `kⁿ`, and `kⁿ ≤ t_n ≤ 2kⁿ` exactly; for a
    /// negative trace `t_n(−a) = (−1)ⁿ t_n(a)` (Lean `trace_neg`).
    #[test]
    fn a_boost_counts_at_its_doppler_rate() {
        for a in [3i64, 4, 7, -3, -5] {
            let site = site(a, 1);
            let doppler = DopplerRatio::of_site(&site).unwrap();
            let counts = site.trace_sequence(24);
            for (n, count) in counts.iter().enumerate() {
                let power = doppler.power(u32::try_from(n).unwrap()).unwrap();
                assert!(count.is_integer());
                assert_eq!(power.trace(), *count);
                assert_eq!(power.norm(), Rat::one());
                if a > 0 {
                    let count = QuadraticSurd::rational(count.clone());
                    assert_ne!(count.compare(&power).unwrap(), Ordering::Less);
                    assert_ne!(
                        count.compare(&power.scaled(&integer(2))).unwrap(),
                        Ordering::Greater
                    );
                }
            }
            let mirror = SiteFactor::new(integer(-a), integer(1)).trace_sequence(24);
            for (n, (left, right)) in counts.iter().zip(&mirror).enumerate() {
                let sign = if n % 2 == 0 { integer(1) } else { integer(-1) };
                assert_eq!(left, &(right * sign));
            }
        }
    }

    /// Lean `boost_counts_grow`, `bounded_iff_not_boost`: at `q = 1`, `|t_n| ≤ 2` for every `n`
    /// exactly when `a² ≤ 4`, and a boost's counts grow, `n + 2 ≤ |t_n|`.
    #[test]
    fn only_a_boost_has_unbounded_counts() {
        for a in -6i64..=6 {
            let counts = site(a, 1).trace_sequence(30);
            let bounded = counts.iter().all(|count| count.abs() <= integer(2));
            assert_eq!(bounded, a * a <= 4);
            if a * a > 4 {
                for (n, count) in counts.iter().enumerate() {
                    assert!(integer(i64::try_from(n).unwrap() + 2) <= count.abs());
                }
            }
        }
    }

    /// The period-`n` points of an integer material on the torus, counted by brute force over the
    /// grid `(1/|det(Mⁿ − 1)|)ℤ²`, which holds every solution of `(Mⁿ − 1)x ∈ ℤ²`; `None` when
    /// `det(Mⁿ − 1) = 0`, where the solutions form a subtorus, not a finite set.
    fn brute_force_torus_points(material: &Material2, period: usize) -> Option<BigUint> {
        let power = (0..period).fold(scalar(Rat::one()), |power, _| multiply(&power, material));
        let shifted = [
            [&power[0][0] - Rat::one(), power[0][1].clone()],
            [power[1][0].clone(), &power[1][1] - Rat::one()],
        ];
        let determinant = material_site(&shifted).determinant().abs();
        if determinant.is_zero() {
            return None;
        }
        let side = i64::try_from(&determinant.to_integer()).unwrap();
        let mut fixed = 0u64;
        for i in 0..side {
            for j in 0..side {
                let (x, y) = (rat(i, side), rat(j, side));
                let image_x = &shifted[0][0] * &x + &shifted[0][1] * &y;
                let image_y = &shifted[1][0] * &x + &shifted[1][1] * &y;
                if image_x.is_integer() && image_y.is_integer() {
                    fixed += 1;
                }
            }
        }
        Some(BigUint::from(fixed))
    }

    /// Lean `det_pow_sub_one`: **the torus count is `|t_n − 2|`, not `t_n`.** For the cat map the
    /// period-`n` points of `𝕋²` are counted by brute force, and they number
    /// `|det(Mⁿ − 1)| = |t_n − 2|`, while `t_n` counts the closed walks of `[[2, 1], [1, 1]]`.
    #[test]
    fn the_torus_counts_differ_from_the_closed_walks() {
        let cat = material([[2, 1], [1, 1]]);
        let site = material_site(&cat);
        let counts = site.trace_sequence(4);
        for (n, count) in counts.iter().enumerate().skip(1) {
            let fixed = brute_force_torus_points(&cat, n).unwrap();
            assert_eq!(torus_fixed_points(&site, n).unwrap(), Some(fixed.clone()));
            let fixed = Rat::from_integer(fixed.into());
            assert_eq!(fixed, (count - integer(2)).abs());
            assert_ne!(fixed, *count);
        }
    }

    /// **`|qⁿ − t_n + 1|` counts the torus points of every integer site, and only there.** The
    /// brute-force count agrees for determinants `1`, `−1`, `3`, `−3` and `0`, including sites
    /// with an eigenvalue `±1`, where it is `None`. The quarter-turn `(0, 1)` has `M⁴ = 1`: every
    /// point has period dividing four, so the count at `n = 4` is `None`, not `0`,
    /// while `n = 1` counts its two fixed points `(0, 0)` and `(½, ½)`. The site `(1/2, 3)` is no
    /// integer material and the period `0` counts nothing; both are refused.
    #[test]
    fn the_torus_count_is_refused_off_the_integer_sites() {
        for entries in [
            [[2, 1], [1, 1]],
            [[1, 1], [1, 0]],
            [[0, -1], [1, 0]],
            [[2, 1], [1, 2]],
            [[1, 1], [-1, 2]],
            [[1, 1], [0, 1]],
            [[1, 0], [0, 0]],
            [[-1, 1], [0, 3]],
        ] {
            let material = material(entries);
            let site = material_site(&material);
            for n in 1..=4 {
                assert_eq!(
                    torus_fixed_points(&site, n).unwrap(),
                    brute_force_torus_points(&material, n),
                    "{entries:?} at period {n}"
                );
            }
        }
        let quarter = site(0, 1);
        assert_eq!(quarter.kind(), SiteKind::Rotation);
        assert_eq!(torus_fixed_points(&quarter, 4).unwrap(), None);
        assert_eq!(torus_fixed_points(&quarter, 8).unwrap(), None);
        assert_eq!(
            torus_fixed_points(&quarter, 1).unwrap(),
            Some(BigUint::from(2u8))
        );
        let half = SiteFactor::new(rat(1, 2), integer(3));
        assert_eq!(
            torus_fixed_points(&half, 3),
            Err(LandmarkError::NotAnIntegerSite {
                trace: rat(1, 2),
                determinant: integer(3),
            })
        );
        assert_eq!(
            torus_fixed_points(&site(3, 1), 0),
            Err(LandmarkError::ZeroPeriod)
        );
    }

    /// **Only a null site or a boost has a Lorentz face.** The rotation `(1, 1)` has
    /// `a²/(4q) = 1/4 < 1`, which is `cos²θ`, not a Lorentz factor, and is refused with its kind;
    /// the null site `(2, 1)` has `γ² = 1`.
    #[test]
    fn a_rotation_has_no_lorentz_face() {
        assert_eq!(
            lorentz_factor_squared(&site(1, 1)),
            Err(LandmarkError::NoLorentzFace {
                kind: SiteKind::Rotation
            })
        );
        assert_eq!(
            lorentz_factor_squared(&site(0, 0)),
            Err(LandmarkError::NoLorentzFace {
                kind: SiteKind::Degenerate
            })
        );
        assert_eq!(lorentz_factor_squared(&site(2, 1)).unwrap(), Rat::one());
        assert_eq!(lorentz_factor_squared(&site(-4, 4)).unwrap(), Rat::one());
    }
}
