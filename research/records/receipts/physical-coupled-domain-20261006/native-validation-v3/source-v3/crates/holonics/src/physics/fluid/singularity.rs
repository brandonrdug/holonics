//! **Planar point-singularity flows are one-parameter Möbius navigators** (egg record §4).
//!
//! [definition] A singularity pair of strength `c = m + iΓ` (source `m`; `Γ` the **clockwise**
//! circulation, since the counterclockwise circulation is `−Γ` by `circulation_flux_jump`) at `z₁`,
//! with the opposite singularity at `z₂`, has the complex potential `F = (c/Θ) ℓ`, where `Θ` is the
//! turn (`2π` in the classical chart, never evaluated) and `ℓ` is a lift of the logarithm of the
//! **undivided ratio** `(z − z₁ : z − z₂)` carried with its winding ([`crate::ratio::LogRatio`],
//! the loss chart `ℓ = log R` of `Objects/Ratio.logFibre`). Its velocity `u = conj F′` satisfies
//!
//! ```text
//! Θ |W|² u = conj(c) · W,      W = (z − z₁)(z − z₂)/(z₁ − z₂)
//! ```
//!
//! ([`SingularityPair::turn_velocity`], Lean `Physics/Fluid/Singularity.velocity_is_mobius_field`):
//! a positive multiple of the vector field `λ W`, `λ = conj c`, of the one-parameter Möbius
//! navigator fixing `z₁`, `z₂` ([`SingularityPair::generator`], Lean `generator`, `generator_field`),
//! carried as the traceless block of `compression::landmark`'s [`MobiusNavigator`] over `ℚ(i)`
//! ([`MobiusNavigator::generator`]).
//! The streamlines are its orbits, and the flow's kind is read from the generator's discriminant
//! `D = λ²` ([`flow_kind`], Lean `flowKind`, `generator_discriminant`):
//!
//! | pair | `c` | `D` | kind |
//! |---|---|---|---|
//! | source–sink | `m` | `m² > 0` | boost ([`SiteKind::Boost`]) |
//! | vortex pair | `iΓ` | `−Γ² < 0` | rotation ([`SiteKind::Rotation`]) |
//! | doublet (merged) | `μ/(z − z₀)` | `0`, nilpotent | null ([`SiteKind::Null`]) |
//! | spiral pair | `m + iΓ`, `mΓ ≠ 0` | `∉ ℝ` | loxodromic |
//!
//! The three real kinds are [`crate::navigator::trace::SiteKind`] itself (Lean `FlowKind.site`): a
//! real discriminant is read through the site of the generator's **Cayley block**
//! `(1 − det X/4)·1 + X`, the rational Cayley element up to scale ([`cayley_block`], Lean
//! `cayleyBlock`, `cayley_siteKind_{boost,rotation,null}`), which for a real pair is a navigator
//! over `ℚ` ([`MobiusNavigator::real`]). A loxodromic flow has a non-real discriminant, so no real
//! site (Lean `real_generator_not_loxodromic`); its Cayley multiplier is a Gaussian rational off
//! both the real line and the unit circle ([`SingularityPair::cayley_multiplier`]).
//!
//! | Lean `Physics/Fluid/Singularity` | Rust |
//! |---|---|
//! | `W`, `hasDerivAt_potential`, `velocity_is_mobius_field` | [`SingularityPair::quadratic`], [`SingularityPair::turn_velocity`] |
//! | `mobiusField`, `hasDerivAt_act`, `generator`, `generator_field`, `generator_fixes`, `generator_discriminant` | [`mobius_field`], [`SingularityPair::generator`] |
//! | `FlowKind`, `flowKind`, `flowKind_eq`, `flowKind_smul`, `cayley_flowKind`, `pair_kind_{boost,rotation,loxodromic}`, `quarter_turn_exchanges` | [`FlowKind`], [`flow_kind`], [`SingularityPair::kind`] |
//! | `siteGenerator`, `offPole`, `cayley_siteKind_eq` | [`cayley_site`] |
//! | `parabolic`, `doublet_velocity_is_mobius_field`, `doublet_null` | [`Doublet`] |
//! | `cayleyBlock`, `cayleyBlock_fixed_iff`, `cayleyBlock_discriminant`, `sourceSink_is_boost_site`, `vortexPair_is_rotation_site`, `sourceSink_fixes_one` | [`cayley_block`], [`MobiusNavigator::real`] |
//! | `potential_jump`, `circulation_flux_jump`, `principal_mem_logFibre`, `logRatio_is_clock` | [`SingularityPair::potential_jump`], [`SingularityPair::log_ratio`], [`crate::ratio::LogRatio`] |

use num_traits::{One, Zero};

use crate::compression::landmark::MobiusNavigator;
use crate::navigator::trace::{SiteFactor, SiteKind};
use crate::ratio::{GaussianRat, LogRatio, Rat, integer, rat};

use super::FluidError;

/// [definition] **The vector field of a generator** `b + (a − d) z − c z²`, the derivative at
/// `t = 0` of `(1 + tX)·z` (Lean `mobiusField`, `hasDerivAt_act`).
pub fn mobius_field(generator: &MobiusNavigator<GaussianRat>, z: &GaussianRat) -> GaussianRat {
    let [a, b, c, d] = generator.entries();
    b.add(&a.sub(d).mul(z)).sub(&c.mul(&z.mul(z)))
}

/// [proved-derived; implemented-exact] **The Cayley block** of a traceless generator,
/// `(1 − det X/4)·1 + X`: the rational Cayley element `(1 + X/2)(1 − X/2)⁻¹` up to the scale
/// `1 + det X/4`, with the generator's fixed points and discriminant (Lean `cayleyBlock`,
/// `cayleyBlock_fixed_iff`, `cayleyBlock_discriminant`). Refused off the traceless blocks and at
/// the Cayley pole `det X = −4`, where the block is singular.
pub fn cayley_block(
    generator: &MobiusNavigator<GaussianRat>,
) -> Result<MobiusNavigator<GaussianRat>, FluidError> {
    if !generator.trace().is_zero() {
        return Err(FluidError::NotTraceless);
    }
    let det = generator.determinant();
    if det == GaussianRat::real(integer(-4)) {
        return Err(FluidError::CayleyPole);
    }
    let s = GaussianRat::one().sub(&det.scale(&rat(1, 4)));
    let [a, b, c, d] = generator.entries();
    Ok(MobiusNavigator::new(
        a.add(&s),
        b.clone(),
        c.clone(),
        d.add(&s),
    )?)
}

/// [definition] **The kind of a one-parameter Möbius navigator** (Lean `FlowKind`: `site` of a
/// [`SiteKind`] or `loxodromic`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlowKind {
    Site(SiteKind),
    Loxodromic,
}

/// [definition] **The site of the Cayley block** of a traceless generator with real discriminant
/// `D`, after the clock rescaling `s² = 1/(1 + D²)` that keeps it off the Cayley pole: trace
/// `2 + D′/8`, determinant `(1 − D′/16)²`, discriminant `D′ = s² D` (Lean `siteGenerator`,
/// `offPole`, `cayleyBlock_trace`, `cayleyBlock_det`, `cayleyBlock_discriminant`,
/// `cayley_siteKind_eq`, `flowKind_smul`).
pub fn cayley_site(discriminant: &Rat) -> SiteFactor {
    let scaled = discriminant / (Rat::one() + discriminant * discriminant);
    let factor = Rat::one() - &scaled / integer(16);
    SiteFactor::new(integer(2) + &scaled / integer(8), &factor * &factor)
}

/// [proved-derived; implemented-exact] **The flow kind of a discriminant** (Lean `flowKind`,
/// `flowKind_eq`, and `cayley_flowKind`, `cayley_siteKind_{boost,rotation,null}` for the real
/// ones): loxodromic off the real line, otherwise the [`SiteKind`] of its Cayley site.
pub fn flow_kind(discriminant: &GaussianRat) -> FlowKind {
    if !discriminant.is_real() {
        return FlowKind::Loxodromic;
    }
    FlowKind::Site(cayley_site(&discriminant.re).kind())
}

/// [definition] **A singularity pair**: strength `c = m + iΓ` at `z₁`, the opposite at `z₂`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SingularityPair {
    first: GaussianRat,
    second: GaussianRat,
    strength: GaussianRat,
}

impl SingularityPair {
    /// A pair; coincident singularities are refused (that limit is the [`Doublet`]).
    pub fn new(
        first: GaussianRat,
        second: GaussianRat,
        strength: GaussianRat,
    ) -> Result<Self, FluidError> {
        if first == second {
            return Err(FluidError::CoincidentSingularities);
        }
        Ok(Self {
            first,
            second,
            strength,
        })
    }

    pub fn strength(&self) -> &GaussianRat {
        &self.strength
    }

    /// `W = (z − z₁)(z − z₂)/(z₁ − z₂)` (Lean `W`).
    pub fn quadratic(&self, z: &GaussianRat) -> Result<GaussianRat, FluidError> {
        Ok(z.sub(&self.first)
            .mul(&z.sub(&self.second))
            .div(&self.first.sub(&self.second))?)
    }

    /// [proved-derived; implemented-exact] **The velocity in turn units** `Θ u = conj(c) W / |W|²`
    /// (Lean `hasDerivAt_potential`, `velocity_is_mobius_field`), refused at the singularities.
    pub fn turn_velocity(&self, z: &GaussianRat) -> Result<GaussianRat, FluidError> {
        let w = self.quadratic(z)?;
        let quadrance = w.norm_sq();
        if quadrance.is_zero() {
            return Err(FluidError::ZeroDivisor {
                what: "the pair's quadratic at a singularity",
            });
        }
        Ok(self
            .strength
            .conj()
            .mul(&w)
            .scale(&(Rat::one() / quadrance)))
    }

    /// [definition] **The pair's generator** at rate `λ = conj c` fixing `z₁`, `z₂` (Lean
    /// `generator`): its field is `λ W` (Lean `generator_field`).
    pub fn generator(&self) -> Result<MobiusNavigator<GaussianRat>, FluidError> {
        let lam = self.strength.conj();
        let gap = self.first.sub(&self.second);
        let sum = self.first.add(&self.second);
        Ok(MobiusNavigator::generator(
            lam.neg().mul(&sum).div(&gap.scale(&integer(2)))?,
            lam.mul(&self.first).mul(&self.second).div(&gap)?,
            lam.neg().div(&gap)?,
        ))
    }

    /// [proved-derived; implemented-exact] **The pair's kind** from `D = conj(c)²` (Lean
    /// `generator_discriminant`, `pair_kind_{boost,rotation,loxodromic}`).
    pub fn kind(&self) -> Result<FlowKind, FluidError> {
        Ok(flow_kind(&self.generator()?.discriminant()))
    }

    /// [proved-derived; implemented-exact] **The Cayley multiplier** `k = (s + λ/2)/(s − λ/2)`,
    /// `s = 1 + λ²/16`: the scaling of the fixed-point chart `(z − z₁)/(z − z₂)` under the Cayley
    /// block (Lean `Compression/Landmark/FixedPoint.chart_conjugates`). Real and positive for a
    /// boost, unimodular for a rotation, neither for a loxodromic pair. Refused at the Cayley pole
    /// `λ = ±4` (`det X = −λ²/4 = −4`), where the block is singular.
    pub fn cayley_multiplier(&self) -> Result<GaussianRat, FluidError> {
        let lam = self.strength.conj();
        let square = lam.mul(&lam);
        if square == GaussianRat::real(integer(16)) {
            return Err(FluidError::CayleyPole);
        }
        let s = GaussianRat::one().add(&square.scale(&rat(1, 16)));
        let half = lam.scale(&rat(1, 2));
        Ok(s.add(&half).div(&s.sub(&half))?)
    }

    /// The lift of `(z − z₁ : z − z₂)` at a declared winding: the principal logarithm of the
    /// divided ratio lies in the log fibre of the undivided one (Lean `principal_mem_logFibre`),
    /// and along the generator's flow it advances at the rate `λ`, the navigator's clock (Lean
    /// `logRatio_is_clock`).
    pub fn log_ratio(&self, z: &GaussianRat, winding: i64) -> Result<LogRatio, FluidError> {
        Ok(LogRatio::new(
            z.sub(&self.first),
            z.sub(&self.second),
            winding,
        )?)
    }

    /// [proved-derived; implemented-exact] **The potential's jump over `n` turns**, `i c n` (Lean
    /// `potential_jump`): its real part, the counterclockwise circulation, is `−Γ n`, and its
    /// imaginary part, the flux, is `m n` (Lean `circulation_flux_jump`).
    pub fn potential_jump(
        &self,
        from: &LogRatio,
        to: &LogRatio,
    ) -> Result<Option<GaussianRat>, FluidError> {
        Ok(to
            .turns_from(from)?
            .map(|turns| GaussianRat::i().mul(&self.strength).scale(&integer(turns))))
    }
}

/// [definition] **The doublet**: the pair merged at `z₀` with moment `μ`, `F = μ/(z − z₀)` (Lean
/// `parabolic`, `doublet_velocity_is_mobius_field`, `doublet_null`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doublet {
    pub centre: GaussianRat,
    pub moment: GaussianRat,
}

impl Doublet {
    /// The parabolic generator `conj(μ) [[z₀, −z₀²], [1, −z₀]]` (Lean `parabolic`), nilpotent.
    pub fn generator(&self) -> MobiusNavigator<GaussianRat> {
        let kappa = self.moment.conj();
        MobiusNavigator::generator(
            kappa.mul(&self.centre),
            kappa.neg().mul(&self.centre.mul(&self.centre)),
            kappa,
        )
    }

    /// [proved-derived; implemented-exact] **The velocity** `u = conj(F′)`, which is the parabolic
    /// field over `|z − z₀|⁴` (Lean `doublet_velocity_is_mobius_field`).
    pub fn velocity(&self, z: &GaussianRat) -> Result<GaussianRat, FluidError> {
        let offset = z.sub(&self.centre);
        let quadrance = offset.norm_sq();
        if quadrance.is_zero() {
            return Err(FluidError::ZeroDivisor {
                what: "the doublet at its centre",
            });
        }
        Ok(mobius_field(&self.generator(), z).scale(&(Rat::one() / (&quadrance * &quadrance))))
    }

    /// The doublet's kind: null (Lean `doublet_null`).
    pub fn kind(&self) -> FlowKind {
        flow_kind(&self.generator().discriminant())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn g(re: i64, im: i64) -> GaussianRat {
        GaussianRat::from_i64(re, im)
    }

    fn pair(strength: GaussianRat) -> SingularityPair {
        SingularityPair::new(g(-1, 0), g(1, 0), strength).unwrap()
    }

    /// Lean `velocity_is_mobius_field`, `generator_field`: the velocity is the generator's field
    /// over the positive `|W|²`, at several points, and the field vanishes at both singularities.
    #[test]
    fn the_velocity_is_a_positive_multiple_of_the_mobius_field() {
        let pair =
            SingularityPair::new(g(2, -1), GaussianRat::new(rat(-1, 2), integer(3)), g(3, -2))
                .unwrap();
        let generator = pair.generator().unwrap();
        for z in [g(0, 0), GaussianRat::new(rat(5, 3), rat(-1, 7)), g(-4, 2)] {
            let w = pair.quadratic(&z).unwrap();
            let velocity = pair.turn_velocity(&z).unwrap();
            assert_eq!(velocity.scale(&w.norm_sq()), mobius_field(&generator, &z));
            assert_eq!(mobius_field(&generator, &z), pair.strength().conj().mul(&w));
        }
        assert!(mobius_field(&generator, &g(2, -1)).is_zero());
        assert!(mobius_field(&generator, &GaussianRat::new(rat(-1, 2), integer(3))).is_zero());
        assert!(generator.trace().is_zero());
        assert!(pair.turn_velocity(&g(2, -1)).is_err());
    }

    /// Lean `generator_discriminant`, `pair_kind_boost`, `sourceSink_is_boost_site`,
    /// `sourceSink_fixes_one`: the source–sink pair is a boost; its real Cayley block is a
    /// `compression::landmark` boost navigator fixing `±1`, whose chart scaling is the Cayley
    /// multiplier's inverse `9/25`.
    #[test]
    fn the_source_sink_pair_is_a_boost() {
        let pair = pair(g(1, 0));
        assert_eq!(pair.generator().unwrap().discriminant(), g(1, 0));
        assert_eq!(pair.kind().unwrap(), FlowKind::Site(SiteKind::Boost));
        let cayley = cayley_block(&pair.generator().unwrap()).unwrap();
        let navigator = cayley.real().expect("a real block");
        assert_eq!(navigator.kind(), SiteKind::Boost);
        assert!(cayley.fixes(&g(1, 0)) && cayley.fixes(&g(-1, 0)));
        assert_eq!(
            pair.cayley_multiplier().unwrap(),
            GaussianRat::real(rat(25, 9))
        );
        let scaling = navigator.chart_scaling().unwrap();
        assert_eq!(scaling.as_rational(), Some(&rat(9, 25)));
    }

    /// Lean `pair_kind_rotation`, `vortexPair_is_rotation_site`: the vortex pair on `±i` is a
    /// rotation with a real Cayley block and the unimodular multiplier `(161 − 240i)/289`.
    #[test]
    fn the_vortex_pair_is_a_rotation() {
        let pair = SingularityPair::new(g(0, 1), g(0, -1), g(0, 1)).unwrap();
        assert_eq!(pair.kind().unwrap(), FlowKind::Site(SiteKind::Rotation));
        let cayley = cayley_block(&pair.generator().unwrap()).unwrap();
        assert_eq!(
            cayley.real().expect("a real block").kind(),
            SiteKind::Rotation
        );
        let k = pair.cayley_multiplier().unwrap();
        assert_eq!(k, GaussianRat::new(rat(161, 289), rat(-240, 289)));
        assert_eq!(k.norm_sq(), Rat::one());
    }

    /// Lean `pair_kind_loxodromic`, `real_generator_not_loxodromic`: the spiral pair has the
    /// non-real discriminant `−2i`, no real Cayley block, and the multiplier `(33 − 56i)/25` of
    /// modulus `13/5`, off the real line and the unit circle.
    #[test]
    fn the_spiral_pair_is_loxodromic() {
        let pair = pair(g(1, 1));
        let generator = pair.generator().unwrap();
        assert_eq!(generator.discriminant(), g(0, -2));
        assert_eq!(pair.kind().unwrap(), FlowKind::Loxodromic);
        assert!(cayley_block(&generator).unwrap().real().is_none());
        let k = pair.cayley_multiplier().unwrap();
        assert_eq!(k, GaussianRat::new(rat(33, 25), rat(-56, 25)));
        assert_eq!(k.norm_sq(), rat(169, 25));
    }

    /// Lean `doublet_velocity_is_mobius_field`, `doublet_null`: the doublet's velocity is the
    /// parabolic field over `|z − z₀|⁴`, its generator is nilpotent, and it is null; for a real
    /// moment at `0` its Cayley block is the `compression::landmark` shear.
    #[test]
    fn the_doublet_is_null() {
        let doublet = Doublet {
            centre: GaussianRat::new(rat(1, 2), integer(-1)),
            moment: g(2, 3),
        };
        let z = g(3, 1);
        let offset = z.sub(&doublet.centre);
        let f_prime = doublet.moment.neg().div(&offset.mul(&offset)).unwrap();
        assert_eq!(doublet.velocity(&z).unwrap(), f_prime.conj());
        assert!(doublet.generator().discriminant().is_zero());
        assert!(!doublet.generator().entries()[2].is_zero());
        assert_eq!(doublet.kind(), FlowKind::Site(SiteKind::Null));
        let real = Doublet {
            centre: g(0, 0),
            moment: g(2, 0),
        };
        let navigator = cayley_block(&real.generator()).unwrap().real().unwrap();
        assert_eq!(navigator.kind(), SiteKind::Null);
    }

    /// Lean `flowKind_smul`, `quarter_turn_exchanges`: rescaling the clock keeps the kind, a quarter
    /// turn of the rate exchanges boost and rotation, and the Cayley pole is refused.
    #[test]
    fn the_kind_is_a_class_of_the_generator_up_to_its_clock() {
        for d in [integer(3), integer(-5), integer(16), Rat::zero()] {
            let scaled = &d * rat(49, 4);
            assert_eq!(
                flow_kind(&GaussianRat::real(d.clone())),
                flow_kind(&GaussianRat::real(scaled))
            );
        }
        let boost = pair(g(2, 0));
        let rotation = pair(g(0, 2));
        assert_eq!(boost.kind().unwrap(), FlowKind::Site(SiteKind::Boost));
        assert_eq!(rotation.kind().unwrap(), FlowKind::Site(SiteKind::Rotation));
        let pole = MobiusNavigator::generator(g(0, 0), g(2, 0), g(2, 0));
        assert_eq!(cayley_block(&pole), Err(FluidError::CayleyPole));
        // The pair of rate `λ = ±4` sits at that pole: its multiplier is refused as the pole.
        for rate in [4, -4] {
            assert_eq!(
                pair(g(rate, 0)).cayley_multiplier(),
                Err(FluidError::CayleyPole)
            );
        }
        assert_eq!(
            flow_kind(&pole.discriminant()),
            FlowKind::Site(SiteKind::Boost)
        );
    }

    /// Lean `potential_jump`, `circulation_flux_jump`, `Objects/Ratio.logFibre_torsor`: two lifts
    /// of the ratio differ by whole turns, the potential jumps by `i c n`, the counterclockwise
    /// circulation by `−Γ n` and the flux by `m n`; the modulus is carried as an exact log form and
    /// returns through the chart transition.
    #[test]
    fn circulation_and_flux_are_winding_readings_of_the_ratio() {
        let pair = pair(GaussianRat::new(integer(3), integer(-2)));
        let z = GaussianRat::new(rat(1, 3), integer(2));
        let start = pair.log_ratio(&z, 0).unwrap();
        let end = start.advanced(2);
        let jump = pair
            .potential_jump(&start, &end)
            .unwrap()
            .expect("one ratio");
        assert_eq!(jump.re, integer(4));
        assert_eq!(jump.im, integer(6));
        let elsewhere = pair.log_ratio(&g(0, 1), 1).unwrap();
        assert_eq!(pair.potential_jump(&start, &elsewhere).unwrap(), None);
        let expected = z.sub(&g(-1, 0)).norm_sq() / z.sub(&g(1, 0)).norm_sq();
        assert_eq!(start.modulus().unwrap(), expected);
        assert!(LogRatio::new(g(0, 0), g(1, 0), 0).is_err());
    }
}
