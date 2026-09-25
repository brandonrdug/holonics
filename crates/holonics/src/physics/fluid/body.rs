//! **A closed body in a stream is a globe; a net emission opens it into a tube** (egg record §4).
//!
//! [definition] A uniform stream `U` with point singularities of strengths `c_k = m_k + iΓ_k`
//! (`Γ_k` the clockwise circulation, as in [`super::singularity`]) at
//! `z_k` ([`StreamBody`]) has the potential `F = U z + Σ (c_k/Θ) ℓ_k`, each `ℓ_k` a lift of the
//! undivided ratio `(z − z_k : 1)` with its winding ([`LogRatio`]; Lean
//! `Physics/Fluid/Body.liftedPotential`). A **dividing streamline** keeps `ψ = Im F` constant along
//! it. Continuing the lifts around an actual closed loop advances each by the loop's winding
//! number `n_k` about `z_k` (path lifting, [`LogRatio::continued`]; [`StreamBody::loop_windings`]),
//! so the potential returns jumped by `i Σ c_k n_k` and `ψ` by the enclosed emission `Σ m_k n_k`
//! ([`StreamBody::stream_jump`], Lean `loop_jump`, `stream_jump`). So a closed dividing streamline
//! encircling every singularity once forces **zero net strength** ([`StreamBody::enclosure`], Lean
//! `closed_streamline_net_zero`): the Gauss/Rankine necessity.
//!
//! [counterexample] **Nonzero net emission opens the body into a tube** ([`HalfBody`], Lean
//! `halfBody_reaches`, `halfBody_width`, `halfBody_unbounded`): one source `m` in a stream `U` has a
//! dividing streamline reaching every downstream station below the half-width `m/(2U)`; far
//! downstream the tube of width `m/U` carries the emitted flux `m` at the stream speed.
//!
//! [definition] **The same law on a Holarchy block** ([`gauss`], Lean `streamline_membrane_net_zero`,
//! composing `Holarchy/Globe.blockMembrane_gauss`): the whole's membrane flux is its enclosed
//! divergence, so a membrane carrying no current (a streamline) encloses zero net emission; a tube's
//! lateral streamlines enclose emission that leaves through its open ends (Lean
//! `tube_encloses_emission`). A block's membrane bounds its interior by construction, clause (3) of
//! relative completeness (Lean `block_bounds`, `Objects/RelativeCompleteness`).
//!
//! | Lean `Physics/Fluid/Body` | Rust |
//! |---|---|
//! | `liftedPotential`, `loop_jump`, `stream_jump` | [`StreamBody::potential_jump`], [`StreamBody::stream_jump`] |
//! | `sitePath`, `siteLift`, `siteLift_advance`, `winding`, `circleLoop_winding` | [`StreamBody::loop_windings`], [`LogRatio::continued`] |
//! | `closed_streamline_balances`, `closed_streamline_net_zero` | [`StreamBody::enclosure`] |
//! | `halfBodyStream`, `halfBody_reaches`, `halfBody_width`, `halfBody_unbounded` | [`HalfBody`] |
//! | `streamline_membrane_net_zero`, `block_bounds`, `tube_encloses_emission` | [`gauss`], [`GaussReading`] |
//!
//! [open] Sufficiency (zero net strength gives a closed Rankine oval) is not proved; clauses (1) and
//! (2) of relative completeness for a body are not stated (#62).

use num_traits::{Signed, Zero};

use crate::holarchy::Holarchy;
use crate::ratio::linear::vector::dot;
use crate::ratio::{GaussianRat, LogRatio, Rat, integer, rat};

use super::FluidError;

/// [definition] **A point singularity**: strength `c = m + iΓ` at a site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointSingularity {
    pub site: GaussianRat,
    pub strength: GaussianRat,
}

/// [definition] **A uniform stream with point singularities.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamBody {
    stream: Rat,
    singularities: Vec<PointSingularity>,
}

/// [definition] **What a closed loop requires of a dividing streamline along it**: the stream
/// function returns unchanged (the necessary condition holds) or it returns changed by the
/// enclosed emission, and then the loop is no dividing streamline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Enclosure {
    /// `Σ m_k n_k = 0` around the loop: the necessary condition of a closed body holds.
    Balanced,
    /// `Σ m_k n_k ≠ 0`: `ψ` is not single-valued around the loop, which is no dividing streamline.
    Emitting { enclosed_emission: Rat },
}

impl StreamBody {
    pub fn new(stream: Rat, singularities: Vec<PointSingularity>) -> Self {
        Self {
            stream,
            singularities,
        }
    }

    pub fn stream(&self) -> &Rat {
        &self.stream
    }

    /// `Σ m_k`.
    pub fn net_strength(&self) -> Rat {
        self.singularities
            .iter()
            .fold(Rat::zero(), |sum, s| sum + &s.strength.re)
    }

    /// The lifts of `(z − z_k : 1)` at declared windings.
    pub fn lifts(&self, z: &GaussianRat, windings: &[i64]) -> Result<Vec<LogRatio>, FluidError> {
        self.check(windings)?;
        self.singularities
            .iter()
            .zip(windings)
            .map(|(s, n)| Ok(LogRatio::new(z.sub(&s.site), GaussianRat::one(), *n)?))
            .collect()
    }

    fn check(&self, windings: &[i64]) -> Result<(), FluidError> {
        if windings.len() != self.singularities.len() {
            return Err(FluidError::Shape {
                what: "windings (one per singularity)",
                expected: self.singularities.len(),
                found: windings.len(),
            });
        }
        Ok(())
    }

    /// [proved-derived; implemented-exact] **The loop jump** `i Σ c_k n_k` of the potential between
    /// two lifts at one point (Lean `loop_jump`, from `Singularity.potential_jump`).
    pub fn potential_jump(
        &self,
        from: &[LogRatio],
        to: &[LogRatio],
    ) -> Result<GaussianRat, FluidError> {
        if from.len() != self.singularities.len() || to.len() != from.len() {
            return Err(FluidError::Shape {
                what: "lifts (one per singularity)",
                expected: self.singularities.len(),
                found: from.len().min(to.len()),
            });
        }
        let mut jump = GaussianRat::zero();
        for ((s, start), end) in self.singularities.iter().zip(from).zip(to) {
            let turns = end.turns_from(start)?.ok_or(FluidError::Shape {
                what: "lifts of one point's ratios",
                expected: 1,
                found: 0,
            })?;
            jump = jump.add(&GaussianRat::i().mul(&s.strength).scale(&integer(turns)));
        }
        Ok(jump)
    }

    /// [proved-derived; implemented-exact] **The stream function's jump** `Σ m_k n_k` over a loop of
    /// windings `n` (Lean `stream_jump`): zero on a closed dividing streamline (Lean
    /// `closed_streamline_balances`).
    pub fn stream_jump(&self, windings: &[i64]) -> Result<Rat, FluidError> {
        self.check(windings)?;
        Ok(self
            .singularities
            .iter()
            .zip(windings)
            .fold(Rat::zero(), |sum, (s, n)| {
                sum + &s.strength.re * integer(*n)
            }))
    }

    /// [proved-derived; implemented-exact] **The windings of an actual closed loop** (path
    /// lifting, Lean `siteLift`, `siteLift_advance`, `winding`): from the principal lift of
    /// `(z − z_k : 1)` at the polygon's first vertex, each lift
    /// is continued along the polygon and back to its start ([`LogRatio::continued`]); it returns
    /// advanced by the polygon's winding number about `z_k`. Refused when the polygon has fewer than
    /// three vertices or passes through a singularity.
    pub fn loop_windings(&self, polygon: &[GaussianRat]) -> Result<Vec<i64>, FluidError> {
        if polygon.len() < 3 {
            return Err(FluidError::Shape {
                what: "a closed polygon's vertices",
                expected: 3,
                found: polygon.len(),
            });
        }
        self.singularities
            .iter()
            .map(|s| {
                let chart: Vec<GaussianRat> = polygon[1..]
                    .iter()
                    .chain(std::iter::once(&polygon[0]))
                    .map(|vertex| vertex.sub(&s.site))
                    .collect();
                let start = LogRatio::new(polygon[0].sub(&s.site), GaussianRat::one(), 0)?;
                Ok(start.continued(&chart)?.winding)
            })
            .collect()
    }

    /// [proved-derived; implemented-exact] **Necessity along an actual loop**: `ψ` returns around
    /// the closed polygon changed by `Σ m_k n_k`, `n_k` its windings ([`Self::loop_windings`]), so a
    /// closed dividing streamline, along which `ψ` is constant, needs it zero; around every
    /// singularity once it is the net strength `Σ m_k` (Lean `closed_streamline_balances`,
    /// `closed_streamline_net_zero`).
    pub fn enclosure(&self, polygon: &[GaussianRat]) -> Result<Enclosure, FluidError> {
        let enclosed_emission = self.stream_jump(&self.loop_windings(polygon)?)?;
        Ok(if enclosed_emission.is_zero() {
            Enclosure::Balanced
        } else {
            Enclosure::Emitting { enclosed_emission }
        })
    }
}

/// [definition] **Rankine's half-body**: one source `m > 0` at the origin in a stream `U > 0`. With
/// the angle read in turns `τ = θ/Θ`, its stream function is `ψ = U y + m τ` and its dividing
/// streamline is `ψ = m/2` (Lean `halfBodyStream`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HalfBody {
    stream: Rat,
    strength: Rat,
}

impl HalfBody {
    /// Refused unless `U > 0` and `m > 0`.
    pub fn new(stream: Rat, strength: Rat) -> Result<Self, FluidError> {
        if !stream.is_positive() {
            return Err(FluidError::NotPositive {
                what: "a half-body's stream",
            });
        }
        if !strength.is_positive() {
            return Err(FluidError::NotPositive {
                what: "a half-body's source strength",
            });
        }
        Ok(Self { stream, strength })
    }

    /// The dividing streamline's value `m/2`.
    pub fn dividing_value(&self) -> Rat {
        &self.strength / integer(2)
    }

    /// `ψ = U y + m τ` at a point whose direction is `τ` turns (the caller's declaration, checked
    /// against the point for the octant directions).
    pub fn stream_function(&self, point: &GaussianRat, turns: &Rat) -> Result<Rat, FluidError> {
        self.check_direction(point, turns)?;
        Ok(&self.stream * &point.im + &self.strength * turns)
    }

    fn cotangent(turns: &Rat) -> Result<Rat, FluidError> {
        for (numerator, cotangent) in [(1, 1), (2, 0), (3, -1)] {
            if *turns == rat(numerator, 8) {
                return Ok(integer(cotangent));
            }
        }
        Err(FluidError::IrrationalDirection {
            numerator: i64::try_from(turns.numer()).unwrap_or(i64::MAX),
            denominator: i64::try_from(turns.denom()).unwrap_or(i64::MAX),
        })
    }

    fn check_direction(&self, point: &GaussianRat, turns: &Rat) -> Result<(), FluidError> {
        let cotangent = Self::cotangent(turns)?;
        if !point.im.is_positive() || point.re != &cotangent * &point.im {
            return Err(FluidError::IrrationalDirection {
                numerator: i64::try_from(turns.numer()).unwrap_or(i64::MAX),
                denominator: i64::try_from(turns.denom()).unwrap_or(i64::MAX),
            });
        }
        Ok(())
    }

    /// [established-bounded; implemented-exact] **A point of the dividing streamline** at the
    /// octant direction `τ ∈ {1/8, 1/4, 3/8}`: `y = (m/U)(1/2 − τ)`, `x = y cot(Θτ)`. Other
    /// directions have no rational cotangent and are refused.
    pub fn dividing_point(&self, turns: &Rat) -> Result<GaussianRat, FluidError> {
        let cotangent = Self::cotangent(turns)?;
        let y = &self.strength / &self.stream * (rat(1, 2) - turns);
        Ok(GaussianRat::new(&cotangent * &y, y))
    }

    /// [proved-derived; implemented-exact] **The half-width** `m/(2U)` that every point of the upper
    /// branch stays below (Lean `halfBody_width`).
    pub fn half_width(&self) -> Rat {
        &self.strength / (integer(2) * &self.stream)
    }

    /// **The tube's asymptotic width** `m/U`, which carries the emitted flux `m` at the stream speed.
    pub fn asymptotic_width(&self) -> Rat {
        &self.strength / &self.stream
    }

    /// The flux the tube carries far downstream, `U · (m/U) = m`.
    pub fn carried_flux(&self) -> Rat {
        &self.stream * self.asymptotic_width()
    }
}

/// [definition] **Gauss on a Holarchy's whole**: the flux of a face current through the whole's
/// membrane and the divergence it encloses (Lean `Holarchy/Globe.blockMembrane_gauss`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaussReading {
    pub membrane_flux: Rat,
    pub enclosed_divergence: Rat,
    /// Whether the current vanishes on every face of the membrane (a streamline membrane).
    pub streamline: bool,
}

/// [proved-derived; implemented-exact] **The membrane flux is the enclosed divergence** on a
/// Holarchy's glued complex, and a streamline membrane encloses zero net divergence (Lean
/// `streamline_membrane_net_zero`).
pub fn gauss(holarchy: &Holarchy, current: &[Rat]) -> Result<GaussReading, FluidError> {
    let membrane_flux = holarchy.flux(current)?.whole;
    let cells = holarchy.gluing().cells().ok_or(FluidError::NotATopCell {
        what: "Holarchy (it declares no glued complex)",
    })?;
    let d = cells.region_degree();
    let boundary = cells.glued().boundary(d).ok_or(FluidError::NotATopCell {
        what: "Holarchy (its glued complex has no faces)",
    })?;
    let interior = holarchy.whole_interior()?;
    let divergence = boundary.transpose()?.apply(current)?;
    let membrane = boundary.apply(&interior)?;
    let streamline = membrane
        .iter()
        .zip(current)
        .all(|(m, j)| m.is_zero() || j.is_zero());
    Ok(GaussReading {
        membrane_flux,
        enclosed_divergence: dot(&divergence, &interior),
        streamline,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::physics::fluid::cells::{GridCell, reflect_across_face};

    fn g(re: i64, im: i64) -> GaussianRat {
        GaussianRat::from_i64(re, im)
    }

    fn body(strengths: &[(i64, i64)]) -> StreamBody {
        StreamBody::new(
            integer(2),
            strengths
                .iter()
                .enumerate()
                .map(|(k, (m, gamma))| PointSingularity {
                    site: g(k as i64 - 1, (k as i64) % 2),
                    strength: g(*m, *gamma),
                })
                .collect(),
        )
    }

    /// Lean `loop_jump`, `stream_jump`: advancing every lift by its winding jumps the potential by
    /// `i Σ c_k n_k` and the stream function by `Σ m_k n_k`.
    #[test]
    fn the_loop_jump_is_the_enclosed_emission() {
        let body = body(&[(3, 1), (-1, 2), (2, -5)]);
        let z = g(4, 3);
        let windings = [1, 0, 2];
        let from = body.lifts(&z, &[0, 0, 0]).unwrap();
        let to = body.lifts(&z, &windings).unwrap();
        let jump = body.potential_jump(&from, &to).unwrap();
        assert_eq!(jump.im, body.stream_jump(&windings).unwrap());
        assert_eq!(jump.im, integer(3 + 4));
        assert_eq!(jump.re, integer(-1 + 10));
    }

    /// A counterclockwise square of half-side `r` about `(x, y)`.
    fn square(x: Rat, y: Rat, r: Rat) -> Vec<GaussianRat> {
        [(1, 1), (-1, 1), (-1, -1), (1, -1)]
            .iter()
            .map(|(a, b)| GaussianRat::new(&x + &r * integer(*a), &y + &r * integer(*b)))
            .collect()
    }

    /// Lean `closed_streamline_net_zero`, `closed_streamline_balances`: the lifts continued around
    /// an actual loop return advanced by its winding numbers, and `ψ` by the enclosed emission. A
    /// Rankine pair (source and sink) inside a loop is balanced, circulations do not enter, and a
    /// loop around the source alone returns `ψ` changed by `m`.
    #[test]
    fn a_closed_loop_around_a_rankine_pair_is_balanced() {
        let rankine = body(&[(3, 0), (-3, 0)]);
        let around = square(Rat::zero(), Rat::zero(), integer(3));
        assert_eq!(rankine.loop_windings(&around).unwrap(), vec![1, 1]);
        assert_eq!(rankine.enclosure(&around).unwrap(), Enclosure::Balanced);
        let swirling = body(&[(3, 7), (-3, -2)]);
        assert_eq!(swirling.enclosure(&around).unwrap(), Enclosure::Balanced);
        // The source at `−1` alone.
        let source_only = square(integer(-1), Rat::zero(), rat(1, 2));
        assert_eq!(rankine.loop_windings(&source_only).unwrap(), vec![1, 0]);
        assert_eq!(
            rankine.enclosure(&source_only).unwrap(),
            Enclosure::Emitting {
                enclosed_emission: integer(3)
            }
        );
        // Traversed clockwise, the loop winds `−1` about both.
        let mut clockwise = around.clone();
        clockwise.reverse();
        assert_eq!(rankine.loop_windings(&clockwise).unwrap(), vec![-1, -1]);
        // A loop through a singularity has no lift.
        let through = square(Rat::zero(), Rat::zero(), integer(1));
        assert!(rankine.loop_windings(&through).is_err());
    }

    /// Lean `closed_streamline_net_zero` (contrapositive): a net emission admits no closed dividing
    /// streamline around every singularity: `ψ` returns changed by the net strength.
    #[test]
    fn a_net_emission_has_no_closed_dividing_streamline() {
        let emitting = body(&[(3, 0), (-1, 0), (2, 5)]);
        let around = square(Rat::zero(), Rat::zero(), integer(4));
        assert_eq!(emitting.loop_windings(&around).unwrap(), vec![1, 1, 1]);
        assert_eq!(
            emitting.enclosure(&around).unwrap(),
            Enclosure::Emitting {
                enclosed_emission: emitting.net_strength()
            }
        );
        assert_eq!(emitting.net_strength(), integer(4));
        // A loop around nothing imposes nothing.
        let away = square(integer(10), integer(10), integer(1));
        assert_eq!(emitting.enclosure(&away).unwrap(), Enclosure::Balanced);
    }

    /// Refusals: a half-body needs a positive stream and a positive source.
    #[test]
    fn a_half_body_refuses_a_nonpositive_stream_or_source() {
        assert_eq!(
            HalfBody::new(Rat::zero(), integer(1)),
            Err(FluidError::NotPositive {
                what: "a half-body's stream"
            })
        );
        assert_eq!(
            HalfBody::new(integer(1), integer(-2)),
            Err(FluidError::NotPositive {
                what: "a half-body's source strength"
            })
        );
    }

    /// Lean `halfBody_reaches`, `halfBody_width`: the half-body's dividing streamline passes the
    /// octant points at heights `m/(8U)`, `m/(4U)`, `3m/(8U)`, all below the half-width `m/(2U)`,
    /// rising downstream toward it; the tube of width `m/U` carries the flux `m`.
    #[test]
    fn a_net_emission_opens_the_body_into_a_tube() {
        let half = HalfBody::new(integer(2), integer(3)).unwrap();
        let mut heights = Vec::new();
        for turns in [rat(3, 8), rat(1, 4), rat(1, 8)] {
            let point = half.dividing_point(&turns).unwrap();
            assert_eq!(
                half.stream_function(&point, &turns).unwrap(),
                half.dividing_value()
            );
            assert!(point.im < half.half_width());
            heights.push(point.im);
        }
        assert_eq!(heights, vec![rat(3, 16), rat(3, 8), rat(9, 16)]);
        assert_eq!(half.half_width(), rat(3, 4));
        assert_eq!(half.carried_flux(), integer(3));
        assert!(half.dividing_point(&rat(1, 6)).is_err());
        assert!(
            half.stream_function(&g(1, 1), &rat(1, 4)).is_err(),
            "a point off its declared direction is refused"
        );
    }

    /// Lean `streamline_membrane_net_zero`, `block_bounds`: on the joined cubes a current carried
    /// only by the shared face is a source–sink pair inside a streamline membrane, and encloses zero
    /// net divergence; each cell alone reads its own nonzero divergence.
    #[test]
    fn a_streamline_membrane_encloses_zero_net_divergence() {
        let reflection = reflect_across_face(3, 0, true).unwrap();
        let holarchy = reflection.join().unwrap();
        let faces = reflection.glued.cells(2).len();
        let mut current = vec![Rat::zero(); faces];
        current[reflection.shared_face] = integer(4);
        let reading = gauss(&holarchy, &current).unwrap();
        assert!(reading.streamline);
        assert!(reading.membrane_flux.is_zero());
        assert!(reading.enclosed_divergence.is_zero());
        let split = holarchy.flux(&current).unwrap();
        assert!(!split.left.is_zero());
        assert_eq!(split.left, -split.right);
    }

    /// Lean `tube_encloses_emission`: a current through the tube's two end faces with none through
    /// its lateral faces encloses emission equal to the flux through the open ends.
    #[test]
    fn a_tube_encloses_emission_leaving_through_its_ends() {
        let reflection = reflect_across_face(3, 0, true).unwrap();
        let holarchy = reflection.join().unwrap();
        let faces = reflection.glued.cells(2);
        let ends = [
            GridCell::new(crate::geometry::RatVec3::from_i64(0, 0, 0), vec![1, 2]).unwrap(),
            GridCell::new(crate::geometry::RatVec3::from_i64(2, 0, 0), vec![1, 2]).unwrap(),
        ];
        let membrane = reflection
            .glued
            .complex()
            .boundary(3)
            .unwrap()
            .apply(&holarchy.whole_interior().unwrap())
            .unwrap();
        // Emission leaves through both ends: the current points outward on each end face.
        let current: Vec<Rat> = faces
            .iter()
            .zip(&membrane)
            .map(|(face, outward)| {
                if ends.contains(face) {
                    outward.clone()
                } else {
                    Rat::zero()
                }
            })
            .collect();
        let reading = gauss(&holarchy, &current).unwrap();
        assert!(!reading.streamline);
        assert_eq!(reading.membrane_flux, reading.enclosed_divergence);
        assert_eq!(reading.enclosed_divergence, integer(2));
    }
}
