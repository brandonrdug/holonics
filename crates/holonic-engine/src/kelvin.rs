//! The material loop, and the circulation it carries.
//!
//! ## What this adds to the advection law that already exists
//!
//! `analytic_field::ExactAnalyticAdvectionLaw` already refuses construction unless its generator is
//! capacity-skew **and divergence-free** — incompressibility as a typed refusal rather than a
//! diagnostic — and it certifies declared circulation covectors. But its probes are **fixed
//! covectors on a fixed complex**, and they are admitted only when they are **left eigenvectors of
//! the successor**: `NoninvariantCirculationProbe` refuses every loop that is not.
//!
//! Kelvin's circulation theorem is not about a fixed loop. It is about a loop that **moves with the
//! flow**:
//!
//! ```text
//!   Gamma(t) = closed integral of v . dl  around a MATERIAL loop C(t),
//!   and dGamma/dt = 0 for the conservative current.
//! ```
//!
//! So the restriction to left-fixed loops is not the theorem — it is the special case in which the
//! material loop happens not to move. This module carries the loop.
//!
//! ## The tautology this had to avoid, stated because it is the whole design problem
//!
//! With the field carried as `v(t+1) = U v(t)`, the covector transport that preserves the pairing is
//! forced: `c(t+1) = (Uᵀ)⁻¹ c(t)` gives `<c(t+1), v(t+1)> = <c(t), v(t)>` **identically, by
//! associativity**. An organ that computed only this would be `CLAUDE.md` §8's receipt that could not
//! have come out otherwise.
//!
//! The content is therefore **not** that the circulation is conserved. It is:
//!
//! 1. **The carried loop is still a loop.** Closedness — `∂ᵀc = 0` at every junction — is *not*
//!    preserved automatically by `(Uᵀ)⁻¹`. It is re-checked after every step and refused by name
//!    when it breaks. In the continuum this is the statement that a material loop stays closed
//!    because a flow carries it; here it is a property of the successor that can fail.
//! 2. **The loop actually moved.** A step that returns the same coefficients is the fixed-probe case
//!    wearing a new name, and `MaterialCirculationReceipt::loop_moved` reports it so a control can
//!    require otherwise.
//! 3. **A loop the existing machinery must refuse is admitted here.** A covector that is not a left
//!    eigenvector of `U` has no conserved circulation when held fixed — and carrying it materially
//!    conserves it exactly. That difference is the movement, and the declared control exhibits both
//!    halves on one loop.
//!
//! ## What this does not claim
//!
//! Not Navier–Stokes, not existence or smoothness, not viscosity, not a fluid solver. The cpu
//! module's own bound stands unsoftened: *"an exact finite conservative advection law, not a
//! relabelling of diffusion or a claim to complete Navier–Stokes."* A complete exact-rational fluid
//! body existed in the laboratory and Brandon ruled on 2026-08-08 that such partials be **lifted and
//! superseded, never restored**; this is the lift of its one load-bearing idea — that the invariant
//! the flow syncs on is the circulation, not the trajectory.

use std::collections::BTreeMap;

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::analytic_field::{
    AnalyticFieldArcId, AnalyticFieldJunctionId, ExactAnalyticAdvectionLaw,
    ExactAnalyticAdvectionStanding,
};

/// The only thing a material loop needs from a field: which junctions each arc runs between.
///
/// Taking the endpoints rather than the whole wave law keeps this module independent of every
/// geometric face an arc also carries — orbit geometry, start phase, phase transport — none of
/// which a closure check consults. It also lets the declared controls found a loop without building
/// a wave, which is what makes them small enough to read.
pub type ArcIncidence =
    BTreeMap<AnalyticFieldArcId, (AnalyticFieldJunctionId, AnalyticFieldJunctionId)>;
use crate::exact_linear::ExactLinearError;

/// A closed covector on the arcs, carried by the flow rather than held fixed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaterialLoop {
    pub name: String,
    coefficients: BTreeMap<AnalyticFieldArcId, Rat>,
    /// How many times this loop has been carried. Zero is the founded loop.
    pub carried_steps: u64,
}

impl MaterialLoop {
    /// Found a material loop, refusing anything that is not closed.
    ///
    /// Closedness is `∂ᵀc = 0`: summing the coefficient out of each arc's tail and into its head
    /// must vanish at every junction. This is the same predicate the advection law applies to its
    /// fixed probes, applied here to the founded loop and again after every step.
    pub fn found(
        arcs: &ArcIncidence,
        name: impl Into<String>,
        coefficients: BTreeMap<AnalyticFieldArcId, Rat>,
    ) -> Result<Self, KelvinError> {
        if coefficients.is_empty() {
            return Err(KelvinError::EmptyLoop);
        }
        verify_closed(arcs, &coefficients)?;
        Ok(Self {
            name: name.into(),
            coefficients,
            carried_steps: 0,
        })
    }

    pub fn coefficients(&self) -> &BTreeMap<AnalyticFieldArcId, Rat> {
        &self.coefficients
    }

    /// `Γ = ⟨c, v⟩` — the circulation this loop reads from a standing field, exactly.
    pub fn circulation(&self, standing: &ExactAnalyticAdvectionStanding) -> Rat {
        self.coefficients
            .iter()
            .map(|(arc, coefficient)| {
                let value = standing.values.get(arc).cloned().unwrap_or_else(Rat::zero);
                coefficient.clone() * value
            })
            .sum()
    }

    /// Carry the loop one step: `c(t+1) = (Uᵀ)⁻¹ c(t)`, then **re-check closedness**.
    ///
    /// The transport is forced by the requirement that the pairing be preserved. What is not forced,
    /// and is checked here, is that the result is still a closed loop.
    ///
    /// **And there is a reason it usually is, which is the structure worth naming.** A covector is
    /// closed exactly when its coefficients sum to zero across each junction's incident arcs; the
    /// carried sum is `1ᵀ(Uᵀ)⁻¹c = ((U⁻¹)1)ᵀc`, and the advection law's own certificate is
    /// `U·1 = 1`, hence `U⁻¹·1 = 1`, hence the sum is unchanged. **The material loop stays closed
    /// because the flow is incompressible.** That is Kelvin's structure exactly, and it is why the
    /// divergence-free gate upstream is load-bearing here rather than decorative. The check remains
    /// because it is a property of a *particular* successor, and a successor that failed it would be
    /// one this module must refuse rather than silently read.
    pub fn carried(
        &self,
        arcs: &ArcIncidence,
        law: &ExactAnalyticAdvectionLaw,
    ) -> Result<Self, KelvinError> {
        let order = law.arc_order();
        let inverse_transpose = law
            .successor()
            .transpose()
            .and_then(|transposed| transposed.inverse())
            .map_err(KelvinError::Linear)?;
        let vector = order
            .iter()
            .map(|arc| {
                self.coefficients
                    .get(arc)
                    .cloned()
                    .unwrap_or_else(Rat::zero)
            })
            .collect::<Vec<_>>();
        let carried = inverse_transpose
            .apply(&vector)
            .map_err(KelvinError::Linear)?;
        let mut coefficients = BTreeMap::new();
        for (arc, value) in order.iter().zip(carried) {
            if !value.is_zero() {
                coefficients.insert(*arc, value);
            }
        }
        if coefficients.is_empty() {
            return Err(KelvinError::LoopCollapsed(self.name.clone()));
        }
        verify_closed(arcs, &coefficients).map_err(|_| KelvinError::CarriedLoopNotClosed {
            name: self.name.clone(),
            step: self.carried_steps + 1,
        })?;
        Ok(Self {
            name: self.name.clone(),
            coefficients,
            carried_steps: self.carried_steps + 1,
        })
    }
}

/// One step of a material loop against a transported field.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaterialCirculationReceipt {
    pub name: String,
    pub step: u64,
    /// `Γ` before the step, read by the loop at its old position from the old field.
    pub before: Rat,
    /// `Γ` after, read by the carried loop from the carried field.
    pub after: Rat,
    /// `after - before`. Exactly zero for the conservative current.
    pub residual: Rat,
    /// **False makes the step vacuous** — the loop did not move, so this is the fixed-probe case.
    pub loop_moved: bool,
    /// False would make the reading vacuous the other way: the field did not move either.
    pub field_moved: bool,
}

impl MaterialCirculationReceipt {
    pub fn conserved(&self) -> bool {
        self.residual.is_zero()
    }
}

/// Read one loop against one field transport, returning the receipt.
///
/// `after_standing` must be the transport of `before_standing` under `law`; this function does not
/// perform the field step, because the caller owns the event that drives it.
pub fn read_material_step(
    arcs: &ArcIncidence,
    law: &ExactAnalyticAdvectionLaw,
    material: &MaterialLoop,
    before_standing: &ExactAnalyticAdvectionStanding,
    after_standing: &ExactAnalyticAdvectionStanding,
) -> Result<(MaterialLoop, MaterialCirculationReceipt), KelvinError> {
    let before = material.circulation(before_standing);
    let carried = material.carried(arcs, law)?;
    let after = carried.circulation(after_standing);
    let receipt = MaterialCirculationReceipt {
        name: material.name.clone(),
        step: carried.carried_steps,
        residual: after.clone() - before.clone(),
        before,
        after,
        loop_moved: carried.coefficients != material.coefficients,
        field_moved: after_standing.values != before_standing.values,
    };
    Ok((carried, receipt))
}

/// `Γ` read by a loop held **fixed** while the field is carried — the existing probe's behaviour,
/// exposed so a control can exhibit the difference.
///
/// For a loop that is not a left eigenvector of the successor this is **not** conserved, and that is
/// the point: the advection law refuses such probes rather than reading them.
pub fn read_fixed_step(
    material: &MaterialLoop,
    before_standing: &ExactAnalyticAdvectionStanding,
    after_standing: &ExactAnalyticAdvectionStanding,
) -> MaterialCirculationReceipt {
    let before = material.circulation(before_standing);
    let after = material.circulation(after_standing);
    MaterialCirculationReceipt {
        name: material.name.clone(),
        step: material.carried_steps,
        residual: after.clone() - before.clone(),
        before,
        after,
        loop_moved: false,
        field_moved: after_standing.values != before_standing.values,
    }
}

fn verify_closed(
    arcs: &ArcIncidence,
    coefficients: &BTreeMap<AnalyticFieldArcId, Rat>,
) -> Result<(), KelvinError> {
    let mut boundary = BTreeMap::<AnalyticFieldJunctionId, Rat>::new();
    for (arc_id, coefficient) in coefficients {
        let (from, to) = arcs
            .get(arc_id)
            .ok_or(KelvinError::ArcOutsideField(*arc_id))?;
        *boundary.entry(*from).or_default() -= coefficient;
        *boundary.entry(*to).or_default() += coefficient;
    }
    if boundary.values().any(|residual| !residual.is_zero()) {
        return Err(KelvinError::LoopNotClosed);
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum KelvinError {
    #[error("a material loop must carry at least one arc")]
    EmptyLoop,
    #[error("the founded loop is not closed: its boundary does not vanish at every junction")]
    LoopNotClosed,
    #[error("arc {0:?} is not in the declared field")]
    ArcOutsideField(AnalyticFieldArcId),
    #[error("carrying loop {name} broke its closure at step {step}")]
    CarriedLoopNotClosed { name: String, step: u64 },
    #[error("carrying loop {0} collapsed it to no arcs")]
    LoopCollapsed(String),
    #[error(transparent)]
    Linear(ExactLinearError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EventId;
    use crate::analytic_field::ExactAnalyticAdvectionLaw;
    use crate::exact_linear::ExactRatMatrix;
    use num_bigint::BigInt;
    use std::collections::BTreeSet;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn arc(index: u64) -> AnalyticFieldArcId {
        AnalyticFieldArcId(index)
    }

    /// A theta graph: three parallel arcs from junction 0 to junction 1.
    ///
    /// Chosen because its cycle space is **two**-dimensional — `{c : c₀+c₁+c₂ = 0}` — so there are
    /// closed loops that are not the trivial all-ones covector. On a simple cycle the cycle space is
    /// one-dimensional and every closed loop is left-fixed, which would make the whole movement
    /// vacuous.
    fn theta_incidence() -> ArcIncidence {
        let j0 = AnalyticFieldJunctionId(0);
        let j1 = AnalyticFieldJunctionId(1);
        [(arc(0), (j0, j1)), (arc(1), (j0, j1)), (arc(2), (j0, j1))]
            .into_iter()
            .collect()
    }

    /// Capacity-skew and divergence-free by construction, with **unequal** capacities.
    ///
    /// The inequality is load-bearing and the first draft of this fixture got it wrong. With equal
    /// capacities `Ω = I`, the successor is **orthogonal** — `UᵀU = I` — so `(Uᵀ)⁻¹ = U` and the
    /// material transport coincides with the naive one. Every test below would still have passed
    /// and the falsifier would have been vacuous, because the declared material could not separate
    /// the property under test. `CLAUDE.md` §8: *a gauge whose group acts trivially on the declared
    /// material is not a gauge.*
    ///
    /// With `Ω = diag(1, 2, 3)` the successor is Ω-orthogonal instead — `UᵀΩU = Ω`, so
    /// `(Uᵀ)⁻¹ = ΩUΩ⁻¹` — and the two transports genuinely differ.
    ///
    /// Capacity-skew requires `ωᵢAᵢⱼ = −ωⱼAⱼᵢ`; zero row sums give divergence-freedom. Solving both
    /// with `A₁₂ = 1` forces the entries below, and the third row's sum vanishes identically rather
    /// than by choice.
    fn conservative_law() -> ExactAnalyticAdvectionLaw {
        let capacities: BTreeMap<AnalyticFieldArcId, Rat> = [
            (arc(0), Rat::from_integer(1.into())),
            (arc(1), Rat::from_integer(2.into())),
            (arc(2), Rat::from_integer(3.into())),
        ]
        .into_iter()
        .collect();
        let generator = ExactRatMatrix::new(vec![
            vec![Rat::from_integer(0.into()), rat(1, 1), rat(-1, 1)],
            vec![rat(-1, 2), Rat::from_integer(0.into()), rat(1, 2)],
            vec![rat(1, 3), rat(-1, 3), Rat::from_integer(0.into())],
        ])
        .unwrap();
        ExactAnalyticAdvectionLaw::new(capacities, generator, Rat::from_integer(1.into()), vec![])
            .expect("capacity-skew with zero row sums passes both gates")
    }

    /// The equal-capacity law, kept **only** to exhibit why the fixture above uses unequal ones.
    fn orthogonal_law() -> ExactAnalyticAdvectionLaw {
        let capacities: BTreeMap<AnalyticFieldArcId, Rat> = [
            (arc(0), Rat::from_integer(1.into())),
            (arc(1), Rat::from_integer(1.into())),
            (arc(2), Rat::from_integer(1.into())),
        ]
        .into_iter()
        .collect();
        let generator = ExactRatMatrix::new(vec![
            vec![Rat::from_integer(0.into()), rat(1, 1), rat(-1, 1)],
            vec![rat(-1, 1), Rat::from_integer(0.into()), rat(1, 1)],
            vec![rat(1, 1), rat(-1, 1), Rat::from_integer(0.into())],
        ])
        .unwrap();
        ExactAnalyticAdvectionLaw::new(capacities, generator, Rat::from_integer(1.into()), vec![])
            .expect("antisymmetric with zero row sums passes both gates")
    }

    /// **Why the fixture's capacities are unequal**, exhibited rather than asserted in a comment.
    ///
    /// On equal capacities the successor is orthogonal and the two transports coincide, so the
    /// falsifier below cannot fail. On unequal ones they differ. The material decides whether the
    /// check has content, which is the whole of §8's gauge rule.
    #[test]
    fn equal_capacities_collapse_the_two_transports_and_unequal_ones_separate_them() {
        let ones = vec![Rat::from_integer(1.into()); 3];

        let orthogonal = orthogonal_law();
        let u = orthogonal.successor();
        let inverse_transpose = u.transpose().unwrap().inverse().unwrap();
        assert_eq!(
            &inverse_transpose, u,
            "equal capacities make U orthogonal, so the material transport IS the naive one \
             and any falsifier built on their difference would be vacuous"
        );
        assert_eq!(u.apply(&ones).unwrap(), ones);

        let weighted = conservative_law();
        let w = weighted.successor();
        let weighted_inverse_transpose = w.transpose().unwrap().inverse().unwrap();
        assert_ne!(
            &weighted_inverse_transpose, w,
            "unequal capacities separate the transports, which is what gives the falsifier content"
        );
        assert_eq!(
            w.apply(&ones).unwrap(),
            ones,
            "and the divergence-free certificate still holds"
        );
    }

    fn standing(
        law: &ExactAnalyticAdvectionLaw,
        values: [i64; 3],
    ) -> ExactAnalyticAdvectionStanding {
        law.initial_standing(
            [
                (arc(0), Rat::from_integer(values[0].into())),
                (arc(1), Rat::from_integer(values[1].into())),
                (arc(2), Rat::from_integer(values[2].into())),
            ]
            .into_iter()
            .collect(),
        )
        .expect("the population matches the law's arcs")
    }

    fn step(
        law: &ExactAnalyticAdvectionLaw,
        before: &ExactAnalyticAdvectionStanding,
        event: u64,
    ) -> ExactAnalyticAdvectionStanding {
        use crate::ExactEventLaw;
        law.enact(
            before,
            &crate::analytic_field::ExactAnalyticAdvectionEvent {
                event: EventId(event),
            },
        )
        .expect("the conservative successor enacts")
        .standing_after
    }

    #[test]
    fn a_loop_whose_boundary_does_not_vanish_is_refused_by_name() {
        let arcs = theta_incidence();
        let open_chain = [(arc(0), Rat::from_integer(1.into()))]
            .into_iter()
            .collect();
        assert_eq!(
            MaterialLoop::found(&arcs, "open", open_chain),
            Err(KelvinError::LoopNotClosed)
        );
        assert_eq!(
            MaterialLoop::found(&arcs, "empty", BTreeMap::new()),
            Err(KelvinError::EmptyLoop)
        );
    }

    /// **The movement, in one test.** A closed loop that the existing fixed-probe machinery must
    /// refuse — because it is not a left eigenvector of the successor — has its circulation
    /// conserved **exactly** when it is carried materially, and **not** conserved when held fixed.
    #[test]
    fn a_loop_the_fixed_probe_must_refuse_conserves_its_circulation_when_carried() {
        let arcs = theta_incidence();
        let law = conservative_law();

        // c = (1, -1, 0): closed, and NOT in the kernel of the generator, so `Uᵀc != c`.
        let material = MaterialLoop::found(
            &arcs,
            "theta",
            [
                (arc(0), Rat::from_integer(1.into())),
                (arc(1), Rat::from_integer((-1).into())),
            ]
            .into_iter()
            .collect(),
        )
        .expect("sum zero is closed on a theta graph");

        let before = standing(&law, [5, 2, -1]);
        let after = step(&law, &before, 1);

        // Held fixed, the circulation MOVES. This is the case the advection law refuses outright
        // with `NoninvariantCirculationProbe` rather than reading.
        let held = read_fixed_step(&material, &before, &after);
        assert!(held.field_moved, "the successor moved the field");
        assert!(
            !held.conserved(),
            "a loop that is not left-fixed has no conserved circulation when held still; \
             residual was {}",
            held.residual
        );

        // Carried, it is conserved EXACTLY, and the loop genuinely moved.
        let (carried, receipt) = read_material_step(&arcs, &law, &material, &before, &after)
            .expect("the carried loop stays closed");
        assert!(
            receipt.loop_moved,
            "if the loop did not move this is the fixed-probe case wearing a new name"
        );
        assert!(receipt.field_moved);
        assert!(
            receipt.conserved(),
            "Kelvin: the circulation of a material loop is conserved; residual was {}",
            receipt.residual
        );
        assert_eq!(receipt.before, held.before);
        assert_ne!(
            receipt.after, held.after,
            "the two readings differ precisely because one loop moved and the other did not"
        );
        assert_eq!(carried.carried_steps, 1);
    }

    /// The carried loop stays **closed**, and it stays closed because the flow is incompressible:
    /// `U·1 = 1` is the advection law's own certificate, so the carried coefficients sum as before.
    #[test]
    fn the_carried_loop_stays_closed_because_the_successor_preserves_the_ones_vector() {
        let arcs = theta_incidence();
        let law = conservative_law();
        let ones = vec![Rat::from_integer(1.into()); 3];
        assert_eq!(
            law.successor().apply(&ones).unwrap(),
            ones,
            "the divergence-free certificate: U fixes the ones vector"
        );

        let mut material = MaterialLoop::found(
            &arcs,
            "theta",
            [
                (arc(0), Rat::from_integer(2.into())),
                (arc(1), Rat::from_integer((-3).into())),
                (arc(2), Rat::from_integer(1.into())),
            ]
            .into_iter()
            .collect(),
        )
        .unwrap();

        for _ in 0..6 {
            let sum: Rat = material.coefficients().values().cloned().sum();
            assert!(
                sum.is_zero(),
                "closedness on a theta graph is a vanishing sum"
            );
            material = material.carried(&arcs, &law).expect("stays closed");
        }
        assert_eq!(material.carried_steps, 6);
    }

    /// **Γ is bit-identical while the field and the loop both move, over many steps.**
    #[test]
    fn the_circulation_is_bit_identical_over_many_steps_while_everything_else_moves() {
        let arcs = theta_incidence();
        let law = conservative_law();
        let mut material = MaterialLoop::found(
            &arcs,
            "theta",
            [
                (arc(0), Rat::from_integer(1.into())),
                (arc(2), Rat::from_integer((-1).into())),
            ]
            .into_iter()
            .collect(),
        )
        .unwrap();

        let mut field = standing(&law, [7, -2, 3]);
        let founding_circulation = material.circulation(&field);
        let mut loop_positions = BTreeSet::new();
        let mut field_positions = BTreeSet::new();

        for tick in 1..=8u64 {
            let next = step(&law, &field, tick);
            let (carried, receipt) = read_material_step(&arcs, &law, &material, &field, &next)
                .expect("closed throughout");
            assert!(
                receipt.conserved(),
                "step {tick} moved the circulation by {}",
                receipt.residual
            );
            assert_eq!(
                receipt.after, founding_circulation,
                "Gamma is bit-identical to its founding value, not merely stationary"
            );
            loop_positions.insert(format!("{:?}", carried.coefficients()));
            field_positions.insert(format!("{:?}", next.values));
            material = carried;
            field = next;
        }

        // The non-vacuity condition: neither the loop nor the field stood still.
        assert!(
            loop_positions.len() > 1,
            "the loop occupied {} distinct positions -- a stationary loop proves nothing",
            loop_positions.len()
        );
        assert!(field_positions.len() > 1, "the field must move too");
    }

    /// **The falsifier.** Transport the loop by anything other than `(Uᵀ)⁻¹` and the circulation
    /// must move. Without this the conservation above could be an artifact of the pairing rather
    /// than a property of the transport.
    #[test]
    fn transporting_the_loop_the_wrong_way_breaks_the_conservation() {
        let arcs = theta_incidence();
        let law = conservative_law();
        let material = MaterialLoop::found(
            &arcs,
            "theta",
            [
                (arc(0), Rat::from_integer(1.into())),
                (arc(1), Rat::from_integer((-1).into())),
            ]
            .into_iter()
            .collect(),
        )
        .unwrap();

        let before = standing(&law, [5, 2, -1]);
        let after = step(&law, &before, 1);

        // Carry the loop by U instead of (U^T)^-1 -- a plausible-looking wrong transport.
        let order = law.arc_order();
        let vector = order
            .iter()
            .map(|a| {
                material
                    .coefficients()
                    .get(a)
                    .cloned()
                    .unwrap_or_else(Rat::zero)
            })
            .collect::<Vec<_>>();
        let wrong = law.successor().apply(&vector).unwrap();
        let wrong_after: Rat = order
            .iter()
            .zip(&wrong)
            .map(|(a, coefficient)| {
                coefficient.clone() * after.values.get(a).cloned().unwrap_or_else(Rat::zero)
            })
            .sum();

        let founding = material.circulation(&before);
        assert_ne!(
            wrong_after, founding,
            "the wrong transport must move Gamma, or the conservation is an artifact of the pairing"
        );

        // And the right one does not.
        let (_, receipt) =
            read_material_step(&arcs, &law, &material, &before, &after).expect("closed");
        assert!(receipt.conserved());
    }
}
