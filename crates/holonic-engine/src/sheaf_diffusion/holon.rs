//! **Sheaf diffusion as a core Holon, and its event law as a `HolonLaw`.**
//!
//! [proved-derived; implemented-exact] The sheaf law is the diffusion Holon of
//! `crate::diffusion` on the stalk coordinates of the selected grade `k`
//! (`Holon/Conformance.lean::diffusion_dissipates`): storage `diag(1/c)`, one external port per
//! coordinate, and resistive ports on the drop map `J = [δ_k ; δ_{k−1}ᵀ]` with unit resistance, so
//! that `Jᵀ J = δ_kᵀ δ_k + δ_{k−1} δ_{k−1}ᵀ = Δ_k`, the full cellular-sheaf Hodge operator the law
//! solves with. Its event `(M + τΔ_k) φ⁺ = n + s` is the backward-Euler word at step `τ` under the
//! external effort `u = s/τ` (`Holon/Element.lean::backwardEuler_balance`), and its
//! [`crate::diffusion::DiffusionEnergyBalance`] is the core balance with identical numbers
//! (conduction `τ⟨φ⁺, Δ_k φ⁺⟩ = τ|J φ⁺|²`).
//!
//! [definition; agent-inferred] As for the scalar law, [`SheafDiffusionHolonLaw`] carries the
//! declared interval; its `advance` enacts this law's own certified event, and a joined law
//! advances through the core [`ReferenceHolon`].

use relational_geometry::Rat;

use holonics::holon::{Holon, HolonError, HolonState};
use holonics::law::{Advance, HolonLaw, ReferenceHolon, Scheme};
use num_traits::Signed;

use super::{
    ExactRatMatrix, ExactSheafCochain, ExactSheafDiffusionLaw, SheafDiffusionError,
    SheafDiffusionEvent,
};
use crate::diffusion::{diffusion_holon, event_bond};

impl ExactSheafDiffusionLaw {
    /// The drop map `J = [δ_k ; δ_{k−1}ᵀ]` over this grade's coordinates.
    fn drop_map(&self) -> Result<ExactRatMatrix, SheafDiffusionError> {
        let upper = self.sheaf.coboundary(self.grade)?;
        if self.grade == 0 {
            return Ok(upper);
        }
        let lower = self.sheaf.coboundary(self.grade - 1)?.transpose()?;
        let mut rows = upper.to_rows();
        rows.extend(lower.to_rows());
        Ok(ExactRatMatrix::shaped(
            upper.rows() + lower.rows(),
            upper.columns(),
            rows,
        )?)
    }

    /// **This sheaf law as a core Holon** (see the module header), on the coordinates of
    /// [`super::ExactCellularSheaf::coordinates`] at the law's grade.
    pub fn holon(&self) -> Result<Holon, SheafDiffusionError> {
        let slip = self.drop_map()?;
        let resistance = ExactRatMatrix::identity(slip.rows())?;
        Ok(diffusion_holon(
            &self.flattened_capacities(),
            &slip,
            resistance,
        )?)
    }

    /// **This law as a `HolonLaw` at a declared interval**: its words are this law's own events.
    pub fn holon_law(&self, interval: Rat) -> Result<SheafDiffusionHolonLaw, SheafDiffusionError> {
        if !interval.is_positive() {
            return Err(SheafDiffusionError::Law(
                crate::SheafDiffusionRefusal::NonpositiveInterval,
            ));
        }
        Ok(SheafDiffusionHolonLaw {
            reference: ReferenceHolon::new(self.holon()?, interval, Scheme::BackwardEuler)?,
            solver: Some((self.clone(), self.drop_map()?)),
        })
    }
}

/// **Exact sheaf diffusion as a core `HolonLaw`** at one declared interval.
#[derive(Clone, Debug)]
pub struct SheafDiffusionHolonLaw {
    reference: ReferenceHolon,
    solver: Option<(ExactSheafDiffusionLaw, ExactRatMatrix)>,
}

impl SheafDiffusionHolonLaw {
    /// The core reference law on the same Holon (backward Euler at the declared interval).
    pub fn reference(&self) -> &ReferenceHolon {
        &self.reference
    }

    /// Whether `advance` runs the sheaf law's own event (a single sheaf) or the reference.
    pub fn is_sheaf_event(&self) -> bool {
        self.solver.is_some()
    }
}

fn refused(_: SheafDiffusionError) -> HolonError {
    HolonError::Unsupported {
        what: "an exact sheaf diffusion event",
        reason: "the sheaf diffusion law refused the event; enact it directly for its own refusal",
    }
}

impl HolonLaw for SheafDiffusionHolonLaw {
    fn holon(&self) -> &Holon {
        self.reference.holon()
    }

    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError> {
        let Some((law, slip)) = &self.solver else {
            return self.reference.advance(state, input);
        };
        let interval = self.reference.step();
        let content =
            ExactSheafCochain::from_flattened(&law.sheaf, law.grade, state.configuration.clone())
                .map_err(refused)?;
        let source = ExactSheafCochain::from_flattened(
            &law.sheaf,
            law.grade,
            input.iter().map(|effort| effort * interval).collect(),
        )
        .map_err(refused)?;
        let event = SheafDiffusionEvent {
            interval: interval.clone(),
            source: source.values,
        };
        let standing = law.initial_standing(content).map_err(refused)?;
        let (after, receipt) = law.enact(&standing, &event).map_err(refused)?;
        let configuration = after.content.flattened(&law.sheaf).map_err(refused)?;
        let potential = receipt
            .potential_after
            .flattened(&law.sheaf)
            .map_err(refused)?;
        let bond = event_bond(
            self.holon(),
            &state.configuration,
            &configuration,
            &potential,
            input,
            slip,
            interval,
        )?;
        let balance = law
            .energy_balance(&receipt, &event)
            .map_err(refused)?
            .energy_balance();
        Ok(Advance {
            state: HolonState {
                configuration,
                commit: state.commit + 1,
            },
            bond,
            balance,
        })
    }

    fn interact(&self, other: &Self, joined: &[(usize, usize)]) -> Result<Self, HolonError> {
        Ok(Self {
            reference: self.reference.interact(&other.reference, joined)?,
            solver: None,
        })
    }
}

impl From<HolonError> for SheafDiffusionError {
    fn from(error: HolonError) -> Self {
        Self::Law(crate::SheafDiffusionRefusal::Holon(Box::new(error)))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use holonics::conformance::{
        check_exact_advance, check_interaction, check_restriction, check_run, check_tellegen,
    };
    use holonics::restriction::PortMap;
    use relational_geometry::integer;

    use super::*;
    use crate::{
        CausalCellId, CausalChain, CellularRestriction, ComparativeMultiplicity, EventId,
        ExactCellularSheaf, GradedCausalComplex,
    };

    /// The existing `rank_one_interval_reproduces_exact_scalar_diffusion` witness: two vertices,
    /// one edge, constant rank-one sheaf.
    fn interval_sheaf() -> (ExactCellularSheaf, CausalCellId, CausalCellId, CausalCellId) {
        let mut complex = GradedCausalComplex::default();
        let events = BTreeSet::from([EventId(1)]);
        let left = complex
            .found_cell("left", events.clone(), 0, CausalChain::default())
            .unwrap();
        let right = complex
            .found_cell("right", events.clone(), 0, CausalChain::default())
            .unwrap();
        let mut boundary = CausalChain::default();
        boundary.add_term(left, ComparativeMultiplicity::negative(1_u8));
        boundary.add_term(right, ComparativeMultiplicity::positive(1_u8));
        let edge = complex.found_cell("edge", events, 1, boundary).unwrap();
        let dimensions = complex
            .cells()
            .keys()
            .map(|cell| (*cell, 1_usize))
            .collect();
        let sheaf = ExactCellularSheaf::new(
            complex,
            dimensions,
            [
                CellularRestriction {
                    lower: left,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
            ],
        )
        .unwrap();
        (sheaf, left, right, edge)
    }

    #[test]
    fn the_sheaf_event_is_the_backward_euler_word_of_its_holon_at_both_grades() {
        let (sheaf, left, right, edge) = interval_sheaf();
        let vertex_law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            0,
            BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(1)])]),
        )
        .unwrap();
        let holon_law = vertex_law.holon_law(integer(1)).unwrap();
        assert!(holon_law.is_sheaf_event());
        let state = HolonState::new(vec![integer(1), integer(0)]);
        let input = vec![integer(0), integer(0)];
        let advance = check_exact_advance(&holon_law, &state, &input).unwrap();
        assert_eq!(
            advance,
            holon_law.reference().advance(&state, &input).unwrap()
        );
        // The existing witness numbers, through the core balance.
        assert_eq!(
            advance.state.configuration,
            vec![integer(2) / integer(3), integer(1) / integer(3)]
        );
        assert_eq!(advance.balance.dissipated, integer(1) / integer(9));
        assert_eq!(
            advance.balance.discretization_defect,
            -integer(1) / integer(9)
        );
        assert_eq!(advance.balance.port, integer(0));

        // The old computation against the core balance, with a supplied source.
        let supplied = vec![integer(1), integer(0)];
        let advance = check_exact_advance(&holon_law, &state, &supplied).unwrap();
        let event = SheafDiffusionEvent {
            interval: integer(1),
            source: BTreeMap::from([(left, vec![integer(1)])]),
        };
        let standing = vertex_law
            .initial_standing(
                ExactSheafCochain::new(
                    &sheaf,
                    0,
                    BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(0)])]),
                )
                .unwrap(),
            )
            .unwrap();
        let (_, receipt) = vertex_law.enact(&standing, &event).unwrap();
        let old = vertex_law.energy_balance(&receipt, &event).unwrap();
        assert_eq!(old.energy_balance(), advance.balance);
        assert_eq!(
            advance.balance.stored_change,
            &receipt.stored_energy_after - &receipt.stored_energy_before
        );

        // Grade one: the edge stalk, whose drop map is the lower coboundary transposed.
        let edge_law =
            ExactSheafDiffusionLaw::new(sheaf, 1, BTreeMap::from([(edge, vec![integer(2)])]))
                .unwrap();
        let edge_holon = edge_law.holon_law(integer(1) / integer(3)).unwrap();
        let state = HolonState::new(vec![integer(3)]);
        let advance = check_exact_advance(&edge_holon, &state, &[integer(1)]).unwrap();
        assert_eq!(
            advance,
            edge_holon
                .reference()
                .advance(&state, &[integer(1)])
                .unwrap()
        );
    }

    #[test]
    fn exact_sheaf_diffusion_passes_the_core_conformance_checks() {
        let (sheaf, left, right, _) = interval_sheaf();
        let law = ExactSheafDiffusionLaw::new(
            sheaf,
            0,
            BTreeMap::from([(left, vec![integer(2)]), (right, vec![integer(3)])]),
        )
        .unwrap();
        let holon_law = law.holon_law(integer(1) / integer(2)).unwrap();
        check_tellegen(holon_law.holon().port_holon().dirac()).unwrap();
        let (_, total) = check_run(
            &holon_law,
            &HolonState::new(vec![integer(5), integer(-1)]),
            &[integer(1), integer(0)],
            3,
        )
        .unwrap();
        assert!(total.is_exact());
        let (joined, _) = check_interaction(
            &holon_law,
            &holon_law,
            &[(1, 0)],
            &[integer(1), integer(2)],
            &[integer(3), integer(4)],
            &[integer(1), integer(-1)],
        )
        .unwrap();
        assert!(!joined.is_sheaf_event());
        let ports = holon_law.holon().port_holon().counts().total();
        let map = PortMap::new(ExactRatMatrix::identity(ports).unwrap());
        let flow: Vec<Rat> = (0..ports as i64).map(integer).collect();
        check_restriction(&holon_law, &map, &flow, &flow).unwrap();
    }
}
