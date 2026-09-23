//! **Diffusion as a core Holon: the purely resistive medium, and its event law as a `HolonLaw`.**
//!
//! [proved-derived; implemented-exact] Diffusion is the medium with no skew part
//! (`Holon/Conformance.lean::diffusion_dissipates`). Its port Holon has storage ports on the node
//! contents `n` with form `C⁻¹` (so the storage effort is the potential `φ = n / c`), resistive
//! ports on the branches with `f_R = d φ` (the endpoint drop) and `R = diag(conductance)`, and one
//! external port per node with `f_P = φ` and `e_P = u`:
//!
//! ```text
//!   f_S = −dᵀ e_R − e_P,     f_R = d e_S,     f_P = e_S     ⇒     ṅ = −dᵀ W d φ + u.
//! ```
//!
//! The law's one completed event `C(φ⁺ − φ) = s − τ L φ⁺` is the backward-Euler word of this Holon
//! at step `τ` under the external effort `u = s/τ` (`Holon/Element.lean::backwardEuler_balance`):
//! its source work is `τ⟨u, f_P⟩ = ⟨s, φ⁺⟩`, its conduction `τ⟨dφ⁺, W dφ⁺⟩`, and its implicit step
//! defect is the core's `−½⟨Δn, C⁻¹ Δn⟩`. [`DiffusionEnergyBalance`] is therefore a view of
//! `holonic_core::law::EnergyBalance`, converted both ways with identical numbers.
//!
//! [definition; agent-inferred] [`HolonLaw`] needs a step and a borrowed [`Holon`], so the law is
//! [`DiffusionHolonLaw`], built by [`ExactDiffusionLaw::holon_law`] at a declared interval. Its
//! `advance` runs **this law's own Schur-certified event** and reads the step bond and the balance
//! from the receipt; two such laws joined at their node ports are a Holon that is no longer a
//! diffusion complex, and the joined law advances through the core [`ReferenceHolon`] instead.

use relational_geometry::Rat;

use holonic_core::dirac::DiracStructure;
use holonic_core::element::ResistiveRelation;
use holonic_core::holon::{Holon, HolonError, HolonState, PortCounts, PortHolon};
use holonic_core::inertia::SymmetricForm;
use holonic_core::law::{Advance, EnergyBalance, HolonLaw, ReferenceHolon, Scheme};
use holonic_core::port::Bond;
use num_traits::{One, Signed, Zero};

use super::{
    CurrentBranchId, CurrentNodeId, DiffusionComplex, DiffusionEnergyBalance, DiffusionError,
    DiffusionEvent, ExactDiffusionLaw, ExactRatMatrix,
};
use crate::algebraic::{CoreChartRefusal, GraphChart};

/// [definition] **A diffusion-shaped port Holon**: storage `diag(1/c)` on the coordinates, resistive
/// ports with the drop map `slip` (`f_R = slip · e_S`) and resistance `R`, and one external port per
/// coordinate (`f_P = e_S`). Shared by the scalar and the sheaf laws.
pub(crate) fn diffusion_holon(
    capacities: &[Rat],
    slip: &ExactRatMatrix,
    resistance: ExactRatMatrix,
) -> Result<Holon, HolonError> {
    let n = capacities.len();
    let b = slip.rows();
    if slip.columns() != n {
        return Err(HolonError::Shape {
            what: "diffusion drop map columns",
            expected: n,
            found: slip.columns(),
        });
    }
    let total = n + b + n;
    let mut rows = vec![vec![Rat::zero(); total]; total];
    for branch in 0..b {
        for node in 0..n {
            let value = slip.get(branch, node)?.clone();
            rows[node][n + branch] = -value.clone();
            rows[n + branch][node] = value;
        }
    }
    for node in 0..n {
        rows[node][n + b + node] = -Rat::one();
        rows[n + b + node][node] = Rat::one();
    }
    let structure = ExactRatMatrix::shaped(total, total, rows)?;
    let storage = SymmetricForm::from_diagonal(
        capacities
            .iter()
            .map(|capacity| Rat::one() / capacity)
            .collect(),
    );
    Holon::new(PortHolon::new(
        DiracStructure::skew_graph(&structure)?,
        PortCounts {
            storage: n,
            resistive: b,
            external: n,
            active: 0,
        },
        storage,
        ResistiveRelation::new(resistance)?,
    )?)
}

/// The backward-Euler step bond of a diffusion-shaped Holon read from a completed event:
/// `(−Δn/τ, φ⁺; slip φ⁺, −R slip φ⁺; φ⁺, u)`.
pub(crate) fn event_bond(
    holon: &Holon,
    before: &[Rat],
    after: &[Rat],
    potential_after: &[Rat],
    input: &[Rat],
    slip: &ExactRatMatrix,
    interval: &Rat,
) -> Result<Bond, HolonError> {
    let storage_flow: Vec<Rat> = after
        .iter()
        .zip(before)
        .map(|(after, before)| -(after - before) / interval)
        .collect();
    let drops = slip.apply(potential_after)?;
    let traction: Vec<Rat> = holon
        .port_holon()
        .resistance()
        .resistance()
        .apply(&drops)?
        .into_iter()
        .map(|value| -value)
        .collect();
    let bond = Bond::new(storage_flow, potential_after.to_vec())?
        .concat(&Bond::new(drops, traction)?)
        .concat(&Bond::new(potential_after.to_vec(), input.to_vec())?);
    if !holon.port_holon().dirac().contains(&bond)? {
        return Err(HolonError::NotAdmitted);
    }
    Ok(bond)
}

impl DiffusionEnergyBalance {
    /// **This event balance as the core energy balance**: `port = source_work`,
    /// `dissipated = conductive_dissipation`, `discretization_defect = −implicit_step_defect`, no
    /// active or deposited term, and `stored_change = E_after − E_before`, recovered exactly as
    /// `source_work − conduction − defect + exact_residual`. The core residual is then this
    /// balance's `exact_residual`, number for number.
    pub fn energy_balance(&self) -> EnergyBalance {
        let stored_change =
            &self.source_work - &self.conductive_dissipation - &self.implicit_step_defect
                + &self.exact_residual;
        let zero = Rat::zero();
        EnergyBalance::closed(
            stored_change,
            self.conductive_dissipation.clone(),
            self.source_work.clone(),
            zero.clone(),
            zero,
            -self.implicit_step_defect.clone(),
        )
    }

    /// **A core balance read as a diffusion event balance.** A diffusion event owes no active and
    /// no deposited term (its capacities are fixed during the event); either is refused by name.
    pub fn from_energy_balance(balance: &EnergyBalance) -> Result<Self, DiffusionError> {
        if !balance.active.is_zero() {
            return Err(DiffusionError::NotADiffusionBalance {
                term: "an active power",
            });
        }
        if !balance.deposition_work.is_zero() {
            return Err(DiffusionError::NotADiffusionBalance {
                term: "a deposition work",
            });
        }
        Ok(Self {
            source_work: balance.port.clone(),
            conductive_dissipation: balance.dissipated.clone(),
            implicit_step_defect: -balance.discretization_defect.clone(),
            exact_residual: balance.residual.clone(),
        })
    }
}

impl ExactDiffusionLaw {
    /// The node order of the Holon's storage and external ports: the complex's node order.
    fn holon_nodes(&self) -> Vec<CurrentNodeId> {
        self.complex.nodes.keys().copied().collect()
    }

    /// The oriented drop map (branches × nodes, `+1` at the source, `−1` at the target) and the
    /// conductances, in the complex's branch order. The drop map is `−d₀` of the complex's core
    /// chart ([`DiffusionComplex::graph_chart`]): the endpoint drop `φ(s) − φ(t)` is the negated
    /// coboundary, read from the one incidence owner rather than rebuilt here.
    fn drop_map(&self) -> Result<(ExactRatMatrix, ExactRatMatrix), DiffusionError> {
        let chart = self.complex.graph_chart()?;
        let slip = chart.complex().incidence()?.scaled(&-Rat::one());
        let conductance = self.complex.conductance_relation()?.resistance().clone();
        Ok((slip, conductance))
    }

    /// **This complex as a core Holon** (see the module header): storage `C⁻¹` on the node contents
    /// in node order, resistive branch ports in branch order, one external port per node.
    pub fn holon(&self) -> Result<Holon, DiffusionError> {
        let capacities: Vec<Rat> = self
            .complex
            .nodes
            .values()
            .map(|node| node.capacity.clone())
            .collect();
        let (slip, conductance) = self.drop_map()?;
        Ok(diffusion_holon(&capacities, &slip, conductance)?)
    }

    /// **This law as a `HolonLaw` at a declared interval**: its words are this law's own events.
    pub fn holon_law(&self, interval: Rat) -> Result<DiffusionHolonLaw, DiffusionError> {
        if !interval.is_positive() {
            return Err(DiffusionError::NonpositiveInterval);
        }
        let (slip, _) = self.drop_map()?;
        Ok(DiffusionHolonLaw {
            reference: ReferenceHolon::new(self.holon()?, interval, Scheme::BackwardEuler)?,
            solver: Some((self.clone(), slip)),
        })
    }
}

/// **Exact diffusion as a core `HolonLaw`** at one declared interval. `advance` enacts the
/// diffusion law's own event while the law is a single complex; a joined law advances through the
/// core reference motion.
#[derive(Clone, Debug)]
pub struct DiffusionHolonLaw {
    reference: ReferenceHolon,
    solver: Option<(ExactDiffusionLaw, ExactRatMatrix)>,
}

impl DiffusionHolonLaw {
    /// The core reference law on the same Holon (backward Euler at the declared interval).
    pub fn reference(&self) -> &ReferenceHolon {
        &self.reference
    }

    /// Whether `advance` runs the diffusion law's own event (a single complex) or the reference.
    pub fn is_diffusion_event(&self) -> bool {
        self.solver.is_some()
    }
}

/// A diffusion refusal where the core law vocabulary is owed; the diffusion law's own refusal is
/// named by the caller that enacts it directly.
fn refused(_: DiffusionError) -> HolonError {
    HolonError::Unsupported {
        what: "an exact diffusion event",
        reason: "the diffusion law refused the event; enact it directly for its own refusal",
    }
}

impl HolonLaw for DiffusionHolonLaw {
    fn holon(&self) -> &Holon {
        self.reference.holon()
    }

    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError> {
        let Some((law, slip)) = &self.solver else {
            return self.reference.advance(state, input);
        };
        let nodes = law.holon_nodes();
        for (what, found) in [
            ("diffusion configuration", state.configuration.len()),
            ("diffusion external efforts", input.len()),
        ] {
            if found != nodes.len() {
                return Err(HolonError::Shape {
                    what,
                    expected: nodes.len(),
                    found,
                });
            }
        }
        let interval = self.reference.step();
        let standing = law
            .initial_standing(
                nodes
                    .iter()
                    .copied()
                    .zip(state.configuration.iter().cloned())
                    .collect(),
            )
            .map_err(refused)?;
        let event = DiffusionEvent {
            interval: interval.clone(),
            source: nodes
                .iter()
                .copied()
                .zip(input.iter().map(|effort| effort * interval))
                .collect(),
        };
        let (after, receipt) = law.enact(&standing, &event).map_err(refused)?;
        let configuration: Vec<Rat> = nodes
            .iter()
            .map(|node| after.content[node].clone())
            .collect();
        let potential: Vec<Rat> = nodes
            .iter()
            .map(|node| receipt.potential_after[node].clone())
            .collect();
        let bond = event_bond(
            self.holon(),
            &state.configuration,
            &configuration,
            &potential,
            input,
            slip,
            interval,
        )?;
        let balance = receipt.energy_balance().map_err(refused)?.energy_balance();
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

impl From<HolonError> for DiffusionError {
    fn from(error: HolonError) -> Self {
        Self::Holon(Box::new(error))
    }
}

impl From<CoreChartRefusal> for DiffusionError {
    /// A core refusal keeps its witness; a chart refusal of a validated complex (an endpoint outside
    /// the nodes, a repeated identity) says the complex is malformed.
    fn from(refusal: CoreChartRefusal) -> Self {
        match refusal {
            CoreChartRefusal::Holon(error) => Self::Holon(error),
            _ => Self::MalformedComplex,
        }
    }
}

// The complex as the core complex `K` with its two element relations (plan phase 4).
impl DiffusionComplex {
    /// [definition] **The complex as the core graph complex**: one 0-cell per node and one 1-cell per
    /// branch, in identity order, `∂₁` with `−1` at each branch's source and `+1` at its target
    /// (`holonic_core::complex::CellComplex::graph`). A diffusion complex is this incidence with two
    /// element relations: the capacities ([`Self::capacity_storage`]) and the conductances
    /// ([`Self::conductance_relation`]).
    pub fn graph_chart(
        &self,
    ) -> Result<GraphChart<CurrentNodeId, CurrentBranchId>, CoreChartRefusal> {
        GraphChart::new(
            self.nodes.keys().copied(),
            self.branches
                .values()
                .map(|branch| (branch.branch, branch.source, branch.target)),
        )
    }

    /// [definition] **The capacities as core storage** `C⁻¹` on the node contents, so the storage
    /// effort is the potential `φ = n / c`.
    pub fn capacity_storage(&self) -> SymmetricForm {
        SymmetricForm::from_diagonal(
            self.nodes
                .values()
                .map(|node| Rat::one() / &node.capacity)
                .collect(),
        )
    }

    /// [definition] **The conductances as the core resistive element** `R = diag(conductance)` on
    /// the branch drops, certified passive (every conductance is nonnegative).
    pub fn conductance_relation(&self) -> Result<ResistiveRelation, CoreChartRefusal> {
        let conductance = ExactRatMatrix::from_diagonal(
            self.branches
                .values()
                .map(|branch| branch.conductance.clone())
                .collect(),
        )?;
        Ok(ResistiveRelation::new(conductance)?)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use holonic_core::conformance::{
        check_exact_advance, check_interaction, check_restriction, check_run, check_tellegen,
    };
    use holonic_core::restriction::PortMap;
    use relational_geometry::integer;

    use super::*;
    use crate::diffusion::{DiffusionBranch, DiffusionComplex, DiffusionNode, DiffusionStanding};
    use crate::{CurrentBranchId, CurrentNodeId};

    fn two_nodes() -> ExactDiffusionLaw {
        let complex = DiffusionComplex::new(
            [
                DiffusionNode {
                    node: CurrentNodeId(1),
                    capacity: integer(1),
                },
                DiffusionNode {
                    node: CurrentNodeId(2),
                    capacity: integer(1),
                },
            ],
            [DiffusionBranch {
                branch: CurrentBranchId(1),
                source: CurrentNodeId(1),
                target: CurrentNodeId(2),
                conductance: integer(1),
            }],
        )
        .unwrap();
        ExactDiffusionLaw::new(complex).unwrap()
    }

    fn three_nodes() -> ExactDiffusionLaw {
        let node = |id: u64, capacity: i64| DiffusionNode {
            node: CurrentNodeId(id),
            capacity: integer(capacity),
        };
        let branch = |id: u64, source: u64, target: u64, conductance: i64| DiffusionBranch {
            branch: CurrentBranchId(id),
            source: CurrentNodeId(source),
            target: CurrentNodeId(target),
            conductance: integer(conductance),
        };
        let complex = DiffusionComplex::new(
            [node(1, 2), node(2, 1), node(3, 3)],
            [branch(1, 1, 2, 1), branch(2, 3, 2, 2), branch(3, 1, 3, 0)],
        )
        .unwrap();
        ExactDiffusionLaw::new(complex).unwrap()
    }

    /// **The complex is the core graph complex with its two elements (plan phase 4).** The drop map
    /// is `−d₀` of the chart, the Holon's storage is the capacity storage, and the event's node
    /// balances are the core boundary `∂₁` of its integrated branch transfers, number for number.
    #[test]
    fn the_diffusion_complex_is_the_core_graph_with_capacity_and_conductance() {
        let law = three_nodes();
        let chart = law.complex.graph_chart().unwrap();
        let incidence = chart.complex().incidence().unwrap();
        let (slip, conductance) = law.drop_map().unwrap();
        assert_eq!(slip, incidence.scaled(&-Rat::one()));
        assert_eq!(
            &conductance,
            law.complex.conductance_relation().unwrap().resistance()
        );
        let holon = law.holon().unwrap();
        assert_eq!(
            holon.port_holon().storage(),
            &law.complex.capacity_storage()
        );
        assert_eq!(
            (
                chart.complex().betti(0).unwrap(),
                chart.complex().betti(1).unwrap()
            ),
            (1, 1)
        );

        let standing = law
            .initial_standing(BTreeMap::from([
                (CurrentNodeId(1), integer(4)),
                (CurrentNodeId(2), integer(0)),
                (CurrentNodeId(3), integer(-1)),
            ]))
            .unwrap();
        let (_, receipt) = law
            .enact(
                &standing,
                &DiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::from([(CurrentNodeId(2), integer(1))]),
                },
            )
            .unwrap();
        let transferred: Vec<Rat> = chart
            .edges()
            .iter()
            .map(|branch| {
                receipt
                    .currents
                    .iter()
                    .find(|current| current.branch == *branch)
                    .unwrap()
                    .transferred
                    .clone()
            })
            .collect();
        let boundary = chart
            .complex()
            .boundary(1)
            .unwrap()
            .apply(&transferred)
            .unwrap();
        for (at, node) in chart.vertices().iter().enumerate() {
            let balance = receipt
                .balances
                .iter()
                .find(|balance| balance.node == *node)
                .unwrap();
            assert_eq!(boundary[at], balance.boundary_transfer);
        }
    }

    /// The existing two-node witness (`two_node_diffusion_transports_and_conserves_exactly`), read
    /// through the core: the same state, the same numbers, and the reference backward-Euler word of
    /// the same Holon agrees exactly.
    #[test]
    fn the_diffusion_event_is_the_backward_euler_word_of_its_holon() {
        let law = two_nodes();
        let holon_law = law.holon_law(integer(1)).unwrap();
        assert!(holon_law.is_diffusion_event());
        let state = HolonState::new(vec![integer(1), integer(0)]);
        for input in [vec![integer(0), integer(0)], vec![integer(1), integer(0)]] {
            let advance = check_exact_advance(&holon_law, &state, &input).unwrap();
            let reference = holon_law.reference().advance(&state, &input).unwrap();
            assert_eq!(
                advance, reference,
                "the event and the core word agree exactly"
            );

            // The old computation, read off the receipt, against the core balance.
            let standing = law
                .initial_standing(BTreeMap::from([
                    (CurrentNodeId(1), integer(1)),
                    (CurrentNodeId(2), integer(0)),
                ]))
                .unwrap();
            let (_, receipt) = law
                .enact(
                    &standing,
                    &DiffusionEvent {
                        interval: integer(1),
                        source: BTreeMap::from([(CurrentNodeId(1), input[0].clone())]),
                    },
                )
                .unwrap();
            let old = receipt.energy_balance().unwrap();
            let core = old.energy_balance();
            assert_eq!(core, advance.balance);
            assert_eq!(
                core.stored_change,
                &receipt.stored_energy_after - &receipt.stored_energy_before
            );
            assert_eq!(core.dissipated, old.conductive_dissipation);
            assert_eq!(core.port, old.source_work);
            assert_eq!(
                core.discretization_defect,
                -old.implicit_step_defect.clone()
            );
            assert_eq!(core.residual, old.exact_residual);
            assert_eq!(
                DiffusionEnergyBalance::from_energy_balance(&core).unwrap(),
                old
            );
        }
        // The witness numbers of the existing test.
        let advance = holon_law
            .advance(&state, &[integer(0), integer(0)])
            .unwrap();
        assert_eq!(
            advance.state.configuration,
            vec![integer(2) / integer(3), integer(1) / integer(3)]
        );
        assert_eq!(advance.balance.dissipated, integer(1) / integer(9));
        assert_eq!(
            advance.balance.discretization_defect,
            -integer(1) / integer(9)
        );
    }

    #[test]
    fn a_balance_with_active_or_deposited_work_is_not_a_diffusion_balance() {
        let mut balance = DiffusionEnergyBalance {
            source_work: integer(1),
            conductive_dissipation: integer(0),
            implicit_step_defect: integer(0),
            exact_residual: integer(0),
        }
        .energy_balance();
        balance.deposition_work = integer(1);
        assert_eq!(
            DiffusionEnergyBalance::from_energy_balance(&balance),
            Err(DiffusionError::NotADiffusionBalance {
                term: "a deposition work"
            })
        );
    }

    /// Generic conformance (`holonic_core::conformance`) against the diffusion law: Tellegen on its
    /// structure, exact words over a run, interaction closure and restriction.
    #[test]
    fn exact_diffusion_passes_the_core_conformance_checks() {
        let law = three_nodes();
        let holon_law = law.holon_law(integer(1) / integer(2)).unwrap();
        check_tellegen(holon_law.holon().port_holon().dirac()).unwrap();
        let state = HolonState::new(vec![integer(4), integer(-1), integer(3)]);
        let input = vec![integer(1), integer(0), integer(-2)];
        let (reached, total) = check_run(&holon_law, &state, &input, 3).unwrap();
        assert!(total.is_exact());
        assert!(total.dissipated >= Rat::zero());
        // Every word is the diffusion event: the reached content is the law's own.
        let mut standing: DiffusionStanding = law
            .initial_standing(
                [1, 2, 3]
                    .into_iter()
                    .map(CurrentNodeId)
                    .zip(state.configuration.iter().cloned())
                    .collect(),
            )
            .unwrap();
        for _ in 0..3 {
            standing = law
                .enact(
                    &standing,
                    &DiffusionEvent {
                        interval: integer(1) / integer(2),
                        source: [1, 2, 3]
                            .into_iter()
                            .map(CurrentNodeId)
                            .zip(input.iter().map(|u| u / integer(2)))
                            .collect(),
                    },
                )
                .unwrap()
                .0;
        }
        assert_eq!(
            reached.configuration,
            standing.content.values().cloned().collect::<Vec<_>>()
        );

        // Two complexes joined at one node port: a Holon, advancing through the reference.
        let other = two_nodes().holon_law(integer(1) / integer(2)).unwrap();
        let (joined, _) = check_interaction(
            &holon_law,
            &other,
            &[(0, 0)],
            &state.configuration,
            &[integer(1), integer(2)],
            &[integer(0), integer(0), integer(1)],
        )
        .unwrap();
        assert!(!joined.is_diffusion_event());

        let ports = holon_law.holon().port_holon().counts().total();
        let identity = PortMap::new(ExactRatMatrix::identity(ports).unwrap());
        let flow: Vec<Rat> = (0..ports as i64).map(integer).collect();
        check_restriction(&holon_law, &identity, &flow, &flow).unwrap();
    }
}
