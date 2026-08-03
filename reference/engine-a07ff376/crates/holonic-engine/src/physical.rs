//! One exact physical realization of the hinge carrier.
//!
//! This module does not install universal physics.  It supplies a bounded
//! discrete variational law whose units, coefficients, boundary impulse, and
//! carried momentum are explicit.  Conservation is an exact completed-event
//! relation, not a demand that a partial interval contain no stored current.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    EventId, EventSuccessor, ExactEventLaw, HingeEvent, HingeId, HingeRadiation, HingeWorldError,
    HingeWorldLaw, HingeWorldStanding,
};

/// The selected world's declared dimensional vocabulary.
///
/// These names are source doctrine. They prevent a naked ratio from
/// impersonating a physical quantity while allowing different worlds to
/// choose different unit systems.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeUnitSystem {
    pub coordinate: String,
    pub event_step: String,
    pub action: String,
    pub momentum: String,
    pub impulse: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuadraticHingeAction {
    /// Coefficient of `(q_next-q_current)^2 / 2`.
    pub inertia: Rat,
    /// Coefficient of `q_current^2 / 2`.
    pub stiffness: Rat,
    pub units: HingeUnitSystem,
}

impl QuadraticHingeAction {
    pub fn new(
        inertia: Rat,
        stiffness: Rat,
        units: HingeUnitSystem,
    ) -> Result<Self, PhysicalLawError> {
        if inertia.is_zero() {
            return Err(PhysicalLawError::ZeroInertia);
        }
        Ok(Self {
            inertia,
            stiffness,
            units,
        })
    }
}

/// Exact invariant of the unforced quadratic recurrence.
///
/// With `alpha = 2-K/I` and state `(q_(k-1),q_k)`, the recurrence is
/// `q_(k+1)=alpha*q_k-q_(k-1)`. The returned quadratic is identical before
/// and after every event carrying zero external impulse.
pub fn quadratic_orbit_invariant(
    action: &QuadraticHingeAction,
    trajectory: &HingeTrajectory,
) -> Rat {
    let alpha = Rat::from_integer(2.into()) - &action.stiffness / &action.inertia;
    &trajectory.previous * &trajectory.previous - alpha * &trajectory.previous * &trajectory.current
        + &trajectory.current * &trajectory.current
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTrajectory {
    pub previous: Rat,
    pub current: Rat,
}

/// Complete exact physical state used to distinguish a returning orbit from a
/// sparsely sampled projection which merely looks stationary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct HingeOrbitState {
    pub trajectories: Vec<(HingeId, Rat, Rat)>,
}

impl HingeOrbitState {
    pub fn from_standing(standing: &PhysicalHingeStanding) -> Self {
        Self {
            trajectories: standing
                .trajectories
                .iter()
                .map(|(hinge, trajectory)| {
                    (
                        *hinge,
                        trajectory.previous.clone(),
                        trajectory.current.clone(),
                    )
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeOrbitCycle {
    pub first_event: u64,
    pub return_event: u64,
    pub period: u64,
    pub state: HingeOrbitState,
}

/// Receiver-external testimony about one uninterrupted physical orbit.
///
/// A boundary deed restarts observation because the resulting path belongs to
/// a new causal segment. Identity is exact state equality, never a hash.
#[derive(Clone, Debug, Default)]
pub struct ExactHingeOrbitObserver {
    seen: BTreeMap<HingeOrbitState, u64>,
    reported: bool,
}

impl ExactHingeOrbitObserver {
    pub fn restart(&mut self, event: u64, standing: &PhysicalHingeStanding) {
        self.seen.clear();
        self.seen
            .insert(HingeOrbitState::from_standing(standing), event);
        self.reported = false;
    }

    pub fn observe(
        &mut self,
        event: u64,
        standing: &PhysicalHingeStanding,
    ) -> Option<HingeOrbitCycle> {
        let state = HingeOrbitState::from_standing(standing);
        if let Some(first_event) = self.seen.get(&state).copied() {
            if self.reported {
                return None;
            }
            self.reported = true;
            return Some(HingeOrbitCycle {
                first_event,
                return_event: event,
                period: event - first_event,
                state,
            });
        }
        self.seen.insert(state, event);
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhysicalHingeStanding {
    pub schema: String,
    pub kinematic: HingeWorldStanding,
    pub trajectories: BTreeMap<HingeId, HingeTrajectory>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhysicalHingeEvent {
    pub event: EventId,
    pub pivot: HingeId,
    /// Boundary deed supplied during this one event interval.
    pub external_impulse: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActionBalanceReceipt {
    pub hinge: HingeId,
    pub coordinate_before: Rat,
    pub coordinate_after: Rat,
    pub momentum_before: Rat,
    pub internal_impulse: Rat,
    pub external_impulse: Rat,
    pub momentum_after: Rat,
    /// `p_after - p_before - internal - external`.
    pub exact_residual: Rat,
    /// Present exactly when this event has neither internal nor external
    /// impulse, so momentum is the transported invariant.
    pub free_momentum_invariant: Option<Rat>,
    /// Current carried into the next event interval.
    pub stored_boundary_current: Rat,
    pub units: HingeUnitSystem,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhysicalHingeRadiation {
    pub event: EventId,
    pub balance: ActionBalanceReceipt,
    pub kinematic: HingeRadiation,
}

#[derive(Clone, Debug)]
pub struct VariationalHingeLaw {
    pub kinematic: HingeWorldLaw,
    pub actions: BTreeMap<HingeId, QuadraticHingeAction>,
}

impl VariationalHingeLaw {
    pub fn new(
        kinematic: HingeWorldLaw,
        actions: BTreeMap<HingeId, QuadraticHingeAction>,
    ) -> Result<Self, PhysicalLawError> {
        for hinge in kinematic.complex.hinges.keys() {
            if !actions.contains_key(hinge) {
                return Err(PhysicalLawError::MissingAction(*hinge));
            }
        }
        for hinge in actions.keys() {
            if !kinematic.complex.hinges.contains_key(hinge) {
                return Err(PhysicalLawError::MissingHinge(*hinge));
            }
        }
        Ok(Self { kinematic, actions })
    }

    pub fn initial_standing(
        &self,
        kinematic: HingeWorldStanding,
        trajectories: BTreeMap<HingeId, HingeTrajectory>,
    ) -> Result<PhysicalHingeStanding, PhysicalLawError> {
        for (hinge, parameter) in &kinematic.parameters {
            let trajectory = trajectories
                .get(hinge)
                .ok_or(PhysicalLawError::MissingTrajectory(*hinge))?;
            if &trajectory.current != parameter {
                return Err(PhysicalLawError::TrajectoryStandingMismatch {
                    hinge: *hinge,
                    trajectory: Box::new(trajectory.current.clone()),
                    standing: Box::new(parameter.clone()),
                });
            }
        }
        Ok(PhysicalHingeStanding {
            schema: "holonic-engine.physical-hinge-standing.v1".to_owned(),
            kinematic,
            trajectories,
        })
    }
}

impl ExactEventLaw for VariationalHingeLaw {
    type Standing = PhysicalHingeStanding;
    type Event = PhysicalHingeEvent;
    type Radiation = PhysicalHingeRadiation;
    type Error = PhysicalLawError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let action = self
            .actions
            .get(&event.pivot)
            .ok_or(PhysicalLawError::MissingAction(event.pivot))?;
        let trajectory = standing_before
            .trajectories
            .get(&event.pivot)
            .ok_or(PhysicalLawError::MissingTrajectory(event.pivot))?;

        // This is the exact discrete Euler--Lagrange update for
        //
        // L_d(q_{k-1},q_k)
        //   = I/2 (q_k-q_{k-1})^2 - K/2 q_k^2 + J_k q_k.
        //
        // It is written in current form so the boundary deed and stored
        // continuation remain visible.
        let momentum_before = &action.inertia * (&trajectory.current - &trajectory.previous);
        let internal_impulse = -&action.stiffness * &trajectory.current;
        let momentum_after = &momentum_before + &internal_impulse + &event.external_impulse;
        let coordinate_after = &trajectory.current + &momentum_after / &action.inertia;
        let exact_residual =
            &momentum_after - &momentum_before - &internal_impulse - &event.external_impulse;
        debug_assert!(exact_residual.is_zero());

        let kinematic_successor = self.kinematic.enact(
            &standing_before.kinematic,
            &HingeEvent {
                event: event.event,
                pivot: event.pivot,
                parameter: coordinate_after.clone(),
            },
        )?;
        let mut standing_after = PhysicalHingeStanding {
            schema: standing_before.schema.clone(),
            kinematic: kinematic_successor.standing_after,
            trajectories: standing_before.trajectories.clone(),
        };
        for changed in &kinematic_successor.radiation[0].changed_hinges {
            let previous_coordinate = standing_before
                .kinematic
                .parameters
                .get(changed)
                .ok_or(PhysicalLawError::MissingTrajectory(*changed))?;
            let current_coordinate = standing_after
                .kinematic
                .parameters
                .get(changed)
                .ok_or(PhysicalLawError::MissingTrajectory(*changed))?;
            let carried = standing_after
                .trajectories
                .get_mut(changed)
                .ok_or(PhysicalLawError::MissingTrajectory(*changed))?;
            carried.previous = previous_coordinate.clone();
            carried.current = current_coordinate.clone();
        }
        // Coordinate equality is not event equality. The selected physical
        // worldline advances across every completed event even when its
        // projected hinge coordinate returns unchanged. Otherwise a turning
        // point is collapsed into false rest and the next variational event
        // loses its incoming boundary current.
        let pivot_carried = standing_after
            .trajectories
            .get_mut(&event.pivot)
            .ok_or(PhysicalLawError::MissingTrajectory(event.pivot))?;
        pivot_carried.previous = trajectory.current.clone();
        pivot_carried.current = coordinate_after.clone();
        let free_momentum_invariant = (internal_impulse.is_zero()
            && event.external_impulse.is_zero())
        .then_some(momentum_after.clone());
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![PhysicalHingeRadiation {
                event: event.event,
                balance: ActionBalanceReceipt {
                    hinge: event.pivot,
                    coordinate_before: trajectory.current.clone(),
                    coordinate_after,
                    momentum_before,
                    internal_impulse,
                    external_impulse: event.external_impulse.clone(),
                    momentum_after: momentum_after.clone(),
                    exact_residual,
                    free_momentum_invariant,
                    stored_boundary_current: momentum_after,
                    units: action.units.clone(),
                },
                kinematic: kinematic_successor.radiation[0].clone(),
            }],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PhysicalLawError {
    #[error("a quadratic hinge action requires nonzero inertia")]
    ZeroInertia,
    #[error("hinge {0:?} is absent from the physical world")]
    MissingHinge(HingeId),
    #[error("hinge {0:?} has no declared action law")]
    MissingAction(HingeId),
    #[error("hinge {0:?} has no carried trajectory")]
    MissingTrajectory(HingeId),
    #[error("hinge {hinge:?} trajectory current {trajectory} differs from standing {standing}")]
    TrajectoryStandingMismatch {
        hinge: HingeId,
        trajectory: Box<Rat>,
        standing: Box<Rat>,
    },
    #[error("node {0:?} carries incommensurate current units")]
    IncommensurateCurrentUnit(CurrentNodeId),
    #[error("a potential word requires at least two nodes")]
    ShortPotentialWord,
    #[error("node {0:?} has no declared potential")]
    MissingPotential(CurrentNodeId),
    #[error("stress requires a nonzero exact deformation")]
    ZeroDeformation,
    #[error(transparent)]
    Kinematic(#[from] HingeWorldError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CurrentNodeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CurrentBranchId(pub u64);

/// One oriented exact current during one declared event interval.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedCurrentBranch {
    pub id: CurrentBranchId,
    pub source: CurrentNodeId,
    pub target: CurrentNodeId,
    pub current: Rat,
    pub unit: String,
}

/// Exact source/sink content at a node during the same interval.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurrentSource {
    pub node: CurrentNodeId,
    pub amount: Rat,
    pub unit: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscreteCurrentComplex {
    pub schema: String,
    pub nodes: BTreeSet<CurrentNodeId>,
    pub branches: BTreeMap<CurrentBranchId, OrientedCurrentBranch>,
    pub sources: BTreeMap<CurrentNodeId, CurrentSource>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NodeCurrentBalance {
    pub node: CurrentNodeId,
    /// Incoming minus outgoing current: the exact boundary `partial J`.
    pub boundary_current: Rat,
    pub declared_source: Rat,
    pub residual: Rat,
    pub unit: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurrentConservationReceipt {
    pub schema: String,
    pub balances: Vec<NodeCurrentBalance>,
    pub exact: bool,
}

impl DiscreteCurrentComplex {
    pub fn conservation(&self) -> Result<CurrentConservationReceipt, PhysicalLawError> {
        let mut balances = Vec::new();
        for node in &self.nodes {
            let incident = self
                .branches
                .values()
                .filter(|branch| branch.source == *node || branch.target == *node)
                .collect::<Vec<_>>();
            let source = self.sources.get(node);
            let unit = incident
                .first()
                .map(|branch| branch.unit.clone())
                .or_else(|| source.map(|source| source.unit.clone()))
                .unwrap_or_else(|| "current".to_owned());
            if incident.iter().any(|branch| branch.unit != unit)
                || source.is_some_and(|source| source.unit != unit)
            {
                return Err(PhysicalLawError::IncommensurateCurrentUnit(*node));
            }
            let boundary_current = incident.iter().fold(Rat::zero(), |sum, branch| {
                if branch.target == *node {
                    sum + &branch.current
                } else {
                    sum - &branch.current
                }
            });
            let declared_source = source
                .map(|source| source.amount.clone())
                .unwrap_or_else(Rat::zero);
            let residual = &boundary_current - &declared_source;
            balances.push(NodeCurrentBalance {
                node: *node,
                boundary_current,
                declared_source,
                residual,
                unit,
            });
        }
        Ok(CurrentConservationReceipt {
            schema: "holonic-engine.current-conservation.v1".to_owned(),
            exact: balances.iter().all(|balance| balance.residual.is_zero()),
            balances,
        })
    }
}

/// KVL as an exact boundary-of-boundary relation.  Potentials are declared
/// at nodes; each branch drop is target minus source.  A completed closed word
/// telescopes to zero, while an unfinished word carries its endpoint
/// difference as stored current rather than pretending completion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedPotentialCycle {
    pub nodes: Vec<CurrentNodeId>,
    pub directed_drops: Vec<Rat>,
    pub loop_sum: Rat,
    pub closed: bool,
    pub endpoint_difference: Rat,
    pub exact_residual: Rat,
    pub unit: String,
}

pub fn potential_cycle(
    nodes: Vec<CurrentNodeId>,
    potentials: &BTreeMap<CurrentNodeId, Rat>,
    unit: impl Into<String>,
) -> Result<ClosedPotentialCycle, PhysicalLawError> {
    if nodes.len() < 2 {
        return Err(PhysicalLawError::ShortPotentialWord);
    }
    let values = nodes
        .iter()
        .map(|node| {
            potentials
                .get(node)
                .cloned()
                .ok_or(PhysicalLawError::MissingPotential(*node))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let directed_drops = values
        .windows(2)
        .map(|pair| &pair[1] - &pair[0])
        .collect::<Vec<_>>();
    let loop_sum = directed_drops
        .iter()
        .fold(Rat::zero(), |sum, drop| sum + drop);
    let endpoint_difference = values
        .last()
        .expect("the potential word has at least two members")
        - &values[0];
    let exact_residual = &loop_sum - &endpoint_difference;
    let closed = nodes.first() == nodes.last();
    Ok(ClosedPotentialCycle {
        nodes,
        directed_drops,
        loop_sum,
        closed,
        endpoint_difference,
        exact_residual,
        unit: unit.into(),
    })
}

/// Exact balance over an interval which may end before its current closes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredCurrentInterval {
    pub entered: Rat,
    pub sourced: Rat,
    pub departed: Rat,
    pub carried: Rat,
    pub exact_residual: Rat,
    pub unit: String,
}

impl StoredCurrentInterval {
    pub fn new(
        entered: Rat,
        sourced: Rat,
        departed: Rat,
        carried: Rat,
        unit: impl Into<String>,
    ) -> Self {
        let exact_residual = &entered + &sourced - &departed - &carried;
        Self {
            entered,
            sourced,
            departed,
            carried,
            exact_residual,
            unit: unit.into(),
        }
    }
}

/// Receiver-relative stress/tension is an action change per declared exact
/// deformation, not a sign-labelled reward.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscreteActionStress {
    pub action_before: Rat,
    pub action_after: Rat,
    pub deformation: Rat,
    pub stress: Rat,
    pub orientation: i8,
    pub action_unit: String,
    pub deformation_unit: String,
}

impl DiscreteActionStress {
    pub fn new(
        action_before: Rat,
        action_after: Rat,
        deformation: Rat,
        action_unit: impl Into<String>,
        deformation_unit: impl Into<String>,
    ) -> Result<Self, PhysicalLawError> {
        if deformation.is_zero() {
            return Err(PhysicalLawError::ZeroDeformation);
        }
        let stress = (&action_after - &action_before) / &deformation;
        let orientation = if stress.is_positive() {
            1
        } else if stress.is_negative() {
            -1
        } else {
            0
        };
        Ok(Self {
            action_before,
            action_after,
            deformation,
            stress,
            orientation,
            action_unit: action_unit.into(),
            deformation_unit: deformation_unit.into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;
    use crate::{
        CausalWorld, Edge, EventId, HingeTransportNetwork, HingeWorldLaw, SimplicialComplex,
    };

    fn free_hinge_world() -> (VariationalHingeLaw, HingeWorldStanding, HingeId) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let d = complex.found_vertex("d", founding);
        complex.found_face("left", founding, [a, b, c]).unwrap();
        complex.found_face("right", founding, [c, b, d]).unwrap();
        let hinge = complex
            .found_hinge("shared", founding, Edge::new(b, c).unwrap())
            .unwrap();
        let kinematic =
            HingeWorldLaw::new(complex, HingeTransportNetwork::default(), Vec::new()).unwrap();
        let standing = kinematic
            .initial_standing(BTreeMap::from([(hinge, integer(1))]))
            .unwrap();
        let units = HingeUnitSystem {
            coordinate: "turn".to_owned(),
            event_step: "event".to_owned(),
            action: "action".to_owned(),
            momentum: "action/turn".to_owned(),
            impulse: "action/turn".to_owned(),
        };
        let law = VariationalHingeLaw::new(
            kinematic,
            BTreeMap::from([(
                hinge,
                QuadraticHingeAction::new(integer(2), integer(0), units).unwrap(),
            )]),
        )
        .unwrap();
        (law, standing, hinge)
    }

    #[test]
    fn a_completed_free_event_transports_momentum_exactly() {
        let (law, standing, hinge) = free_hinge_world();
        let physical = law
            .initial_standing(
                standing,
                BTreeMap::from([(
                    hinge,
                    HingeTrajectory {
                        previous: integer(0),
                        current: integer(1),
                    },
                )]),
            )
            .unwrap();
        let mut world = CausalWorld::new(law, physical);
        let receipt = world
            .receive(&PhysicalHingeEvent {
                event: EventId(2),
                pivot: hinge,
                external_impulse: integer(0),
            })
            .unwrap();
        let balance = &receipt.radiation[0].balance;
        assert_eq!(balance.momentum_before, integer(2));
        assert_eq!(balance.momentum_after, integer(2));
        assert_eq!(balance.exact_residual, integer(0));
        assert_eq!(balance.free_momentum_invariant, Some(integer(2)));
        assert_eq!(balance.stored_boundary_current, integer(2));
        assert_eq!(
            world.standing().trajectories[&hinge],
            HingeTrajectory {
                previous: integer(1),
                current: integer(2)
            }
        );
    }

    #[test]
    fn a_boundary_impulse_changes_the_carried_current_without_false_loss() {
        let (law, standing, hinge) = free_hinge_world();
        let physical = law
            .initial_standing(
                standing,
                BTreeMap::from([(
                    hinge,
                    HingeTrajectory {
                        previous: integer(0),
                        current: integer(1),
                    },
                )]),
            )
            .unwrap();
        let mut world = CausalWorld::new(law, physical);
        let receipt = world
            .receive(&PhysicalHingeEvent {
                event: EventId(2),
                pivot: hinge,
                external_impulse: integer(2),
            })
            .unwrap();
        let balance = &receipt.radiation[0].balance;
        assert_eq!(balance.momentum_before, integer(2));
        assert_eq!(balance.momentum_after, integer(4));
        assert_eq!(balance.exact_residual, integer(0));
        assert_eq!(balance.free_momentum_invariant, None);
        assert_eq!(balance.stored_boundary_current, integer(4));
    }

    #[test]
    fn the_stiff_hinge_returns_after_six_events_without_sampling_alias() {
        let (mut law, standing, hinge) = free_hinge_world();
        law.actions.get_mut(&hinge).unwrap().stiffness = integer(2);
        let initial_trajectory = HingeTrajectory {
            previous: integer(0),
            current: integer(1),
        };
        let invariant = quadratic_orbit_invariant(&law.actions[&hinge], &initial_trajectory);
        let physical = law
            .initial_standing(standing, BTreeMap::from([(hinge, initial_trajectory)]))
            .unwrap();
        let mut world = CausalWorld::new(law, physical);
        let mut observer = ExactHingeOrbitObserver::default();
        observer.restart(1, world.standing());
        let mut cycle = None;
        for event in 2..=7 {
            world
                .receive(&PhysicalHingeEvent {
                    event: EventId(event),
                    pivot: hinge,
                    external_impulse: integer(0),
                })
                .unwrap();
            assert_eq!(
                quadratic_orbit_invariant(
                    &QuadraticHingeAction::new(
                        integer(2),
                        integer(2),
                        HingeUnitSystem {
                            coordinate: "q".to_owned(),
                            event_step: "event".to_owned(),
                            action: "action".to_owned(),
                            momentum: "momentum".to_owned(),
                            impulse: "impulse".to_owned(),
                        },
                    )
                    .unwrap(),
                    &world.standing().trajectories[&hinge],
                ),
                invariant
            );
            cycle = observer.observe(event, world.standing()).or(cycle);
        }
        assert_eq!(cycle.unwrap().period, 6);
    }

    #[test]
    fn current_boundary_and_closed_voltage_are_exact_over_completed_words() {
        let first = CurrentNodeId(1);
        let second = CurrentNodeId(2);
        let third = CurrentNodeId(3);
        let current = |id, source, target| OrientedCurrentBranch {
            id: CurrentBranchId(id),
            source,
            target,
            current: integer(3),
            unit: "ampere".to_owned(),
        };
        let complex = DiscreteCurrentComplex {
            schema: "test".to_owned(),
            nodes: BTreeSet::from([first, second, third]),
            branches: [
                current(1, first, second),
                current(2, second, third),
                current(3, third, first),
            ]
            .into_iter()
            .map(|branch| (branch.id, branch))
            .collect(),
            sources: BTreeMap::new(),
        };
        assert!(complex.conservation().unwrap().exact);
        let cycle = potential_cycle(
            vec![first, second, third, first],
            &BTreeMap::from([
                (first, integer(2)),
                (second, integer(5)),
                (third, integer(-1)),
            ]),
            "volt",
        )
        .unwrap();
        assert!(cycle.closed);
        assert!(cycle.loop_sum.is_zero());
        assert!(cycle.exact_residual.is_zero());
    }

    #[test]
    fn unfinished_intervals_carry_current_and_stress_retains_orientation() {
        let interval =
            StoredCurrentInterval::new(integer(5), integer(2), integer(3), integer(4), "charge");
        assert!(interval.exact_residual.is_zero());
        let stress =
            DiscreteActionStress::new(integer(7), integer(1), integer(2), "action", "length")
                .unwrap();
        assert_eq!(stress.stress, integer(-3));
        assert_eq!(stress.orientation, -1);
    }
}
