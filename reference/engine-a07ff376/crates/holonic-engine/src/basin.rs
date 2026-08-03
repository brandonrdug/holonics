//! Exact caused-outcome geometry over a bounded configuration complex.
//!
//! Probability is not stored as a primitive success scalar. A declared
//! preparation supplies exact source standings, deeds, adjacency, action
//! lengths, and measure. The production `ExactEventLaw` advances every
//! configuration from its own immutable predecessor. A receiver-relative
//! observation then cuts the resulting complex into an accepted basin and its
//! geometric loss body.
//!
//! This module is the exact finite-complex species of that construction. It
//! does not claim that an arbitrary continuous configuration space has already
//! been partitioned. Continuous species require their own exact or certified
//! cell decomposition before they may use the same measure and boundary
//! operations.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_traits::{Signed, Zero};
use relational_geometry::{Rat, ReceiverId};
use thiserror::Error;

use crate::{EventSuccessor, ExactEventLaw};

pub type ExactOutcomeBasinResult<S, E, R, O, LawError> =
    Result<ExactOutcomeBasin<S, E, R, O>, CausalBasinError<LawError>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConfigurationCellId(pub u64);

/// One exact preparation cell.
///
/// `standing` and `deed` are source material. No successor or accepted label
/// is supplied by the application.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactConfigurationCell<S, E> {
    pub id: ConfigurationCellId,
    pub standing: S,
    pub deed: E,
    pub measure: Rat,
}

/// One undirected local relation in configuration space.
///
/// `action` is the exact cost of crossing this relation. It need not equal its
/// measure and is not silently interpreted as probability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactConfigurationAdjacency {
    pub left: ConfigurationCellId,
    pub right: ConfigurationCellId,
    pub action: Rat,
}

impl ExactConfigurationAdjacency {
    fn canonical(mut self) -> Self {
        if self.right < self.left {
            std::mem::swap(&mut self.left, &mut self.right);
        }
        self
    }
}

/// A bounded exact preparation geometry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactConfigurationComplex<S, E> {
    pub schema: String,
    pub cells: BTreeMap<ConfigurationCellId, ExactConfigurationCell<S, E>>,
    pub adjacency: Vec<ExactConfigurationAdjacency>,
}

impl<S, E> ExactConfigurationComplex<S, E> {
    pub fn new(
        cells: impl IntoIterator<Item = ExactConfigurationCell<S, E>>,
        adjacency: impl IntoIterator<Item = ExactConfigurationAdjacency>,
    ) -> Result<Self, ConfigurationComplexError> {
        let mut indexed = BTreeMap::new();
        for cell in cells {
            if cell.measure.is_negative() {
                return Err(ConfigurationComplexError::NegativeMeasure(cell.id));
            }
            let id = cell.id;
            if indexed.insert(id, cell).is_some() {
                return Err(ConfigurationComplexError::DuplicateCell(id));
            }
        }
        if indexed.is_empty() {
            return Err(ConfigurationComplexError::Empty);
        }
        if indexed.values().all(|cell| cell.measure.is_zero()) {
            return Err(ConfigurationComplexError::ZeroTotalMeasure);
        }

        let mut edges = adjacency
            .into_iter()
            .map(ExactConfigurationAdjacency::canonical)
            .collect::<Vec<_>>();
        edges.sort_by_key(|edge| (edge.left, edge.right));
        for edge in &edges {
            if edge.left == edge.right {
                return Err(ConfigurationComplexError::Loop(edge.left));
            }
            if !indexed.contains_key(&edge.left) {
                return Err(ConfigurationComplexError::MissingEndpoint(edge.left));
            }
            if !indexed.contains_key(&edge.right) {
                return Err(ConfigurationComplexError::MissingEndpoint(edge.right));
            }
            if edge.action.is_negative() {
                return Err(ConfigurationComplexError::NegativeAction {
                    left: edge.left,
                    right: edge.right,
                });
            }
        }
        if edges
            .windows(2)
            .any(|pair| (pair[0].left, pair[0].right) == (pair[1].left, pair[1].right))
        {
            return Err(ConfigurationComplexError::DuplicateAdjacency);
        }
        Ok(Self {
            schema: "holonic-engine.exact-configuration-complex.v1".to_owned(),
            cells: indexed,
            adjacency: edges,
        })
    }

    pub fn total_measure(&self) -> Rat {
        self.cells
            .values()
            .fold(Rat::zero(), |sum, cell| sum + &cell.measure)
    }

    /// Advance every exact preparation through the same production law, then
    /// form a receiver-relative caused basin.
    ///
    /// The observer declares the consequence quotient; `accepts` selects the
    /// desired consequence classes. Neither callback supplies a successor.
    pub fn enact_outcome_basin<L, O, Observe, Accept>(
        &self,
        law: &L,
        receiver: ReceiverId,
        mut observe: Observe,
        mut accepts: Accept,
    ) -> ExactOutcomeBasinResult<S, E, L::Radiation, O, L::Error>
    where
        S: Clone + PartialEq + Eq,
        E: Clone,
        L: ExactEventLaw<Standing = S, Event = E>,
        L::Radiation: Clone + PartialEq + Eq,
        O: Clone + PartialEq + Eq + PartialOrd + Ord,
        Observe: FnMut(ReceiverId, ConfigurationCellId, &EventSuccessor<S, L::Radiation>) -> O,
        Accept: FnMut(&O) -> bool,
    {
        let mut outcomes = BTreeMap::new();
        let mut quotient = BTreeMap::<O, BTreeSet<ConfigurationCellId>>::new();
        let mut accepted = BTreeSet::new();
        for cell in self.cells.values() {
            let successor = law
                .enact(&cell.standing, &cell.deed)
                .map_err(CausalBasinError::Law)?;
            let outcome = observe(receiver, cell.id, &successor);
            if accepts(&outcome) {
                accepted.insert(cell.id);
            }
            quotient.entry(outcome.clone()).or_default().insert(cell.id);
            outcomes.insert(
                cell.id,
                CausalOutcomeCell {
                    id: cell.id,
                    source_standing: cell.standing.clone(),
                    deed: cell.deed.clone(),
                    successor,
                    outcome,
                    measure: cell.measure.clone(),
                },
            );
        }
        let all = self.cells.keys().copied().collect::<BTreeSet<_>>();
        let rejected = all.difference(&accepted).copied().collect::<BTreeSet<_>>();
        let accepted_geometry = self.region_geometry(&accepted);
        let rejected_geometry = self.region_geometry(&rejected);
        let boundary = self
            .adjacency
            .iter()
            .filter_map(|edge| {
                let left = accepted.contains(&edge.left);
                let right = accepted.contains(&edge.right);
                (left != right).then(|| ExactBasinBoundary {
                    rejected: if left { edge.right } else { edge.left },
                    accepted: if left { edge.left } else { edge.right },
                    action: edge.action.clone(),
                })
            })
            .collect::<Vec<_>>();
        let corrections = rejected
            .iter()
            .copied()
            .map(|source| {
                (
                    source,
                    self.minimum_correction(source, &accepted)
                        .map(|(action, path)| ExactCorrectivePath {
                            source,
                            accepted: *path
                                .last()
                                .expect("a corrective path includes its accepted target"),
                            action,
                            path,
                        }),
                )
            })
            .collect();
        let total_measure = self.total_measure();
        let accepted_measure = accepted
            .iter()
            .fold(Rat::zero(), |sum, id| sum + &self.cells[id].measure);
        let rejected_measure = &total_measure - &accepted_measure;
        Ok(ExactOutcomeBasin {
            schema: "holonic-engine.exact-outcome-basin.v1".to_owned(),
            receiver,
            outcomes,
            outcome_quotient: quotient,
            accepted: accepted_geometry,
            loss: ExactGeometricLoss {
                region: rejected_geometry,
                boundary,
                minimum_corrections: corrections,
                measure: rejected_measure,
            },
            total_measure: total_measure.clone(),
            accepted_measure: accepted_measure.clone(),
            probability: accepted_measure / total_measure,
        })
    }

    fn region_geometry(&self, members: &BTreeSet<ConfigurationCellId>) -> ExactBasinRegion {
        let adjacency = self
            .adjacency
            .iter()
            .filter(|edge| members.contains(&edge.left) && members.contains(&edge.right))
            .cloned()
            .collect::<Vec<_>>();
        let components = connected_components(members, &adjacency);
        let cycle_rank = adjacency
            .len()
            .saturating_add(components.len())
            .saturating_sub(members.len());
        ExactBasinRegion {
            members: members.clone(),
            adjacency,
            components,
            cycle_rank,
        }
    }

    fn minimum_correction(
        &self,
        source: ConfigurationCellId,
        accepted: &BTreeSet<ConfigurationCellId>,
    ) -> Option<(Rat, Vec<ConfigurationCellId>)> {
        if accepted.contains(&source) {
            return Some((Rat::zero(), vec![source]));
        }
        if accepted.is_empty() {
            return None;
        }
        let mut distance = BTreeMap::from([(source, Rat::zero())]);
        let mut predecessor = BTreeMap::<ConfigurationCellId, ConfigurationCellId>::new();
        let mut unsettled = self.cells.keys().copied().collect::<BTreeSet<_>>();
        while !unsettled.is_empty() {
            let current = unsettled
                .iter()
                .filter_map(|cell| distance.get(cell).map(|distance| (*cell, distance)))
                .min_by(|(left_id, left), (right_id, right)| {
                    left.cmp(right).then_with(|| left_id.cmp(right_id))
                })
                .map(|(cell, _)| cell)?;
            unsettled.remove(&current);
            if accepted.contains(&current) {
                let mut path = vec![current];
                let mut cursor = current;
                while let Some(parent) = predecessor.get(&cursor).copied() {
                    path.push(parent);
                    cursor = parent;
                }
                path.reverse();
                return Some((distance[&current].clone(), path));
            }
            for edge in self
                .adjacency
                .iter()
                .filter(|edge| edge.left == current || edge.right == current)
            {
                let neighbour = if edge.left == current {
                    edge.right
                } else {
                    edge.left
                };
                if !unsettled.contains(&neighbour) {
                    continue;
                }
                let candidate = &distance[&current] + &edge.action;
                let improve = distance
                    .get(&neighbour)
                    .is_none_or(|known| candidate < *known);
                if improve {
                    distance.insert(neighbour, candidate);
                    predecessor.insert(neighbour, current);
                }
            }
        }
        None
    }
}

fn connected_components(
    members: &BTreeSet<ConfigurationCellId>,
    adjacency: &[ExactConfigurationAdjacency],
) -> Vec<BTreeSet<ConfigurationCellId>> {
    let mut unseen = members.clone();
    let mut components = Vec::new();
    while let Some(root) = unseen.first().copied() {
        unseen.remove(&root);
        let mut component = BTreeSet::from([root]);
        let mut frontier = VecDeque::from([root]);
        while let Some(cell) = frontier.pop_front() {
            for edge in adjacency
                .iter()
                .filter(|edge| edge.left == cell || edge.right == cell)
            {
                let neighbour = if edge.left == cell {
                    edge.right
                } else {
                    edge.left
                };
                if unseen.remove(&neighbour) {
                    component.insert(neighbour);
                    frontier.push_back(neighbour);
                }
            }
        }
        components.push(component);
    }
    components
}

/// Full production testimony for one configuration cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalOutcomeCell<S, E, R, O> {
    pub id: ConfigurationCellId,
    pub source_standing: S,
    pub deed: E,
    pub successor: EventSuccessor<S, R>,
    pub outcome: O,
    pub measure: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactBasinRegion {
    pub members: BTreeSet<ConfigurationCellId>,
    pub adjacency: Vec<ExactConfigurationAdjacency>,
    pub components: Vec<BTreeSet<ConfigurationCellId>>,
    /// First Betti number of this finite graph species.
    pub cycle_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactBasinBoundary {
    pub rejected: ConfigurationCellId,
    pub accepted: ConfigurationCellId,
    pub action: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactCorrectivePath {
    pub source: ConfigurationCellId,
    pub accepted: ConfigurationCellId,
    pub action: Rat,
    pub path: Vec<ConfigurationCellId>,
}

/// The rejected body remains geometric. Its measure is only one derived face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactGeometricLoss {
    pub region: ExactBasinRegion,
    pub boundary: Vec<ExactBasinBoundary>,
    pub minimum_corrections: BTreeMap<ConfigurationCellId, Option<ExactCorrectivePath>>,
    pub measure: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactOutcomeBasin<S, E, R, O> {
    pub schema: String,
    pub receiver: ReceiverId,
    pub outcomes: BTreeMap<ConfigurationCellId, CausalOutcomeCell<S, E, R, O>>,
    pub outcome_quotient: BTreeMap<O, BTreeSet<ConfigurationCellId>>,
    pub accepted: ExactBasinRegion,
    pub loss: ExactGeometricLoss,
    pub total_measure: Rat,
    pub accepted_measure: Rat,
    pub probability: Rat,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ConfigurationComplexError {
    #[error("a configuration complex requires at least one exact cell")]
    Empty,
    #[error("configuration cell {0:?} was supplied more than once")]
    DuplicateCell(ConfigurationCellId),
    #[error("configuration cell {0:?} carries negative measure")]
    NegativeMeasure(ConfigurationCellId),
    #[error("the complete preparation has zero measure")]
    ZeroTotalMeasure,
    #[error("configuration adjacency has missing endpoint {0:?}")]
    MissingEndpoint(ConfigurationCellId),
    #[error("configuration adjacency cannot loop at {0:?}")]
    Loop(ConfigurationCellId),
    #[error("configuration adjacency carries negative action between {left:?} and {right:?}")]
    NegativeAction {
        left: ConfigurationCellId,
        right: ConfigurationCellId,
    },
    #[error("one configuration adjacency was supplied more than once")]
    DuplicateAdjacency,
}

#[derive(Debug, Error)]
pub enum CausalBasinError<E> {
    #[error("the production event law refused one exact configuration")]
    Law(E),
}
