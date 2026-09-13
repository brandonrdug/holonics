//! Exact shortest-word navigation on a declared finite group.
//!
//! This owner supplies the finite Cayley/Schreier traversal primitive used by bounded
//! configuration applications. The group and move costs are caller declarations; closure is
//! performed by [`StructureGroup`], while this module derives distances, an optimal policy and the
//! retained family of minimizing continuations. It does not infer a full puzzle model from a name
//! or claim that a quotient lift is optimal for an omitted coordinate.

use crate::structure_group::{GroupElement, StructureGroup};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use thiserror::Error;

/// One named generator action and its exact positive traversal cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NavigationMove {
    pub label: String,
    pub element: GroupElement,
    pub cost: u32,
}

impl NavigationMove {
    pub fn new(
        label: impl Into<String>,
        element: GroupElement,
        cost: u32,
    ) -> Result<Self, NavigationRefusal> {
        if cost == 0 {
            return Err(NavigationRefusal::ZeroMoveCost);
        }
        Ok(Self {
            label: label.into(),
            element,
            cost,
        })
    }
}

/// A policy step that decreases exact distance to the target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NavigationStep {
    pub label: String,
    pub element: GroupElement,
    pub cost: u32,
}

/// A complete optimal traversal and its retained minimizing fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NavigationSolution {
    pub source: GroupElement,
    pub target: GroupElement,
    pub distance: u32,
    pub steps: Vec<NavigationStep>,
    pub minimizing_fibre_size: BigUint,
}

/// Exact preprocessing and policy owner for a finite declared group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactGroupNavigation {
    group: StructureGroup,
    target: GroupElement,
    moves: Vec<NavigationMove>,
    expanded_moves: Vec<NavigationMove>,
    distances: BTreeMap<GroupElement, u32>,
    shortest_word_counts: BTreeMap<GroupElement, BigUint>,
    edges_examined: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum NavigationRefusal {
    #[error("navigation requires a nonempty move set")]
    NoMoveDeclared,
    #[error("navigation move cost must be positive")]
    ZeroMoveCost,
    #[error("navigation target is outside the declared group")]
    TargetOutsideGroup,
    #[error("navigation move `{0}` is outside the declared group")]
    MoveOutsideGroup(String),
    #[error("navigation source is outside the declared group")]
    SourceOutsideGroup,
    #[error("declared moves reach {reached} of {group_order} group states")]
    MoveSetDoesNotReachGroup { reached: usize, group_order: usize },
    #[error("navigation has no path from source to target")]
    Unreachable,
    #[error("navigation path cost overflowed its declared u32 metric")]
    CostOverflow,
    #[error("navigation shortest-word reconstruction exceeded the finite group")]
    ReconstructionOverflow,
}

impl ExactGroupNavigation {
    /// Derive exact distances from every group element to `target` by weighted reverse closure.
    /// Inverse moves are added automatically, so callers declare each physical generator once.
    pub fn new(
        group: StructureGroup,
        target: GroupElement,
        moves: impl IntoIterator<Item = NavigationMove>,
    ) -> Result<Self, NavigationRefusal> {
        let moves = moves.into_iter().collect::<Vec<_>>();
        if moves.is_empty() {
            return Err(NavigationRefusal::NoMoveDeclared);
        }
        if !group.contains(&target) {
            return Err(NavigationRefusal::TargetOutsideGroup);
        }
        for movement in &moves {
            if movement.cost == 0 {
                return Err(NavigationRefusal::ZeroMoveCost);
            }
            if !group.contains(&movement.element) {
                return Err(NavigationRefusal::MoveOutsideGroup(movement.label.clone()));
            }
        }

        let mut expanded = Vec::with_capacity(moves.len() * 2);
        for movement in &moves {
            expanded.push(movement.clone());
            let inverse = movement
                .element
                .inverse()
                .ok_or_else(|| NavigationRefusal::MoveOutsideGroup(movement.label.clone()))?;
            expanded.push(NavigationMove {
                label: format!("{}'", movement.label),
                element: inverse,
                cost: movement.cost,
            });
        }

        let mut distances = BTreeMap::new();
        distances.insert(target.clone(), 0);
        let mut frontier = BinaryHeap::new();
        frontier.push((Reverse(0u32), Reverse(target.clone())));
        let mut edges_examined = 0;
        let mut overflowed = false;
        while let Some((Reverse(distance), Reverse(state))) = frontier.pop() {
            if distances.get(&state).copied() != Some(distance) {
                continue;
            }
            for movement in &expanded {
                let next = state
                    .then(&movement.element)
                    .ok_or_else(|| NavigationRefusal::MoveOutsideGroup(movement.label.clone()))?;
                edges_examined += 1;
                // An overflowing walk may be dominated by a shorter path found later. Finish
                // the search before deciding whether any shortest distance needs wider storage.
                let candidate = match distance.checked_add(movement.cost) {
                    Some(candidate) => candidate,
                    None => {
                        overflowed = true;
                        continue;
                    }
                };
                if distances.get(&next).is_none_or(|known| candidate < *known) {
                    distances.insert(next.clone(), candidate);
                    frontier.push((Reverse(candidate), Reverse(next)));
                }
            }
        }
        if distances.len() != group.order() {
            if overflowed {
                // Distinguish a disconnected move set from a connected metric which exceeds
                // u32; this additional walk is needed only on the overflow boundary.
                let mut reached = BTreeSet::from([target.clone()]);
                let mut queue = std::collections::VecDeque::from([target.clone()]);
                while let Some(state) = queue.pop_front() {
                    for movement in &expanded {
                        let next = state
                            .then(&movement.element)
                            .ok_or(NavigationRefusal::ReconstructionOverflow)?;
                        if reached.insert(next.clone()) {
                            queue.push_back(next);
                        }
                    }
                }
                if reached.len() == group.order() {
                    return Err(NavigationRefusal::CostOverflow);
                }
                return Err(NavigationRefusal::MoveSetDoesNotReachGroup {
                    reached: reached.len(),
                    group_order: group.order(),
                });
            }
            return Err(NavigationRefusal::MoveSetDoesNotReachGroup {
                reached: distances.len(),
                group_order: group.order(),
            });
        }
        let shortest_word_counts = shortest_word_counts(&target, &expanded, &distances)?;
        Ok(Self {
            group,
            target,
            moves,
            expanded_moves: expanded,
            distances,
            shortest_word_counts,
            edges_examined,
        })
    }

    pub fn group(&self) -> &StructureGroup {
        &self.group
    }
    pub fn target(&self) -> &GroupElement {
        &self.target
    }
    pub fn moves(&self) -> &[NavigationMove] {
        &self.moves
    }
    pub fn states(&self) -> usize {
        self.distances.len()
    }
    pub fn edges_examined(&self) -> usize {
        self.edges_examined
    }

    /// Exact distance from `source` to the target in the declared weighted generator metric.
    pub fn distance(&self, source: &GroupElement) -> Result<u32, NavigationRefusal> {
        if !self.group.contains(source) {
            return Err(NavigationRefusal::SourceOutsideGroup);
        }
        self.distances
            .get(source)
            .copied()
            .ok_or(NavigationRefusal::Unreachable)
    }

    /// Maximum exact distance in the declared finite Cayley graph.
    pub fn diameter(&self) -> u32 {
        self.distances.values().copied().max().unwrap_or(0)
    }

    /// Every move that decreases the source distance by its declared cost.
    pub fn minimizing_fibre(
        &self,
        source: &GroupElement,
    ) -> Result<Vec<NavigationStep>, NavigationRefusal> {
        let distance = self.distance(source)?;
        let mut result = Vec::new();
        for movement in &self.expanded_moves {
            let next = source
                .then(&movement.element)
                .ok_or_else(|| NavigationRefusal::MoveOutsideGroup(movement.label.clone()))?;
            if self.distances.get(&next).is_some_and(|next_distance| {
                next_distance.checked_add(movement.cost) == Some(distance)
            }) {
                result.push(NavigationStep {
                    label: movement.label.clone(),
                    element: movement.element.clone(),
                    cost: movement.cost,
                });
            }
        }
        Ok(result)
    }

    /// Select the first declared minimizing step and return the complete optimal traversal.
    pub fn solve(&self, source: GroupElement) -> Result<NavigationSolution, NavigationRefusal> {
        let distance = self.distance(&source)?;
        let mut state = source.clone();
        let mut steps = Vec::new();
        let mut seen = BTreeSet::new();
        while state != self.target {
            if !seen.insert(state.clone()) {
                return Err(NavigationRefusal::ReconstructionOverflow);
            }
            let step = self
                .minimizing_fibre(&state)?
                .into_iter()
                .next()
                .ok_or(NavigationRefusal::Unreachable)?;
            state = state
                .then(&step.element)
                .ok_or(NavigationRefusal::ReconstructionOverflow)?;
            steps.push(step);
        }
        let minimizing_fibre_size = self
            .shortest_word_counts
            .get(&source)
            .cloned()
            .ok_or(NavigationRefusal::Unreachable)?;
        Ok(NavigationSolution {
            source,
            target: self.target.clone(),
            distance,
            steps,
            minimizing_fibre_size,
        })
    }
}

fn shortest_word_counts(
    target: &GroupElement,
    expanded_moves: &[NavigationMove],
    distances: &BTreeMap<GroupElement, u32>,
) -> Result<BTreeMap<GroupElement, BigUint>, NavigationRefusal> {
    let mut states = distances.keys().cloned().collect::<Vec<_>>();
    states.sort_by_key(|state| distances.get(state).copied().unwrap_or(u32::MAX));
    let mut counts = BTreeMap::from([(target.clone(), BigUint::one())]);
    for state in states.into_iter().filter(|state| state != target) {
        let distance = distances
            .get(&state)
            .copied()
            .ok_or(NavigationRefusal::Unreachable)?;
        let mut total = BigUint::zero();
        for movement in expanded_moves {
            let next = state
                .then(&movement.element)
                .ok_or_else(|| NavigationRefusal::MoveOutsideGroup(movement.label.clone()))?;
            if distances
                .get(&next)
                .and_then(|next_distance| next_distance.checked_add(movement.cost))
                == Some(distance)
            {
                total += counts
                    .get(&next)
                    .cloned()
                    .ok_or(NavigationRefusal::Unreachable)?;
            }
        }
        counts.insert(state, total);
    }
    Ok(counts)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overflowing_dominated_walk_does_not_refuse_a_representable_metric() {
        let flip = GroupElement::Permutation(vec![1, 0]);
        let group = StructureGroup::close([flip.clone()], 2).unwrap();
        let navigation = ExactGroupNavigation::new(
            group.clone(),
            group.identity().clone(),
            [NavigationMove::new("flip", flip.clone(), u32::MAX).unwrap()],
        )
        .unwrap();
        assert_eq!(navigation.distance(&flip).unwrap(), u32::MAX);
        assert_eq!(navigation.solve(flip).unwrap().distance, u32::MAX);
    }

    #[test]
    fn overflowing_candidate_can_be_replaced_by_a_later_shorter_path() {
        let group = alternating_four();
        let ordinary = moves();
        let expensive = ordinary[0].element.then(&ordinary[1].element).unwrap();
        let reference =
            ExactGroupNavigation::new(group.clone(), group.identity().clone(), ordinary.clone())
                .unwrap();
        let mut redundant = ordinary;
        redundant.push(NavigationMove::new("expensive", expensive, u32::MAX).unwrap());
        let actual =
            ExactGroupNavigation::new(group.clone(), group.identity().clone(), redundant).unwrap();
        for state in group.elements() {
            assert_eq!(actual.distance(state), reference.distance(state));
        }
    }

    fn alternating_four() -> StructureGroup {
        StructureGroup::close(
            [
                GroupElement::Permutation(vec![1, 2, 0, 3]),
                GroupElement::Permutation(vec![0, 2, 3, 1]),
            ],
            12,
        )
        .expect("the two even cycles close to A4")
    }

    fn moves() -> Vec<NavigationMove> {
        vec![
            NavigationMove::new("U", GroupElement::Permutation(vec![1, 2, 0, 3]), 1).unwrap(),
            NavigationMove::new("R", GroupElement::Permutation(vec![0, 2, 3, 1]), 1).unwrap(),
        ]
    }

    #[test]
    fn exact_policy_solves_every_a4_state_and_returns_a_retained_minimizing_fibre() {
        let group = alternating_four();
        let navigation =
            ExactGroupNavigation::new(group.clone(), group.identity().clone(), moves())
                .expect("navigation preprocessing");
        assert_eq!(navigation.states(), 12);
        assert!(navigation.diameter() > 0);
        for state in group.elements() {
            let solution = navigation
                .solve(state.clone())
                .expect("every A4 state is reachable");
            assert_eq!(solution.distance as usize, solution.steps.len());
            assert!(!solution.minimizing_fibre_size.is_zero());
            let mut landed = state.clone();
            for step in &solution.steps {
                landed = landed.then(&step.element).expect("policy step composes");
            }
            assert!(landed.is_identity());
        }
    }

    #[test]
    fn distances_agree_with_an_independent_unweighted_bfs_and_bellman_edges() {
        let group = alternating_four();
        let navigation =
            ExactGroupNavigation::new(group.clone(), group.identity().clone(), moves())
                .expect("navigation preprocessing");
        let mut distances = BTreeMap::from([(group.identity().clone(), 0u32)]);
        let mut queue = std::collections::VecDeque::from([group.identity().clone()]);
        let expanded = [
            GroupElement::Permutation(vec![1, 2, 0, 3]),
            GroupElement::Permutation(vec![0, 2, 3, 1]),
            GroupElement::Permutation(vec![2, 0, 1, 3]),
            GroupElement::Permutation(vec![0, 3, 1, 2]),
        ];
        while let Some(state) = queue.pop_front() {
            let distance = distances[&state];
            for movement in &expanded {
                let next = state.then(movement).unwrap();
                if !distances.contains_key(&next) {
                    distances.insert(next.clone(), distance + 1);
                    queue.push_back(next);
                }
            }
        }
        assert_eq!(distances, navigation.distances);
        for state in group.elements() {
            let fibre = navigation.minimizing_fibre(state).unwrap();
            assert!(fibre.iter().all(|step| {
                state
                    .then(&step.element)
                    .and_then(|next| navigation.distances.get(&next).copied())
                    == Some(navigation.distance(state).unwrap() - 1)
            }));
        }
    }

    #[test]
    fn incomplete_declared_move_set_is_refused_instead_of_reported_as_a_group_diameter() {
        let group = alternating_four();
        let error = ExactGroupNavigation::new(
            group,
            GroupElement::Permutation(vec![0, 1, 2, 3]),
            [NavigationMove::new("a", GroupElement::Permutation(vec![1, 2, 0, 3]), 1).unwrap()],
        )
        .unwrap_err();
        assert_eq!(
            error,
            NavigationRefusal::MoveSetDoesNotReachGroup {
                reached: 3,
                group_order: 12,
            }
        );
    }

    #[test]
    fn weighted_metric_is_retained_in_the_distance_and_policy() {
        let group = alternating_four();
        let navigation = ExactGroupNavigation::new(
            group.clone(),
            group.identity().clone(),
            vec![
                NavigationMove::new("U", GroupElement::Permutation(vec![1, 2, 0, 3]), 2).unwrap(),
                NavigationMove::new("R", GroupElement::Permutation(vec![0, 2, 3, 1]), 1).unwrap(),
            ],
        )
        .expect("weighted navigation preprocessing");
        let u = GroupElement::Permutation(vec![1, 2, 0, 3]);
        assert_eq!(navigation.distance(&u).unwrap(), 2);
        assert!(
            navigation
                .minimizing_fibre(&u)
                .unwrap()
                .iter()
                .any(|step| step.label == "U'" && step.cost == 2)
        );
    }
}
