//! Exact local realization modes and mode-relative closure.
//!
//! A mode is not a global scale flag or an executor setting.  It is the
//! contemporary tuple of boundary, coefficient law, and receiver distinction
//! under which one local realization is valid.  Several modes may coexist by
//! juxtaposition.  A transition exists only when a declared interaction
//! supplies transport between them.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// One exact local realization regime.
///
/// The three carriers remain generic because different ecologies have
/// different boundary, algebra, and receiver fibers.  Equality is structural:
/// two occurrences may reuse one admitted realization only when this complete
/// signature agrees.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ExactModeSignature<B, C, R> {
    pub boundary: B,
    pub coefficients: C,
    pub receiver: R,
}

impl<B, C, R> ExactModeSignature<B, C, R> {
    pub fn new(boundary: B, coefficients: C, receiver: R) -> Self {
        Self {
            boundary,
            coefficients,
            receiver,
        }
    }
}

/// The topology-changing species a declared interaction may realize.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ModeTransportKind {
    Rechart,
    Localization,
    Gluing,
    Quotient,
    Refinement,
    Branch,
    SingularRankChange,
    Return,
}

/// Why a proposed transport cannot yet enter exact standing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ModeTransportObstruction {
    InteractionUndeclared,
    CarrierNotInvertible,
    RankChanged,
    RemainderUncertified,
    ReceiverDistinctionLost,
}

/// Comparison of the two causal paths around a mode-transport square.
///
/// `Exact` means evolve-then-transport and transport-then-evolve agree.
/// `Residual` preserves their directed exact difference.  `Open` records the
/// precise missing law instead of silently identifying the paths.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModeCommutation<R> {
    Exact,
    Residual(R),
    Open(ModeTransportObstruction),
}

/// A declared transport between two modes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactModeTransport<M, T, R> {
    pub source: M,
    pub target: M,
    pub kind: ModeTransportKind,
    pub transport: T,
    pub commutation: ModeCommutation<R>,
}

/// Receiver-relative degree of separation along one transported path.
///
/// These grades are deliberately plural.  Adding them componentwise composes
/// paths without collapsing causal depth, incidence, local grain, arithmetic
/// rank, mode crossings, and return holonomy into one scalar distance.
#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct SeparationDegree {
    pub causal_depth: u64,
    pub incidence_grade: u64,
    pub grain: u64,
    pub valuation_rank: u64,
    pub mode_crossings: u64,
    pub return_holonomy: u64,
}

impl SeparationDegree {
    pub fn compose(self, next: Self) -> Result<Self, ModeError> {
        Ok(Self {
            causal_depth: self
                .causal_depth
                .checked_add(next.causal_depth)
                .ok_or(ModeError::DegreeOverflow)?,
            incidence_grade: self
                .incidence_grade
                .checked_add(next.incidence_grade)
                .ok_or(ModeError::DegreeOverflow)?,
            grain: self
                .grain
                .checked_add(next.grain)
                .ok_or(ModeError::DegreeOverflow)?,
            valuation_rank: self
                .valuation_rank
                .checked_add(next.valuation_rank)
                .ok_or(ModeError::DegreeOverflow)?,
            mode_crossings: self
                .mode_crossings
                .checked_add(next.mode_crossings)
                .ok_or(ModeError::DegreeOverflow)?,
            return_holonomy: self
                .return_holonomy
                .checked_add(next.return_holonomy)
                .ok_or(ModeError::DegreeOverflow)?,
        })
    }
}

/// A mode's physical realization is admitted once with an exact witness and
/// subsequently addressed by structural identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeAdmissionLedger<M, W> {
    admitted: BTreeMap<M, W>,
}

impl<M, W> Default for ModeAdmissionLedger<M, W> {
    fn default() -> Self {
        Self {
            admitted: BTreeMap::new(),
        }
    }
}

impl<M: Ord, W> ModeAdmissionLedger<M, W> {
    pub fn admission(&self, mode: &M) -> Option<&W> {
        self.admitted.get(mode)
    }

    pub fn contains(&self, mode: &M) -> bool {
        self.admitted.contains_key(mode)
    }

    pub fn len(&self) -> usize {
        self.admitted.len()
    }

    pub fn is_empty(&self) -> bool {
        self.admitted.is_empty()
    }

    /// Admit a previously unseen structural mode.
    ///
    /// Replacing an existing witness would rewrite the causal basis of reuse,
    /// so repeated admission is refused rather than overwritten.
    pub fn admit(&mut self, mode: M, witness: W) -> Result<(), ModeError> {
        if self.admitted.contains_key(&mode) {
            return Err(ModeError::ModeAlreadyAdmitted);
        }
        self.admitted.insert(mode, witness);
        Ok(())
    }
}

/// Deterministic equivalence closure over receiver identities.
///
/// This owns the recurring union/find machinery used when exact local
/// relations force identities together.  It does not invent those relations;
/// only explicitly supplied joins change the closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquivalenceClosure<K> {
    keys: Vec<K>,
    indices: BTreeMap<K, usize>,
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl<K: Clone + Ord> EquivalenceClosure<K> {
    pub fn new(keys: impl IntoIterator<Item = K>) -> Result<Self, ModeError> {
        let mut retained = Vec::new();
        let mut indices = BTreeMap::new();
        for key in keys {
            let index = retained.len();
            if indices.insert(key.clone(), index).is_some() {
                return Err(ModeError::RepeatedClosureMember);
            }
            retained.push(key);
        }
        Ok(Self {
            parent: (0..retained.len()).collect(),
            rank: vec![0; retained.len()],
            keys: retained,
            indices,
        })
    }

    pub fn join(&mut self, left: &K, right: &K) -> Result<(), ModeError> {
        let left = *self
            .indices
            .get(left)
            .ok_or(ModeError::MissingClosureMember)?;
        let right = *self
            .indices
            .get(right)
            .ok_or(ModeError::MissingClosureMember)?;
        let left = self.root(left);
        let right = self.root(right);
        if left == right {
            return Ok(());
        }
        match self.rank[left].cmp(&self.rank[right]) {
            std::cmp::Ordering::Less => self.parent[left] = right,
            std::cmp::Ordering::Greater => self.parent[right] = left,
            std::cmp::Ordering::Equal => {
                self.parent[right] = left;
                self.rank[left] = self.rank[left]
                    .checked_add(1)
                    .ok_or(ModeError::ClosureRankOverflow)?;
            }
        }
        Ok(())
    }

    pub fn classes(mut self) -> Vec<Vec<K>> {
        let mut grouped = BTreeMap::<usize, Vec<K>>::new();
        for index in 0..self.keys.len() {
            let root = self.root(index);
            grouped
                .entry(root)
                .or_default()
                .push(self.keys[index].clone());
        }
        let mut classes = grouped.into_values().collect::<Vec<_>>();
        for class in &mut classes {
            class.sort();
        }
        classes.sort_by(|left, right| left.first().cmp(&right.first()));
        classes
    }

    fn root(&mut self, mut index: usize) -> usize {
        while self.parent[index] != index {
            self.parent[index] = self.parent[self.parent[index]];
            index = self.parent[index];
        }
        index
    }
}

#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum ModeError {
    #[error("an exact mode was admitted twice")]
    ModeAlreadyAdmitted,
    #[error("a receiver-relative separation degree overflowed")]
    DegreeOverflow,
    #[error("an equivalence-closure member was repeated")]
    RepeatedClosureMember,
    #[error("an equivalence join named a member outside the closure")]
    MissingClosureMember,
    #[error("an equivalence-closure rank overflowed")]
    ClosureRankOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_is_independent_of_join_order() {
        let mut first = EquivalenceClosure::new([1_u64, 2, 3, 4]).unwrap();
        first.join(&1, &2).unwrap();
        first.join(&3, &4).unwrap();
        first.join(&2, &3).unwrap();

        let mut second = EquivalenceClosure::new([1_u64, 2, 3, 4]).unwrap();
        second.join(&2, &3).unwrap();
        second.join(&4, &3).unwrap();
        second.join(&2, &1).unwrap();
        assert_eq!(first.classes(), second.classes());
    }

    #[test]
    fn separation_composition_does_not_collapse_its_grades() {
        let first = SeparationDegree {
            causal_depth: 2,
            incidence_grade: 1,
            grain: 5,
            valuation_rank: 0,
            mode_crossings: 1,
            return_holonomy: 0,
        };
        let second = SeparationDegree {
            causal_depth: 1,
            incidence_grade: 3,
            grain: 0,
            valuation_rank: 2,
            mode_crossings: 0,
            return_holonomy: 1,
        };
        assert_eq!(
            first.compose(second).unwrap(),
            SeparationDegree {
                causal_depth: 3,
                incidence_grade: 4,
                grain: 5,
                valuation_rank: 2,
                mode_crossings: 1,
                return_holonomy: 1,
            }
        );
    }

    #[test]
    fn an_open_transport_does_not_claim_a_transition_law() {
        let transport = ExactModeTransport {
            source: 1_u8,
            target: 2_u8,
            kind: ModeTransportKind::SingularRankChange,
            transport: (),
            commutation: ModeCommutation::<()>::Open(ModeTransportObstruction::RankChanged),
        };
        assert!(matches!(transport.commutation, ModeCommutation::Open(_)));
    }
}
