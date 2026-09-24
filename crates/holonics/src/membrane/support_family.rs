//! Exact factorized support carried by one live constituent.
//!
//! A support factor is not stored as the repeatedly expanded union of every boundary which
//! caused it.  Leaf expressions name local boundary germs.  A caused join retains its input
//! expressions and only the newly emitted seam boundaries.  The canonical node table is a
//! persistence/execution representation of that expression DAG; active roots are the actual
//! receiver-addressable factors.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SupportFamilyError {
    Topology,
    Extent,
    InvalidWire,
}

/// Historical/source-facing declaration of one explicit support coface.
///
/// Production standing immediately converts these declarations into [`LiveSupportFamily`].
/// They remain useful at a world membrane and for bounded observer enumeration, but they are not
/// the production carrier.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LiveSupportSection {
    boundaries: Vec<u32>,
}

impl LiveSupportSection {
    pub fn new(boundaries: Vec<u32>) -> Self {
        Self { boundaries }
    }

    pub fn boundaries(&self) -> &[u32] {
        &self.boundaries
    }
}

/// Structural expression for one support factor. `causes` are prior factor expressions retained
/// by a caused join; `boundaries` are the boundaries emitted directly at this expression node.
/// A leaf has no causes and at least one direct boundary.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct LiveSupportExpression {
    causes: Vec<LiveSupportExpression>,
    boundaries: Vec<u32>,
}

impl LiveSupportExpression {
    pub(crate) fn leaf(boundaries: Vec<u32>) -> Result<Self, SupportFamilyError> {
        Self::new(Vec::new(), boundaries)
    }

    pub(crate) fn join(
        causes: Vec<LiveSupportExpression>,
        boundaries: Vec<u32>,
    ) -> Result<Self, SupportFamilyError> {
        Self::new(causes, boundaries)
    }

    fn new(
        mut causes: Vec<LiveSupportExpression>,
        mut boundaries: Vec<u32>,
    ) -> Result<Self, SupportFamilyError> {
        boundaries.sort_unstable();
        boundaries.dedup();
        causes.sort();
        if causes.is_empty() && boundaries.is_empty() {
            return Err(SupportFamilyError::Topology);
        }
        Ok(Self { causes, boundaries })
    }

    pub(crate) fn rebased(&self, offset: u32) -> Result<Self, SupportFamilyError> {
        let causes = self
            .causes
            .iter()
            .map(|cause| cause.rebased(offset))
            .collect::<Result<Vec<_>, _>>()?;
        let boundaries = self
            .boundaries
            .iter()
            .map(|boundary| {
                boundary
                    .checked_add(offset)
                    .ok_or(SupportFamilyError::Extent)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(causes, boundaries)
    }

    pub(crate) fn remapped(
        &self,
        boundary_map: &[Option<u32>],
    ) -> Result<Option<Self>, SupportFamilyError> {
        let mut causes = Vec::new();
        causes
            .try_reserve_exact(self.causes.len())
            .map_err(|_| SupportFamilyError::Extent)?;
        for cause in &self.causes {
            let Some(cause) = cause.remapped(boundary_map)? else {
                return Ok(None);
            };
            causes.push(cause);
        }
        let mut boundaries = Vec::new();
        boundaries
            .try_reserve_exact(self.boundaries.len())
            .map_err(|_| SupportFamilyError::Extent)?;
        for boundary in &self.boundaries {
            let Some(mapped) = boundary_map
                .get(usize::try_from(*boundary).map_err(|_| SupportFamilyError::Extent)?)
                .ok_or(SupportFamilyError::Topology)?
            else {
                return Ok(None);
            };
            boundaries.push(*mapped);
        }
        Ok(Some(Self::new(causes, boundaries)?))
    }

    pub(crate) fn resolved_boundaries(&self) -> Result<Vec<u32>, SupportFamilyError> {
        let mut boundaries = self.boundaries.clone();
        for cause in &self.causes {
            boundaries.extend(cause.resolved_boundaries()?);
        }
        boundaries.sort_unstable();
        boundaries.dedup();
        if boundaries.is_empty() {
            return Err(SupportFamilyError::Topology);
        }
        Ok(boundaries)
    }

    fn depth(&self) -> Result<u32, SupportFamilyError> {
        let child = self
            .causes
            .iter()
            .map(Self::depth)
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .max()
            .unwrap_or(0);
        if self.causes.is_empty() {
            Ok(0)
        } else {
            child.checked_add(1).ok_or(SupportFamilyError::Extent)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LiveSupportNode {
    causes: Vec<u32>,
    boundaries: Vec<u32>,
}

/// Canonical exact factor family. The node table is topological, structurally deduplicated, and
/// independent of expression insertion order. Roots are the active local factors; non-root nodes
/// remain as their inspectable causal lineage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveSupportFamily {
    nodes: Vec<LiveSupportNode>,
    roots: Vec<u32>,
}

impl LiveSupportFamily {
    pub fn from_sections(sections: Vec<LiveSupportSection>) -> Result<Self, SupportFamilyError> {
        let expressions = sections
            .into_iter()
            .map(|section| LiveSupportExpression::leaf(section.boundaries))
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_expressions(expressions)
    }

    pub(crate) fn from_expressions(
        mut roots: Vec<LiveSupportExpression>,
    ) -> Result<Self, SupportFamilyError> {
        roots.sort();
        roots.dedup();
        if roots.is_empty() {
            return Err(SupportFamilyError::Topology);
        }

        fn collect(expression: &LiveSupportExpression, all: &mut BTreeSet<LiveSupportExpression>) {
            if !all.insert(expression.clone()) {
                return;
            }
            for cause in &expression.causes {
                collect(cause, all);
            }
        }

        let mut all = BTreeSet::new();
        for root in &roots {
            collect(root, &mut all);
        }
        let mut ordered = all
            .into_iter()
            .map(|expression| Ok((expression.depth()?, expression)))
            .collect::<Result<Vec<_>, SupportFamilyError>>()?;
        ordered.sort();

        let mut address = BTreeMap::new();
        for (at, (_, expression)) in ordered.iter().enumerate() {
            address.insert(
                expression.clone(),
                u32::try_from(at).map_err(|_| SupportFamilyError::Extent)?,
            );
        }

        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(ordered.len())
            .map_err(|_| SupportFamilyError::Extent)?;
        for (_, expression) in &ordered {
            let causes = expression
                .causes
                .iter()
                .map(|cause| {
                    address
                        .get(cause)
                        .copied()
                        .ok_or(SupportFamilyError::Topology)
                })
                .collect::<Result<Vec<_>, _>>()?;
            nodes.push(LiveSupportNode {
                causes,
                boundaries: expression.boundaries.clone(),
            });
        }
        let mut roots = roots
            .iter()
            .map(|root| {
                address
                    .get(root)
                    .copied()
                    .ok_or(SupportFamilyError::Topology)
            })
            .collect::<Result<Vec<_>, _>>()?;
        roots.sort_unstable();
        roots.dedup();
        let result = Self { nodes, roots };
        result.validate()?;
        Ok(result)
    }

    pub fn factor_count(&self) -> usize {
        self.roots.len()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn factor_boundaries(&self, at: usize) -> Result<Vec<u32>, SupportFamilyError> {
        self.factor_boundary_sets()?
            .get(at)
            .cloned()
            .ok_or(SupportFamilyError::Topology)
    }

    /// Resolve every active factor through one topological node-table traversal. This is a
    /// rebuildable execution quotient; the canonical standing identity remains the factor DAG.
    pub fn factor_boundary_sets(&self) -> Result<Vec<Vec<u32>>, SupportFamilyError> {
        let mut node_boundaries = Vec::<Vec<u32>>::new();
        node_boundaries
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| SupportFamilyError::Extent)?;
        for (at, node) in self.nodes.iter().enumerate() {
            let mut boundaries = node.boundaries.clone();
            for cause in &node.causes {
                let cause_at = usize::try_from(*cause).map_err(|_| SupportFamilyError::Extent)?;
                if cause_at >= at {
                    return Err(SupportFamilyError::Topology);
                }
                boundaries.extend_from_slice(
                    node_boundaries
                        .get(cause_at)
                        .ok_or(SupportFamilyError::Topology)?,
                );
            }
            boundaries.sort_unstable();
            boundaries.dedup();
            if boundaries.is_empty() {
                return Err(SupportFamilyError::Topology);
            }
            node_boundaries.push(boundaries);
        }
        self.roots
            .iter()
            .map(|root| {
                node_boundaries
                    .get(usize::try_from(*root).map_err(|_| SupportFamilyError::Extent)?)
                    .cloned()
                    .ok_or(SupportFamilyError::Topology)
            })
            .collect()
    }

    pub fn explicit_sections(&self) -> Result<Vec<LiveSupportSection>, SupportFamilyError> {
        self.factor_boundary_sets()?
            .into_iter()
            .map(|boundaries| Ok(LiveSupportSection::new(boundaries)))
            .collect()
    }

    pub(crate) fn root_expressions(
        &self,
    ) -> Result<Vec<LiveSupportExpression>, SupportFamilyError> {
        let expressions = self.node_expressions()?;
        self.roots
            .iter()
            .map(|root| {
                expressions
                    .get(usize::try_from(*root).map_err(|_| SupportFamilyError::Extent)?)
                    .cloned()
                    .ok_or(SupportFamilyError::Topology)
            })
            .collect()
    }

    fn node_expressions(&self) -> Result<Vec<LiveSupportExpression>, SupportFamilyError> {
        let mut expressions = Vec::new();
        expressions
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| SupportFamilyError::Extent)?;
        for (at, node) in self.nodes.iter().enumerate() {
            let mut causes = Vec::new();
            causes
                .try_reserve_exact(node.causes.len())
                .map_err(|_| SupportFamilyError::Extent)?;
            for cause in &node.causes {
                let cause_at = usize::try_from(*cause).map_err(|_| SupportFamilyError::Extent)?;
                if cause_at >= at {
                    return Err(SupportFamilyError::Topology);
                }
                causes.push(
                    expressions
                        .get(cause_at)
                        .cloned()
                        .ok_or(SupportFamilyError::Topology)?,
                );
            }
            expressions.push(LiveSupportExpression::new(causes, node.boundaries.clone())?);
        }
        Ok(expressions)
    }

    pub(crate) fn rebased(&self, offset: u32) -> Result<Self, SupportFamilyError> {
        Self::from_expressions(
            self.root_expressions()?
                .iter()
                .map(|expression| expression.rebased(offset))
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    /// Restrict every complete active factor through a boundary map. A factor departs when any
    /// one of its caused boundaries is absent. Every selected boundary not retained by a complete
    /// factor becomes one new leaf, preserving the complete outgoing cover.
    pub(crate) fn remapped_complete(
        &self,
        boundary_map: &[Option<u32>],
        selected_count: usize,
    ) -> Result<Self, SupportFamilyError> {
        let mut expressions = Vec::new();
        for expression in self.root_expressions()? {
            if let Some(mapped) = expression.remapped(boundary_map)? {
                expressions.push(mapped);
            }
        }
        let mut covered = vec![false; selected_count];
        for expression in &expressions {
            for boundary in expression.resolved_boundaries()? {
                let boundary = usize::try_from(boundary).map_err(|_| SupportFamilyError::Extent)?;
                let slot = covered
                    .get_mut(boundary)
                    .ok_or(SupportFamilyError::Topology)?;
                *slot = true;
            }
        }
        for (at, covered) in covered.into_iter().enumerate() {
            if !covered {
                expressions.push(LiveSupportExpression::leaf(vec![
                    u32::try_from(at).map_err(|_| SupportFamilyError::Extent)?
                ])?);
            }
        }
        Self::from_expressions(expressions)
    }

    pub(crate) fn all_factor_boundaries(&self) -> Result<Vec<u32>, SupportFamilyError> {
        let mut selected = Vec::new();
        for boundaries in self.factor_boundary_sets()? {
            selected.extend(boundaries);
        }
        selected.sort_unstable();
        selected.dedup();
        Ok(selected)
    }

    pub fn native_word_len(&self) -> Result<usize, SupportFamilyError> {
        let mut words = 2usize;
        for node in &self.nodes {
            words = words
                .checked_add(2)
                .and_then(|value| value.checked_add(node.causes.len()))
                .and_then(|value| value.checked_add(node.boundaries.len()))
                .ok_or(SupportFamilyError::Extent)?;
        }
        words
            .checked_add(self.roots.len())
            .ok_or(SupportFamilyError::Extent)
    }

    pub fn direct_boundary_entries(&self) -> usize {
        self.nodes.iter().map(|node| node.boundaries.len()).sum()
    }

    pub fn cause_edges(&self) -> usize {
        self.nodes.iter().map(|node| node.causes.len()).sum()
    }

    pub fn resolved_active_boundary_entries(&self) -> Result<usize, SupportFamilyError> {
        self.factor_boundary_sets()?
            .into_iter()
            .try_fold(0usize, |total, boundaries| {
                total
                    .checked_add(boundaries.len())
                    .ok_or(SupportFamilyError::Extent)
            })
    }

    pub(crate) fn write_native_words(
        &self,
        words: &mut Vec<u32>,
    ) -> Result<(), SupportFamilyError> {
        self.validate()?;
        words.push(u32::try_from(self.nodes.len()).map_err(|_| SupportFamilyError::Extent)?);
        for node in &self.nodes {
            words.push(u32::try_from(node.causes.len()).map_err(|_| SupportFamilyError::Extent)?);
            words.extend_from_slice(&node.causes);
            words.push(
                u32::try_from(node.boundaries.len()).map_err(|_| SupportFamilyError::Extent)?,
            );
            words.extend_from_slice(&node.boundaries);
        }
        words.push(u32::try_from(self.roots.len()).map_err(|_| SupportFamilyError::Extent)?);
        words.extend_from_slice(&self.roots);
        Ok(())
    }

    pub(crate) fn read_native_words(
        words: &[u32],
        cursor: &mut usize,
    ) -> Result<Self, SupportFamilyError> {
        fn take(words: &[u32], cursor: &mut usize) -> Result<u32, SupportFamilyError> {
            let word = words
                .get(*cursor)
                .copied()
                .ok_or(SupportFamilyError::InvalidWire)?;
            *cursor = cursor
                .checked_add(1)
                .ok_or(SupportFamilyError::InvalidWire)?;
            Ok(word)
        }

        let node_count =
            usize::try_from(take(words, cursor)?).map_err(|_| SupportFamilyError::InvalidWire)?;
        let mut nodes = Vec::with_capacity(node_count);
        for _ in 0..node_count {
            let cause_count = usize::try_from(take(words, cursor)?)
                .map_err(|_| SupportFamilyError::InvalidWire)?;
            let mut causes = Vec::with_capacity(cause_count);
            for _ in 0..cause_count {
                causes.push(take(words, cursor)?);
            }
            let boundary_count = usize::try_from(take(words, cursor)?)
                .map_err(|_| SupportFamilyError::InvalidWire)?;
            let mut boundaries = Vec::with_capacity(boundary_count);
            for _ in 0..boundary_count {
                boundaries.push(take(words, cursor)?);
            }
            nodes.push(LiveSupportNode { causes, boundaries });
        }
        let root_count =
            usize::try_from(take(words, cursor)?).map_err(|_| SupportFamilyError::InvalidWire)?;
        let mut roots = Vec::with_capacity(root_count);
        for _ in 0..root_count {
            roots.push(take(words, cursor)?);
        }
        let parsed = Self { nodes, roots };
        parsed
            .validate()
            .map_err(|_| SupportFamilyError::InvalidWire)?;
        let canonical = Self::from_expressions(
            parsed
                .root_expressions()
                .map_err(|_| SupportFamilyError::InvalidWire)?,
        )
        .map_err(|_| SupportFamilyError::InvalidWire)?;
        if canonical != parsed {
            return Err(SupportFamilyError::InvalidWire);
        }
        Ok(parsed)
    }

    pub(crate) fn validate_for_boundaries(
        &self,
        boundary_count: usize,
    ) -> Result<(), SupportFamilyError> {
        self.validate()?;
        let mut covered = vec![false; boundary_count];
        for boundaries in self.factor_boundary_sets()? {
            for boundary in boundaries {
                let boundary = usize::try_from(boundary).map_err(|_| SupportFamilyError::Extent)?;
                let slot = covered
                    .get_mut(boundary)
                    .ok_or(SupportFamilyError::Topology)?;
                *slot = true;
            }
        }
        if covered.iter().any(|covered| !covered) {
            return Err(SupportFamilyError::Topology);
        }
        Ok(())
    }

    fn validate(&self) -> Result<(), SupportFamilyError> {
        if self.nodes.is_empty()
            || self.roots.is_empty()
            || self.roots.windows(2).any(|pair| pair[0] >= pair[1])
            || self.nodes.iter().any(|node| {
                node.boundaries.windows(2).any(|pair| pair[0] >= pair[1])
                    || (node.causes.is_empty() && node.boundaries.is_empty())
            })
        {
            return Err(SupportFamilyError::Topology);
        }
        for (at, node) in self.nodes.iter().enumerate() {
            if node.causes.windows(2).any(|pair| pair[0] > pair[1])
                || node
                    .causes
                    .iter()
                    .any(|cause| usize::try_from(*cause).ok().is_none_or(|cause| cause >= at))
            {
                return Err(SupportFamilyError::Topology);
            }
        }
        if self.roots.iter().any(|root| {
            usize::try_from(*root)
                .ok()
                .is_none_or(|root| root >= self.nodes.len())
        }) {
            return Err(SupportFamilyError::Topology);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{LiveSupportExpression, LiveSupportFamily, LiveSupportSection};

    #[test]
    fn factor_order_is_gauge_and_join_retains_causes() {
        let left = LiveSupportExpression::leaf(vec![0, 1]).unwrap();
        let right = LiveSupportExpression::leaf(vec![2]).unwrap();
        let joined =
            LiveSupportExpression::join(vec![right.clone(), left.clone()], vec![3]).unwrap();
        let first =
            LiveSupportFamily::from_expressions(vec![joined.clone(), left.clone()]).unwrap();
        let second = LiveSupportFamily::from_expressions(vec![left, joined]).unwrap();
        assert_eq!(first, second);
        assert_eq!(first.factor_count(), 2);
        assert_eq!(first.factor_boundaries(1).unwrap(), vec![0, 1, 2, 3]);
        assert_eq!(first.node_count(), 3);
    }

    #[test]
    fn native_words_are_exact_and_canonical() {
        let family = LiveSupportFamily::from_sections(vec![
            LiveSupportSection::new(vec![2]),
            LiveSupportSection::new(vec![0, 1]),
        ])
        .unwrap();
        let mut words = Vec::new();
        family.write_native_words(&mut words).unwrap();
        let mut cursor = 0;
        let reopened = LiveSupportFamily::read_native_words(&words, &mut cursor).unwrap();
        assert_eq!(cursor, words.len());
        assert_eq!(family, reopened);
    }

    #[test]
    fn complete_restriction_preserves_factors_and_founds_uncovered_leaves() {
        let family = LiveSupportFamily::from_sections(vec![
            LiveSupportSection::new(vec![0, 1]),
            LiveSupportSection::new(vec![2]),
        ])
        .unwrap();
        let restricted = family
            .remapped_complete(&[Some(0), None, Some(1)], 2)
            .unwrap();
        assert_eq!(
            restricted.explicit_sections().unwrap(),
            vec![
                LiveSupportSection::new(vec![0]),
                LiveSupportSection::new(vec![1]),
            ]
        );
    }

    #[test]
    fn recurrent_joins_grow_as_a_factor_dag_and_resolve_to_the_exact_flat_cover() {
        const JOINS: u32 = 64;
        let mut root = LiveSupportExpression::leaf(vec![0]).unwrap();
        for at in 0..JOINS {
            let leaf = LiveSupportExpression::leaf(vec![1 + at]).unwrap();
            root = LiveSupportExpression::join(vec![root, leaf], vec![1 + JOINS + at]).unwrap();
        }
        let factorized = LiveSupportFamily::from_expressions(vec![root]).unwrap();
        let expected_boundaries = (0..=2 * JOINS).collect::<Vec<_>>();
        let explicit = LiveSupportFamily::from_sections(vec![LiveSupportSection::new(
            expected_boundaries.clone(),
        )])
        .unwrap();

        assert_eq!(factorized.factor_count(), 1);
        assert_eq!(factorized.node_count(), (2 * JOINS + 1) as usize);
        assert_eq!(factorized.cause_edges(), (2 * JOINS) as usize);
        assert_eq!(
            factorized.direct_boundary_entries(),
            (2 * JOINS + 1) as usize
        );
        assert_eq!(
            factorized.factor_boundaries(0).unwrap(),
            expected_boundaries
        );
        assert_eq!(
            factorized.factor_boundary_sets().unwrap(),
            explicit.factor_boundary_sets().unwrap()
        );
        assert!(factorized.native_word_len().unwrap() < 9 * factorized.node_count());
    }
}
