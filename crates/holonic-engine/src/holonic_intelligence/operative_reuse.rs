//! Resident reuse of complete numerical segments, not of native occurrences or learning returns.
//!
//! The immutable graph supplies dependencies. A changed occurrence chart invalidates its lookup
//! descendants; an actual morphology mutation invalidates that population's descendants. No
//! numerical zero, selected receiver, digest, or equality of names can establish independence.
//! Successful sections move between current use and this cache; they are never cloned.

use super::{
    full_operation::ContemporaryCarrier,
    operative_segment::{segments, SegmentOutcome},
    NativeCarrierOrdinal, NativeFullOperatorEcology, NativeOperationPrimitive, NativeOperatorNode,
    NativeSuccessorProjection, NativeTensorOrdinal,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct NativeForwardReuseCensus {
    pub indexed_operations: usize,
    pub indexed_segments: usize,
    pub indexed_dependencies: usize,
    pub dependency_edges_visited: u64,
    pub invalidated_segments: u64,
    pub reused_segments: u64,
    pub reused_operations: u64,
    pub recomputed_segments: u64,
    pub pressure_evictions: u64,
    pub retained_octets: u64,
    pub peak_retained_octets: u64,
    /// Input-word payload of retained numerical origins, excluding map/allocator overhead.
    pub input_lineage_octets: u64,
}

struct SegmentDependency {
    start: usize,
    end: usize,
    outputs: Vec<NativeCarrierOrdinal>,
    successors: Vec<usize>,
}

/// An apparatus index over exact input incidences; canonical numerical segments are its reuse
/// grain because changing capture boundaries can change measured admission/enclosure bounds.
struct DependencyIndex {
    segments: Vec<SegmentDependency>,
    by_start: BTreeMap<usize, usize>,
    population_users: BTreeMap<NativeTensorOrdinal, BTreeSet<usize>>,
    occurrence_users: BTreeSet<usize>,
}

impl DependencyIndex {
    fn found(operations: &[NativeOperatorNode]) -> Self {
        let mut result = Self {
            segments: Vec::new(),
            by_start: BTreeMap::new(),
            population_users: BTreeMap::new(),
            occurrence_users: BTreeSet::new(),
        };
        let mut producers = BTreeMap::new();
        let mut edges = BTreeSet::new();
        for (start, end) in segments(operations) {
            let segment = result.segments.len();
            result.by_start.insert(start, segment);
            let mut outputs = Vec::new();
            for operation in &operations[start..end] {
                for input in &operation.inputs {
                    if let Some(previous) = producers.get(input).copied() {
                        if previous != segment {
                            edges.insert((previous, segment));
                        }
                    }
                }
                for population in &operation.coefficients {
                    result
                        .population_users
                        .entry(*population)
                        .or_default()
                        .insert(segment);
                }
                if matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. }) {
                    result.occurrence_users.insert(segment);
                }
                producers.insert(operation.output, segment);
                outputs.push(operation.output);
            }
            result.segments.push(SegmentDependency {
                start,
                end,
                outputs,
                successors: Vec::new(),
            });
        }
        for (before, after) in edges {
            result.segments[before].successors.push(after);
        }
        result
    }

    fn closure(&self, seeds: impl IntoIterator<Item = usize>) -> (BTreeSet<usize>, u64) {
        let mut visited = BTreeSet::new();
        let mut queue: VecDeque<_> = seeds.into_iter().collect();
        let mut edges = 0;
        while let Some(at) = queue.pop_front() {
            if !visited.insert(at) {
                continue;
            }
            for next in &self.segments[at].successors {
                edges += 1;
                queue.push_back(*next);
            }
        }
        (visited, edges)
    }
}

#[derive(Clone)]
struct NumericalReturn {
    admitted: u32,
    projection: NativeSuccessorProjection,
    origin: NativeNumericalOrigin,
}

/// The addressed prior computation retained by a numerical reuse passage. Its occurrence is
/// scoped to this one continuing session, whose immutable ecology supplies the actual operator
/// and both input/output boundary maps. The entering word is retained, not hashed or replaced
/// by an equality of counts. This is not the identity of the new native occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeNumericalOrigin {
    pub occurrence: u64,
    pub operation: u32,
    pub row_addresses: Vec<u32>,
}

pub(super) struct NativeForwardReuse<'chart> {
    index: DependencyIndex,
    standing: BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>,
    numerical: BTreeMap<NativeCarrierOrdinal, NumericalReturn>,
    census: NativeForwardReuseCensus,
}

impl<'chart> NativeForwardReuse<'chart> {
    pub(super) fn found(ecology: &NativeFullOperatorEcology) -> Self {
        let operations = &ecology.operations[..ecology.operations.len().saturating_sub(5)];
        let index = DependencyIndex::found(operations);
        let census = NativeForwardReuseCensus {
            indexed_operations: operations.len(),
            indexed_segments: index.segments.len(),
            indexed_dependencies: index.segments.iter().map(|s| s.successors.len()).sum(),
            ..Default::default()
        };
        Self {
            index,
            standing: BTreeMap::new(),
            numerical: BTreeMap::new(),
            census,
        }
    }

    pub(super) fn census(&self) -> NativeForwardReuseCensus {
        let mut census = self.census.clone();
        census.input_lineage_octets = self
            .numerical
            .values()
            .map(|n| n.origin.row_addresses.len() as u64 * 4)
            .sum();
        census
    }

    pub(super) fn occurrence_changed(&mut self) {
        self.invalidate(self.index.occurrence_users.clone());
    }

    pub(super) fn morphology_changed(
        &mut self,
        populations: impl IntoIterator<Item = NativeTensorOrdinal>,
    ) {
        let seeds: BTreeSet<_> = populations
            .into_iter()
            .flat_map(|population| {
                self.index
                    .population_users
                    .get(&population)
                    .into_iter()
                    .flatten()
                    .copied()
            })
            .collect();
        self.invalidate(seeds);
    }

    fn invalidate(&mut self, seeds: BTreeSet<usize>) {
        let (affected, edges) = self.index.closure(seeds);
        self.census.dependency_edges_visited += edges;
        for at in affected {
            if self.index.segments[at]
                .outputs
                .iter()
                .any(|output| self.numerical.contains_key(output))
            {
                self.census.invalidated_segments += 1;
            }
            self.discard_segment(at);
        }
    }

    fn discard_segment(&mut self, at: usize) {
        for output in &self.index.segments[at].outputs {
            self.numerical.remove(output);
            if let Some(held) = self.standing.remove(output) {
                self.census.retained_octets -= held.section.resident_octets();
            }
        }
    }

    pub(super) fn take_segment(
        &mut self,
        start: usize,
        end: usize,
    ) -> Option<(Vec<SegmentOutcome<'chart>>, Vec<NativeNumericalOrigin>)> {
        let at = *self.index.by_start.get(&start)?;
        let segment = &self.index.segments[at];
        if segment.start != start
            || segment.end != end
            || segment.outputs.iter().any(|output| {
                !self.standing.contains_key(output) || !self.numerical.contains_key(output)
            })
        {
            // A missing carrier is an ordinary cache miss, not a zero or an obstruction.
            self.discard_segment(at);
            self.census.recomputed_segments += 1;
            return None;
        }
        let mut outcomes = Vec::with_capacity(end - start);
        let mut origins = Vec::with_capacity(end - start);
        for output in &segment.outputs {
            let carrier = self
                .standing
                .remove(output)
                .expect("complete retained segment");
            let numerical = &self.numerical[output];
            origins.push(numerical.origin.clone());
            self.census.retained_octets -= carrier.section.resident_octets();
            outcomes.push(SegmentOutcome {
                output: *output,
                carrier,
                admitted_octaves: numerical.admitted,
                projection: numerical.projection.clone(),
            });
        }
        self.census.reused_segments += 1;
        self.census.reused_operations += outcomes.len() as u64;
        Some((outcomes, origins))
    }

    pub(super) fn remember(
        &mut self,
        outcome: &SegmentOutcome<'chart>,
        occurrence: u64,
        operation: u32,
        row_addresses: &[u32],
    ) {
        self.numerical.insert(
            outcome.output,
            NumericalReturn {
                admitted: outcome.admitted_octaves,
                projection: outcome.projection.clone(),
                origin: NativeNumericalOrigin {
                    occurrence,
                    operation,
                    row_addresses: row_addresses.to_vec(),
                },
            },
        );
    }

    pub(super) fn retain(
        &mut self,
        output: NativeCarrierOrdinal,
        carrier: ContemporaryCarrier<'chart>,
    ) {
        if !self.numerical.contains_key(&output) {
            return;
        }
        self.census.retained_octets += carrier.section.resident_octets();
        if let Some(previous) = self.standing.insert(output, carrier) {
            self.census.retained_octets -= previous.section.resident_octets();
        }
        self.census.peak_retained_octets = self
            .census
            .peak_retained_octets
            .max(self.census.retained_octets);
    }

    /// Discard only unused immutable numerical standing. Current carriers/checkpoints and local
    /// developmental deltas are outside this owner. A later miss recomputes its complete segment.
    pub(super) fn relieve_pressure(&mut self) -> bool {
        if self.standing.is_empty() {
            return false;
        }
        self.standing.clear();
        self.census.retained_octets = 0;
        self.census.pressure_evictions += 1;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(at: u32, inputs: &[u32], population: u32) -> NativeOperatorNode {
        NativeOperatorNode {
            ordinal: at,
            layer: None,
            primitive: NativeOperationPrimitive::Contract,
            inputs: inputs.iter().copied().map(NativeCarrierOrdinal).collect(),
            output: NativeCarrierOrdinal(at),
            coefficients: vec![NativeTensorOrdinal(population)],
        }
    }

    #[test]
    fn dependency_closure_ignores_a_disconnected_extension_and_reopens_a_connection() {
        let mut operations = vec![node(0, &[], 0), node(1, &[0], 1), node(2, &[], 2)];
        let before = DependencyIndex::found(&operations);
        assert_eq!(before.closure([0]), (BTreeSet::from([0, 1]), 1));
        for at in 3..103 {
            operations.push(node(at, &[at - 1], at));
        }
        let extended = DependencyIndex::found(&operations);
        assert_eq!(
            extended.closure([0]),
            before.closure([0]),
            "no hot dependency walk enters the separate component"
        );
        operations[2].inputs.push(NativeCarrierOrdinal(1));
        let connected = DependencyIndex::found(&operations);
        assert_eq!(connected.closure([0]).0.len(), 103);
        assert_eq!(connected.closure([0]).1, 102);
    }

    #[test]
    fn all_consumers_of_a_changed_population_seed_reopening() {
        let index = DependencyIndex::found(&[
            node(0, &[], 7),
            node(1, &[], 8),
            node(2, &[1], 7),
            node(3, &[0, 2], 9),
        ]);
        let seeds = index.population_users[&NativeTensorOrdinal(7)]
            .iter()
            .copied();
        assert_eq!(index.closure(seeds).0, BTreeSet::from([0, 2, 3]));
    }

    #[test]
    #[ignore = "requires CUDA; retained numerical sections move without a device copy"]
    fn resident_reuse_moves_whole_segments_and_reopens_only_the_connected_standing() {
        use crate::{
            embedding_fiber::ResidentReadout,
            resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
        };
        let readout = ResidentReadout::new().expect("CUDA");
        let surface = ResidentSurface::on(&readout).unwrap();
        let mut operations = vec![
            node(0, &[], 0),
            node(1, &[0], 1),
            node(2, &[1], 2),
            node(3, &[], 7),
        ];
        operations[1].primitive = NativeOperationPrimitive::Tanh;
        operations[1].coefficients.clear();
        let base_index = DependencyIndex::found(&operations);
        let base_walk = base_index.closure(
            base_index.population_users[&NativeTensorOrdinal(0)]
                .iter()
                .copied(),
        );
        for at in 4..104 {
            operations.push(node(at, &[], at + 10));
        }
        let mut reuse = NativeForwardReuse {
            index: DependencyIndex::found(&operations),
            standing: BTreeMap::new(),
            numerical: BTreeMap::new(),
            census: Default::default(),
        };
        let make = |output: u32| SegmentOutcome {
            output: NativeCarrierOrdinal(output),
            admitted_octaves: 8,
            projection: NativeSuccessorProjection::Exact,
            carrier: ContemporaryCarrier {
                bound_octaves: 8,
                section: surface
                    .mount_section_rest(&ResidentSectionRest {
                        rows: 1,
                        width: 1,
                        grain: ResidentGrain(0),
                        bound_octaves: 8,
                        intervals: vec![(output as i64 + 1, output as i64 + 1)],
                    })
                    .unwrap(),
            },
        };
        let partial = make(0);
        reuse.remember(&partial, 37, 0, &[11]);
        reuse.retain(partial.output, partial.carrier);
        assert!(
            reuse.take_segment(0, 2).is_none(),
            "a partial numerical segment cannot be reused"
        );
        assert_eq!(reuse.census().retained_octets, 0);
        let mut addresses = Vec::new();
        for output in 0..104 {
            let outcome = make(output);
            addresses.push(outcome.carrier.section.lo_device_ptr());
            reuse.remember(&outcome, 37, output, &[11]);
            reuse.retain(outcome.output, outcome.carrier);
        }
        let before = surface.census();
        let (returned, origins) = reuse.take_segment(0, 2).unwrap();
        assert_eq!(
            origins,
            vec![
                NativeNumericalOrigin {
                    occurrence: 37,
                    operation: 0,
                    row_addresses: vec![11]
                },
                NativeNumericalOrigin {
                    occurrence: 37,
                    operation: 1,
                    row_addresses: vec![11]
                }
            ]
        );
        assert_eq!(
            returned
                .iter()
                .map(|o| o.carrier.section.lo_device_ptr())
                .collect::<Vec<_>>(),
            addresses[..2]
        );
        assert_eq!(
            surface.census(),
            before,
            "moving a retained result launches, copies and allocates nothing"
        );
        for outcome in returned {
            reuse.retain(outcome.output, outcome.carrier);
        }
        let grown_walk = reuse.index.closure(
            reuse.index.population_users[&NativeTensorOrdinal(0)]
                .iter()
                .copied(),
        );
        assert_eq!(
            grown_walk, base_walk,
            "mounting/indexing 100 unrelated resident carriers adds no dependency work"
        );
        reuse.morphology_changed([NativeTensorOrdinal(0)]);
        assert!(reuse.take_segment(0, 2).is_none());
        assert!(
            reuse.take_segment(2, 3).is_none(),
            "transitive consumer reopened"
        );
        let (independent, origins) = reuse.take_segment(3, 4).unwrap();
        assert_eq!(
            origins[0].occurrence, 37,
            "reopening another component cannot rename this retained computation"
        );
        assert_eq!(independent[0].carrier.section.lo_device_ptr(), addresses[3]);
        assert_eq!(
            surface.read_out(&independent[0].carrier.section).unwrap(),
            vec![(4, 4)]
        );
        let before_growth_read = surface.census();
        let mut held_exterior = Vec::new();
        for at in 4..104 {
            let (segment, _) = reuse.take_segment(at, at + 1).unwrap();
            assert_eq!(segment[0].carrier.section.lo_device_ptr(), addresses[at]);
            held_exterior.extend(segment);
        }
        assert_eq!(surface.census(), before_growth_read,
            "the unrelated resident extension adds no launch, allocation, copy or read-out after its accounted mount");
        let outcome = make(0);
        reuse.remember(&outcome, 88, 0, &[12]);
        reuse.retain(outcome.output, outcome.carrier);
        assert!(reuse.relieve_pressure());
        assert!(!reuse.relieve_pressure());
        assert_eq!(
            surface.read_out(&independent[0].carrier.section).unwrap(),
            vec![(4, 4)],
            "pressure relief cannot destroy a carrier already moved into current use"
        );
    }
}
