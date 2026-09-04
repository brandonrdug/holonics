//! Receiver growth, local perspective, and recurrence across observation grain.
//!
//! A relation prediction supplies an open population of connected receiver
//! proposals.  A later exclusive return supplies another partition of the
//! same caused occurrences.  Their support-intersection diagram determines
//! whether a proposal closed, subdivided, grew together with other proposals,
//! or met a genuinely mixed branch.  No scalar matching score is used.
//!
//! A receiver perspective is derived only when requested.  Its pivot is the
//! earliest member in a declared causal coordinate; every other member is
//! carried by its signed transport from that pivot.  Projectivizing those
//! transports gives a finite directional horizon, while exact row rank gives
//! the locally distinguishable tangent population.  This is a finite
//! receiver-relative hypervolume, not an absolute center, radius, or ambient
//! coordinate system.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    EventId, ObservationEcologyStanding, ReceiverCoordinateFamilyId, ReceiverGradeId,
    ReceiverPredictionId, ReceiverTestimonyId, ReturnedCellId, ReturnedReceiverPartition,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverGrainQuotientId(pub u64);

/// Address of one returned cell in an admitted receiver partition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReturnedReceiverCellAddress {
    pub partition_event: EventId,
    pub cell: ReturnedCellId,
}

/// One complete lower receiver cell received as a constituent of a later
/// testimony occurrence.  The lower support remains available through
/// `source`; the quotient never replaces it with the outer face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGrainQuotient {
    pub id: ReceiverGrainQuotientId,
    pub caused_by: EventId,
    pub source: ReturnedReceiverCellAddress,
    pub source_family: ReceiverCoordinateFamilyId,
    pub target_family: ReceiverCoordinateFamilyId,
    pub target_chronology: u64,
    pub target: ReceiverTestimonyId,
}

/// Application-supplied identity join between a returned cell and its native
/// outer receiver face.  Production validates complete one-to-one coverage
/// and exact identity equality before forming a quotient.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReceiverCellReturn {
    pub source_cell: ReturnedCellId,
    pub target: ReceiverTestimonyId,
}

/// A batch assembled from testimony which already entered standing as the
/// outer face of a lower-grain receiver quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExistingReceiverBatch {
    pub family: ReceiverCoordinateFamilyId,
    pub chronology: u64,
    pub source: String,
    pub aperture: Vec<crate::ExactCoordinateInterval>,
    pub occurrences: Vec<ReceiverTestimonyId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ReceiverPerspectiveAddress {
    Proposed {
        prediction: ReceiverPredictionId,
        component: u64,
    },
    Returned(ReturnedReceiverCellAddress),
}

/// The coordinates through which one local perspective is requested.
///
/// The causal coordinate selects a pivot.  Directional coordinates determine
/// the local transport algebra.  Neither choice becomes a universal ambient
/// basis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPerspectiveSpec {
    pub causal_coordinate: u32,
    pub directional_coordinates: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverRelativeExtent {
    pub coordinate: u32,
    pub negative: Rat,
    pub positive: Rat,
}

/// One oriented projective direction in a receiver's local horizon.
///
/// The first nonzero coordinate is normalized to `+1` or `-1`; its absolute
/// magnitude supplies the positive depth coordinate.  Opposed directions
/// therefore remain distinct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverDirectionFiber {
    pub direction: Vec<Rat>,
    pub nearest_depth: Rat,
    pub farthest_depth: Rat,
    pub members: Vec<ReceiverTestimonyId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverHorizonTopology {
    Empty,
    /// A finite projective direction population whose sphere type has not
    /// been established by a link/manifold certificate.
    UncertifiedDirectional {
        projective_dimension: u32,
    },
    CertifiedHypersphere {
        dimension: u32,
    },
    Singular {
        projective_dimension: u32,
        components: u32,
    },
}

/// Complete on-demand local body of one receiver.
///
/// This object intentionally has no scalar volume.  Its hypervolume is the
/// exact population of source members, signed relative extents, tangent rank,
/// and directional depth fibers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHypervolume {
    pub tangent_rank: u32,
    pub horizon: ReceiverHorizonTopology,
    pub extents: Vec<ReceiverRelativeExtent>,
    pub directions: Vec<ReceiverDirectionFiber>,
    pub zero_transport_members: Vec<ReceiverTestimonyId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPerspective {
    pub address: ReceiverPerspectiveAddress,
    pub family: ReceiverCoordinateFamilyId,
    pub chronology: u64,
    /// Complete minimum-causal-coordinate face.  It may contain more than one
    /// occurrence and is never collapsed into a fictitious scalar center.
    pub causal_basis: BTreeSet<ReceiverTestimonyId>,
    /// One exact chart gauge chosen lexicographically within `causal_basis`.
    /// It is not an ontological center.
    pub pivot: ReceiverTestimonyId,
    pub support: BTreeSet<ReceiverTestimonyId>,
    pub hypervolume: ReceiverHypervolume,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ReceiverMorphologyKind {
    ExactClosure,
    Subdivision,
    Growth,
    MixedBranch,
}

/// Compact exact receipt of the complete proposal/return overlap diagram.
///
/// Full member identities remain in the referenced prediction and returned
/// partition.  This receipt records the topology and populations without
/// duplicating millions of source identities in standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverMorphologySummary {
    pub schema: String,
    pub proposed_receivers: u64,
    pub returned_receivers: u64,
    pub overlap_relations: u64,
    pub shared_occurrences: u64,
    pub exact_closures: u64,
    pub subdivisions: u64,
    pub growths: u64,
    pub mixed_branches: u64,
    pub maximum_proposals_in_component: u64,
    pub maximum_returns_in_component: u64,
    pub maximum_occurrences_in_overlap: u64,
    pub component_bidegrees: BTreeMap<(u64, u64), u64>,
}

impl ReceiverMorphologySummary {
    pub fn component_count(&self) -> u64 {
        self.exact_closures + self.subdivisions + self.growths + self.mixed_branches
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverEcologyError {
    #[error("receiver perspective has no source support")]
    EmptyPerspective,
    #[error("receiver perspective coordinate {0} is absent")]
    MissingPerspectiveCoordinate(u32),
    #[error("receiver perspective has a repeated directional coordinate")]
    RepeatedPerspectiveCoordinate,
    #[error("receiver prediction component {component} is absent from {prediction:?}")]
    MissingPredictionComponent {
        prediction: ReceiverPredictionId,
        component: u64,
    },
    #[error("receiver partition event {0:?} is absent")]
    MissingPartitionEvent(EventId),
    #[error("receiver cell {cell:?} is absent from partition event {event:?}")]
    MissingReturnedCell {
        event: EventId,
        cell: ReturnedCellId,
    },
    #[error("receiver relation grade {0:?} is absent")]
    MissingReceiverGrade(ReceiverGradeId),
    #[error("receiver relation prediction {0:?} is absent")]
    MissingReceiverPrediction(ReceiverPredictionId),
    #[error("a receiver partition does not cover the predicted population exactly")]
    IncompatibleReceiverPartitions,
    #[error("receiver morphology carrier overflowed")]
    CarrierOverflow,
    #[error("receiver perspective standing is malformed")]
    MalformedPerspectiveStanding,
}

impl ObservationEcologyStanding {
    /// Derive one complete local receiver perspective without materializing a
    /// fixed global receiver grid.
    pub fn receiver_perspective(
        &self,
        address: ReceiverPerspectiveAddress,
        spec: &ReceiverPerspectiveSpec,
    ) -> Result<ReceiverPerspective, ReceiverEcologyError> {
        if spec.directional_coordinates.is_empty() {
            return Err(ReceiverEcologyError::EmptyPerspective);
        }
        let mut selected = BTreeSet::new();
        for coordinate in &spec.directional_coordinates {
            if !selected.insert(*coordinate) {
                return Err(ReceiverEcologyError::RepeatedPerspectiveCoordinate);
            }
        }

        let (family, chronology, support) = match address {
            ReceiverPerspectiveAddress::Proposed {
                prediction,
                component,
            } => {
                let prediction_body = self
                    .predictions
                    .get(&prediction)
                    .ok_or(ReceiverEcologyError::MissingReceiverPrediction(prediction))?;
                let component_index = usize::try_from(component)
                    .map_err(|_| ReceiverEcologyError::CarrierOverflow)?;
                let members = prediction_body
                    .forced_components
                    .get(component_index)
                    .ok_or(ReceiverEcologyError::MissingPredictionComponent {
                        prediction,
                        component,
                    })?;
                (
                    prediction_body.family,
                    prediction_body.chronology,
                    members.iter().copied().collect::<BTreeSet<_>>(),
                )
            }
            ReceiverPerspectiveAddress::Returned(returned) => {
                let partition = self
                    .admitted_partitions
                    .iter()
                    .find(|partition| partition.event == returned.partition_event)
                    .ok_or(ReceiverEcologyError::MissingPartitionEvent(
                        returned.partition_event,
                    ))?;
                let cell = partition
                    .partition
                    .cells
                    .iter()
                    .find(|cell| cell.id == returned.cell)
                    .ok_or(ReceiverEcologyError::MissingReturnedCell {
                        event: returned.partition_event,
                        cell: returned.cell,
                    })?;
                (partition.family, partition.chronology, cell.members.clone())
            }
        };
        if support.is_empty() {
            return Err(ReceiverEcologyError::EmptyPerspective);
        }
        let family_body = self
            .families
            .get(&family)
            .ok_or(ReceiverEcologyError::MalformedPerspectiveStanding)?;
        let coordinate_extent = family_body.coordinates.len();
        for coordinate in
            std::iter::once(&spec.causal_coordinate).chain(spec.directional_coordinates.iter())
        {
            let index =
                usize::try_from(*coordinate).map_err(|_| ReceiverEcologyError::CarrierOverflow)?;
            if index >= coordinate_extent {
                return Err(ReceiverEcologyError::MissingPerspectiveCoordinate(
                    *coordinate,
                ));
            }
        }

        let mut decoded = BTreeMap::<ReceiverTestimonyId, Vec<Rat>>::new();
        for member in &support {
            let testimony = self
                .testimonies
                .get(member)
                .ok_or(ReceiverEcologyError::MalformedPerspectiveStanding)?;
            let chart = self
                .charts
                .get(&testimony.occurrence.chart)
                .ok_or(ReceiverEcologyError::MalformedPerspectiveStanding)?;
            if chart.family != family {
                return Err(ReceiverEcologyError::MalformedPerspectiveStanding);
            }
            decoded.insert(
                *member,
                chart
                    .receive(&testimony.occurrence.raw)
                    .map_err(|_| ReceiverEcologyError::MalformedPerspectiveStanding)?,
            );
        }
        let causal_coordinate = usize::try_from(spec.causal_coordinate)
            .map_err(|_| ReceiverEcologyError::CarrierOverflow)?;
        let causal_minimum = support
            .iter()
            .map(|member| decoded[member][causal_coordinate].clone())
            .min()
            .ok_or(ReceiverEcologyError::EmptyPerspective)?;
        let directional = spec
            .directional_coordinates
            .iter()
            .map(|coordinate| {
                usize::try_from(*coordinate).map_err(|_| ReceiverEcologyError::CarrierOverflow)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let causal_basis = support
            .iter()
            .copied()
            .filter(|member| decoded[member][causal_coordinate] == causal_minimum)
            .collect::<BTreeSet<_>>();
        let pivot = causal_basis
            .iter()
            .copied()
            .min_by(|left, right| {
                directional
                    .iter()
                    .map(|coordinate| &decoded[left][*coordinate])
                    .cmp(
                        directional
                            .iter()
                            .map(|coordinate| &decoded[right][*coordinate]),
                    )
                    .then_with(|| left.cmp(right))
            })
            .ok_or(ReceiverEcologyError::EmptyPerspective)?;
        let pivot_coordinates = directional
            .iter()
            .map(|coordinate| decoded[&pivot][*coordinate].clone())
            .collect::<Vec<_>>();

        let mut transports = Vec::<Vec<Rat>>::new();
        let mut direction_members =
            BTreeMap::<Vec<Rat>, (Rat, Rat, Vec<ReceiverTestimonyId>)>::new();
        let mut zero_transport_members = Vec::new();
        let mut minima = vec![Rat::zero(); directional.len()];
        let mut maxima = vec![Rat::zero(); directional.len()];
        for member in &support {
            let transport = directional
                .iter()
                .zip(&pivot_coordinates)
                .map(|(coordinate, pivot_value)| &decoded[member][*coordinate] - pivot_value)
                .collect::<Vec<_>>();
            for (coordinate, value) in transport.iter().enumerate() {
                minima[coordinate] = minima[coordinate].clone().min(value.clone());
                maxima[coordinate] = maxima[coordinate].clone().max(value.clone());
            }
            let Some(first_nonzero) = transport.iter().position(|value| !value.is_zero()) else {
                zero_transport_members.push(*member);
                continue;
            };
            let depth = transport[first_nonzero].clone().abs();
            let direction = transport
                .iter()
                .map(|value| value / &depth)
                .collect::<Vec<_>>();
            transports.push(transport);
            direction_members
                .entry(direction)
                .and_modify(|(nearest, farthest, members)| {
                    *nearest = nearest.clone().min(depth.clone());
                    *farthest = farthest.clone().max(depth.clone());
                    members.push(*member);
                })
                .or_insert_with(|| (depth.clone(), depth, vec![*member]));
        }
        let tangent_rank = exact_rank(transports);
        let directions = direction_members
            .into_iter()
            .map(
                |(direction, (nearest_depth, farthest_depth, members))| ReceiverDirectionFiber {
                    direction,
                    nearest_depth,
                    farthest_depth,
                    members,
                },
            )
            .collect::<Vec<_>>();
        let horizon = if directions.is_empty() {
            ReceiverHorizonTopology::Empty
        } else {
            ReceiverHorizonTopology::UncertifiedDirectional {
                projective_dimension: u32::try_from(tangent_rank.saturating_sub(1))
                    .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
            }
        };
        let extents = spec
            .directional_coordinates
            .iter()
            .enumerate()
            .map(|(index, coordinate)| ReceiverRelativeExtent {
                coordinate: *coordinate,
                negative: (-minima[index].clone()).max(Rat::zero()),
                positive: maxima[index].clone().max(Rat::zero()),
            })
            .collect();
        Ok(ReceiverPerspective {
            address,
            family,
            chronology,
            causal_basis,
            pivot,
            support,
            hypervolume: ReceiverHypervolume {
                tangent_rank: u32::try_from(tangent_rank)
                    .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
                horizon,
                extents,
                directions,
                zero_transport_members,
            },
        })
    }

    pub fn receiver_morphology(
        &self,
        grade: ReceiverGradeId,
    ) -> Result<ReceiverMorphologySummary, ReceiverEcologyError> {
        let grade_body = self
            .grades
            .get(&grade)
            .ok_or(ReceiverEcologyError::MissingReceiverGrade(grade))?;
        let prediction = self.predictions.get(&grade_body.prediction).ok_or(
            ReceiverEcologyError::MissingReceiverPrediction(grade_body.prediction),
        )?;
        receiver_morphology_summary(prediction, &grade_body.returned)
    }
}

pub fn receiver_morphology_summary(
    prediction: &crate::ReceiverRelationPrediction,
    returned: &ReturnedReceiverPartition,
) -> Result<ReceiverMorphologySummary, ReceiverEcologyError> {
    let proposed_count = prediction.forced_components.len();
    let returned_count = returned.cells.len();
    let mut proposal_by_member = BTreeMap::<ReceiverTestimonyId, usize>::new();
    for (proposal, members) in prediction.forced_components.iter().enumerate() {
        for member in members {
            if proposal_by_member.insert(*member, proposal).is_some() {
                return Err(ReceiverEcologyError::IncompatibleReceiverPartitions);
            }
        }
    }
    if proposal_by_member.len() != prediction.occurrences.len() {
        return Err(ReceiverEcologyError::IncompatibleReceiverPartitions);
    }
    let mut return_by_member = BTreeMap::<ReceiverTestimonyId, usize>::new();
    for (returned_ordinal, cell) in returned.cells.iter().enumerate() {
        for member in &cell.members {
            if return_by_member.insert(*member, returned_ordinal).is_some() {
                return Err(ReceiverEcologyError::IncompatibleReceiverPartitions);
            }
        }
    }
    if proposal_by_member.keys().copied().collect::<BTreeSet<_>>()
        != return_by_member.keys().copied().collect()
    {
        return Err(ReceiverEcologyError::IncompatibleReceiverPartitions);
    }

    let mut overlaps = BTreeMap::<(usize, usize), u64>::new();
    for (member, proposal) in &proposal_by_member {
        let returned_ordinal = return_by_member[member];
        let population = overlaps.entry((*proposal, returned_ordinal)).or_default();
        *population = population
            .checked_add(1)
            .ok_or(ReceiverEcologyError::CarrierOverflow)?;
    }
    let mut disjoint = DisjointSet::new(
        proposed_count
            .checked_add(returned_count)
            .ok_or(ReceiverEcologyError::CarrierOverflow)?,
    );
    for (proposal, returned_ordinal) in overlaps.keys() {
        disjoint.union(*proposal, proposed_count + *returned_ordinal);
    }
    let mut components = BTreeMap::<usize, (BTreeSet<usize>, BTreeSet<usize>)>::new();
    for proposal in 0..proposed_count {
        let root = disjoint.find(proposal);
        components.entry(root).or_default().0.insert(proposal);
    }
    for returned_ordinal in 0..returned_count {
        let root = disjoint.find(proposed_count + returned_ordinal);
        components
            .entry(root)
            .or_default()
            .1
            .insert(returned_ordinal);
    }
    let mut summary = ReceiverMorphologySummary {
        schema: "holonic-engine.receiver-morphology-summary.v1".to_owned(),
        proposed_receivers: u64::try_from(proposed_count)
            .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
        returned_receivers: u64::try_from(returned_count)
            .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
        overlap_relations: u64::try_from(overlaps.len())
            .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
        shared_occurrences: u64::try_from(proposal_by_member.len())
            .map_err(|_| ReceiverEcologyError::CarrierOverflow)?,
        exact_closures: 0,
        subdivisions: 0,
        growths: 0,
        mixed_branches: 0,
        maximum_proposals_in_component: 0,
        maximum_returns_in_component: 0,
        maximum_occurrences_in_overlap: overlaps.values().copied().max().unwrap_or(0),
        component_bidegrees: BTreeMap::new(),
    };
    for (proposals, returns) in components.values() {
        if proposals.is_empty() || returns.is_empty() {
            return Err(ReceiverEcologyError::IncompatibleReceiverPartitions);
        }
        let proposal_population =
            u64::try_from(proposals.len()).map_err(|_| ReceiverEcologyError::CarrierOverflow)?;
        let return_population =
            u64::try_from(returns.len()).map_err(|_| ReceiverEcologyError::CarrierOverflow)?;
        summary.maximum_proposals_in_component = summary
            .maximum_proposals_in_component
            .max(proposal_population);
        summary.maximum_returns_in_component =
            summary.maximum_returns_in_component.max(return_population);
        let count = summary
            .component_bidegrees
            .entry((proposal_population, return_population))
            .or_default();
        *count = count
            .checked_add(1)
            .ok_or(ReceiverEcologyError::CarrierOverflow)?;
        let target = match (proposal_population, return_population) {
            (1, 1) => &mut summary.exact_closures,
            (1, _) => &mut summary.subdivisions,
            (_, 1) => &mut summary.growths,
            _ => &mut summary.mixed_branches,
        };
        *target = target
            .checked_add(1)
            .ok_or(ReceiverEcologyError::CarrierOverflow)?;
    }
    Ok(summary)
}

fn exact_rank(mut matrix: Vec<Vec<Rat>>) -> usize {
    if matrix.is_empty() {
        return 0;
    }
    let columns = matrix[0].len();
    let mut pivot_row = 0_usize;
    for column in 0..columns {
        let Some(candidate) = (pivot_row..matrix.len()).find(|row| !matrix[*row][column].is_zero())
        else {
            continue;
        };
        matrix.swap(pivot_row, candidate);
        let pivot = matrix[pivot_row][column].clone();
        for coordinate in column..columns {
            matrix[pivot_row][coordinate] /= &pivot;
        }
        let normalized = matrix[pivot_row].clone();
        for (row, values) in matrix.iter_mut().enumerate() {
            if row == pivot_row || values[column].is_zero() {
                continue;
            }
            let scale = values[column].clone();
            for coordinate in column..columns {
                values[coordinate] -= &scale * &normalized[coordinate];
            }
        }
        pivot_row += 1;
        if pivot_row == matrix.len() {
            break;
        }
    }
    pivot_row
}

#[derive(Clone, Debug)]
struct DisjointSet {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl DisjointSet {
    fn new(extent: usize) -> Self {
        Self {
            parent: (0..extent).collect(),
            rank: vec![0; extent],
        }
    }

    fn find(&mut self, value: usize) -> usize {
        let parent = self.parent[value];
        if parent != value {
            let root = self.find(parent);
            self.parent[value] = root;
        }
        self.parent[value]
    }

    fn union(&mut self, left: usize, right: usize) {
        let mut left_root = self.find(left);
        let mut right_root = self.find(right);
        if left_root == right_root {
            return;
        }
        if self.rank[left_root] < self.rank[right_root] {
            std::mem::swap(&mut left_root, &mut right_root);
        }
        self.parent[right_root] = left_root;
        if self.rank[left_root] == self.rank[right_root] {
            self.rank[left_root] += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use num_traits::One;

    use super::*;
    use crate::{
        ExactDifferenceVector, LearnedPartitionRelation, PredictedReceiverRelation,
        ReceiverRelationPrediction, ReceiverRelationState, ReturnedAlgorithmId,
        ReturnedCellCoverage, ReturnedReceiverCell,
    };

    fn prediction(components: &[&[u64]]) -> ReceiverRelationPrediction {
        let forced_components = components
            .iter()
            .map(|members| {
                members
                    .iter()
                    .copied()
                    .map(ReceiverTestimonyId)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let occurrences = forced_components.iter().flatten().copied().collect();
        ReceiverRelationPrediction {
            schema: "holonic-engine.receiver-relation-prediction.v1".to_owned(),
            id: ReceiverPredictionId(1),
            caused_by: EventId(1),
            family: ReceiverCoordinateFamilyId(1),
            algorithm: ReturnedAlgorithmId(1),
            chronology: 0,
            source: "test".to_owned(),
            aperture: Vec::new(),
            occurrences,
            candidate_relations: vec![PredictedReceiverRelation {
                members: [ReceiverTestimonyId(1), ReceiverTestimonyId(2)],
                difference: ExactDifferenceVector(vec![Rat::one()]),
                state: ReceiverRelationState::ForcedTogether,
            }],
            forced_components,
            relation_before: LearnedPartitionRelation {
                schema: "holonic-engine.learned-partition-relation.v1".to_owned(),
                family: ReceiverCoordinateFamilyId(1),
                algorithm: ReturnedAlgorithmId(1),
                positive_maxima: Vec::new(),
                negative_minima: Vec::new(),
                testimony_events: BTreeSet::new(),
                returned_cells: 0,
            },
        }
    }

    fn returned(cells: &[&[u64]]) -> ReturnedReceiverPartition {
        ReturnedReceiverPartition {
            algorithm: ReturnedAlgorithmId(1),
            coverage: ReturnedCellCoverage::CompleteExclusive,
            cells: cells
                .iter()
                .enumerate()
                .map(|(ordinal, members)| ReturnedReceiverCell {
                    id: ReturnedCellId(u64::try_from(ordinal + 1).unwrap()),
                    members: members.iter().copied().map(ReceiverTestimonyId).collect(),
                })
                .collect(),
        }
    }

    #[test]
    fn support_intersection_distinguishes_closure_split_growth_and_branch() {
        let closure =
            receiver_morphology_summary(&prediction(&[&[1, 2], &[3]]), &returned(&[&[1, 2], &[3]]))
                .unwrap();
        assert_eq!(closure.exact_closures, 2);

        let split =
            receiver_morphology_summary(&prediction(&[&[1, 2]]), &returned(&[&[1], &[2]])).unwrap();
        assert_eq!(split.subdivisions, 1);

        let growth =
            receiver_morphology_summary(&prediction(&[&[1], &[2]]), &returned(&[&[1, 2]])).unwrap();
        assert_eq!(growth.growths, 1);

        let branch = receiver_morphology_summary(
            &prediction(&[&[1, 2], &[3, 4]]),
            &returned(&[&[1, 3], &[2, 4]]),
        )
        .unwrap();
        assert_eq!(branch.mixed_branches, 1);
        assert_eq!(branch.component_bidegrees, BTreeMap::from([((2, 2), 1)]));
    }
}
