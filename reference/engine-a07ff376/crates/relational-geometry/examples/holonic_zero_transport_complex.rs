//! Derive an exact transport complex from the certified eta receiver atlas.
//!
//! The source atlas supplies zero-bearing rational receivers and one exact
//! midpoint eta-current face per receiver. This analysis does not substitute
//! those midpoint faces for the unknown zero coordinates. It asks how the
//! complete receiver-local current words reorient between every ordered pair,
//! how direct transport compares with transport through a third receiver, and
//! which apparent interval defects owe only forgotten dependency.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use num_traits::{Signed, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, EtaCurrentReceipt, PrimeValuation, Rat, RatInterval,
    format_rat,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, Deserialize)]
struct SourceAtlas {
    schema: String,
    arithmetic: String,
    zero_lineages: Vec<SourceZeroLineage>,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceZeroLineage {
    ordinal: usize,
    refinements: Vec<SourceRefinement>,
    final_receiver: ComplexReceiverBox,
    midpoint_current: EtaCurrentReceipt,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceRefinement {
    grain: u32,
    selected: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum CertifiedSign {
    Negative,
    Zero,
    Positive,
    Open,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum CurrentFeature {
    ContributionReal,
    ContributionImaginary,
    PartialReal,
    PartialImaginary,
    TurnToSuccessor,
    RadialChangeToSuccessor,
}

const CURRENT_FEATURES: [CurrentFeature; 6] = [
    CurrentFeature::ContributionReal,
    CurrentFeature::ContributionImaginary,
    CurrentFeature::PartialReal,
    CurrentFeature::PartialImaginary,
    CurrentFeature::TurnToSuccessor,
    CurrentFeature::RadialChangeToSuccessor,
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SourceOrdinal {
    ordinal: u32,
    hand: i8,
    prime_valuations: Vec<PrimeValuation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CurrentState {
    contribution_real: CertifiedSign,
    contribution_imaginary: CertifiedSign,
    partial_real: CertifiedSign,
    partial_imaginary: CertifiedSign,
    turn_to_successor: Option<CertifiedSign>,
    radial_change_to_successor: Option<CertifiedSign>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CurrentAtom {
    ordinal: u32,
    state: CurrentState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct RefinementSelection {
    grain: u32,
    side: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ReceiverFace {
    ordinal: usize,
    zero_receiver: ComplexReceiverBox,
    representative_receiver: ComplexReceiverBox,
    refinement_word: Vec<RefinementSelection>,
    tail_radius: Rat,
    current_word: Vec<CurrentAtom>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct RefinementChange {
    grain: u32,
    from: String,
    to: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StateChange {
    ordinal: u32,
    changed_features: Vec<String>,
    from: CurrentState,
    to: CurrentState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct EdgeTransport {
    from: usize,
    to: usize,
    delta_sigma: Rat,
    delta_tau: Rat,
    zero_ordinate_difference_receiver: RatInterval,
    refinement_changes: Vec<RefinementChange>,
    current_changes: Vec<StateChange>,
    primitive_under_receiver_words: bool,
    detour_free_factorizations: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct IntervalDependencyFoil {
    direct_difference: RatInterval,
    mediated_sum: RatInterval,
    mediated_contains_direct: bool,
    excess_width: Rat,
    interpretation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FeaturePassage {
    feature: CurrentFeature,
    first_leg_only_ordinals: Vec<u32>,
    second_leg_only_ordinals: Vec<u32>,
    detour_ordinals: Vec<u32>,
    third_value_ordinals: Vec<u32>,
    unchanged_ordinals: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct TriangleTransport {
    from: usize,
    via: usize,
    to: usize,
    direct_change_ordinals: Vec<u32>,
    mediated_support_ordinals: Vec<u32>,
    first_leg_only_ordinals: Vec<u32>,
    second_leg_only_ordinals: Vec<u32>,
    detour_ordinals: Vec<u32>,
    third_state_ordinals: Vec<u32>,
    mixed_retriangulation_ordinals: Vec<u32>,
    unchanged_ordinals: Vec<u32>,
    feature_passages: Vec<FeaturePassage>,
    refinement_detour_grains: Vec<u32>,
    refinement_third_state_grains: Vec<u32>,
    endpoint_current_exact: bool,
    symbolic_phase_delta_direct: Rat,
    symbolic_phase_delta_mediated: Rat,
    symbolic_phase_control_closes: bool,
    detour_free_factorization: bool,
    interval_dependency_foil: IntervalDependencyFoil,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PrimitivePathFamily {
    from: usize,
    to: usize,
    causal_degree: Option<usize>,
    shortest_primitive_paths: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ReducibleEdge {
    from: usize,
    to: usize,
    through: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FeatureTopology {
    feature: CurrentFeature,
    primitive_edges: Vec<(usize, usize)>,
    reducible_edges: Vec<ReducibleEdge>,
    detour_free_oriented_triangles: Vec<(usize, usize, usize)>,
    curved_oriented_triangles: Vec<(usize, usize, usize)>,
    primitive_path_families: Vec<PrimitivePathFamily>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StructuralRead {
    receiver_ordinals: Vec<usize>,
    primitive_edges: Vec<(usize, usize)>,
    reducible_edges: Vec<ReducibleEdge>,
    detour_free_oriented_triangles: Vec<(usize, usize, usize)>,
    curved_oriented_triangles: Vec<(usize, usize, usize)>,
    unreachable_through_primitive_edges: Vec<(usize, usize)>,
    feature_topologies: Vec<FeatureTopology>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ZeroTransportComplex {
    schema: String,
    source_schema: String,
    source_sha256: String,
    arithmetic: String,
    boundary: String,
    source_ordinals: Vec<SourceOrdinal>,
    receiver_faces: Vec<ReceiverFace>,
    edge_transports: Vec<EdgeTransport>,
    triangle_transports: Vec<TriangleTransport>,
    primitive_path_families: Vec<PrimitivePathFamily>,
    structural_read: StructuralRead,
}

fn require(condition: bool, message: impl Into<String>) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}

fn classify(interval: &RatInterval) -> CertifiedSign {
    if interval.upper.is_negative() {
        CertifiedSign::Negative
    } else if interval.lower.is_positive() {
        CertifiedSign::Positive
    } else if interval.lower.is_zero() && interval.upper.is_zero() {
        CertifiedSign::Zero
    } else {
        CertifiedSign::Open
    }
}

fn squared_norm(value: &ComplexInterval) -> RatInterval {
    value.re.square().add(&value.im.square())
}

fn turn(left: &ComplexInterval, right: &ComplexInterval) -> CertifiedSign {
    classify(
        &left
            .re
            .multiply(&right.im)
            .subtract(&left.im.multiply(&right.re)),
    )
}

fn current_word(current: &EtaCurrentReceipt) -> Vec<CurrentAtom> {
    current
        .terms
        .iter()
        .enumerate()
        .map(|(index, term)| {
            let successor = current.terms.get(index + 1);
            CurrentAtom {
                ordinal: term.ordinal,
                state: CurrentState {
                    contribution_real: classify(&term.contribution.re),
                    contribution_imaginary: classify(&term.contribution.im),
                    partial_real: classify(&term.partial_sum.re),
                    partial_imaginary: classify(&term.partial_sum.im),
                    turn_to_successor: successor
                        .map(|next| turn(&term.contribution, &next.contribution)),
                    radial_change_to_successor: successor.map(|next| {
                        classify(
                            &squared_norm(&next.partial_sum)
                                .subtract(&squared_norm(&term.partial_sum)),
                        )
                    }),
                },
            }
        })
        .collect()
}

fn source_ordinals(lineages: &[SourceZeroLineage]) -> Result<Vec<SourceOrdinal>, String> {
    let first = lineages
        .first()
        .ok_or_else(|| "the source atlas has no zero lineages".to_owned())?;
    let source = first
        .midpoint_current
        .terms
        .iter()
        .map(|term| SourceOrdinal {
            ordinal: term.ordinal,
            hand: term.hand,
            prime_valuations: term.valuations.clone(),
        })
        .collect::<Vec<_>>();
    for lineage in lineages.iter().skip(1) {
        let candidate = lineage
            .midpoint_current
            .terms
            .iter()
            .map(|term| SourceOrdinal {
                ordinal: term.ordinal,
                hand: term.hand,
                prime_valuations: term.valuations.clone(),
            })
            .collect::<Vec<_>>();
        require(
            candidate == source,
            format!(
                "receiver {} does not carry the common ordinal/valuation source",
                lineage.ordinal
            ),
        )?;
    }
    Ok(source)
}

fn build_receiver_faces(lineages: &[SourceZeroLineage]) -> Result<Vec<ReceiverFace>, String> {
    let mut faces = Vec::with_capacity(lineages.len());
    for (index, lineage) in lineages.iter().enumerate() {
        require(
            lineage.ordinal == index,
            format!("lineage ordinal {} is not contiguous", lineage.ordinal),
        )?;
        require(
            lineage.midpoint_current.receiver.sigma
                == RatInterval::point(lineage.final_receiver.sigma.midpoint()),
            format!("lineage {index} representative sigma is not its receiver midpoint"),
        )?;
        require(
            lineage.midpoint_current.receiver.tau
                == RatInterval::point(lineage.final_receiver.tau.midpoint()),
            format!("lineage {index} representative tau is not its receiver midpoint"),
        )?;
        faces.push(ReceiverFace {
            ordinal: lineage.ordinal,
            zero_receiver: lineage.final_receiver.clone(),
            representative_receiver: lineage.midpoint_current.receiver.clone(),
            refinement_word: lineage
                .refinements
                .iter()
                .map(|step| RefinementSelection {
                    grain: step.grain,
                    side: step.selected.clone(),
                })
                .collect(),
            tail_radius: lineage.midpoint_current.tail_radius.clone(),
            current_word: current_word(&lineage.midpoint_current),
        });
    }
    let expected_extent = faces
        .first()
        .map(|face| face.current_word.len())
        .unwrap_or(0);
    require(expected_extent > 0, "the receiver current words are empty")?;
    for face in &faces {
        require(
            face.current_word.len() == expected_extent,
            format!("receiver {} has a different current extent", face.ordinal),
        )?;
    }
    Ok(faces)
}

fn changed_features(left: &CurrentState, right: &CurrentState) -> Vec<String> {
    let mut changed = Vec::new();
    if left.contribution_real != right.contribution_real {
        changed.push("contribution_real".to_owned());
    }
    if left.contribution_imaginary != right.contribution_imaginary {
        changed.push("contribution_imaginary".to_owned());
    }
    if left.partial_real != right.partial_real {
        changed.push("partial_real".to_owned());
    }
    if left.partial_imaginary != right.partial_imaginary {
        changed.push("partial_imaginary".to_owned());
    }
    if left.turn_to_successor != right.turn_to_successor {
        changed.push("turn_to_successor".to_owned());
    }
    if left.radial_change_to_successor != right.radial_change_to_successor {
        changed.push("radial_change_to_successor".to_owned());
    }
    changed
}

fn feature_value(state: &CurrentState, feature: CurrentFeature) -> Option<CertifiedSign> {
    match feature {
        CurrentFeature::ContributionReal => Some(state.contribution_real),
        CurrentFeature::ContributionImaginary => Some(state.contribution_imaginary),
        CurrentFeature::PartialReal => Some(state.partial_real),
        CurrentFeature::PartialImaginary => Some(state.partial_imaginary),
        CurrentFeature::TurnToSuccessor => state.turn_to_successor,
        CurrentFeature::RadialChangeToSuccessor => state.radial_change_to_successor,
    }
}

fn feature_passage(
    feature: CurrentFeature,
    source: &ReceiverFace,
    middle: &ReceiverFace,
    target: &ReceiverFace,
) -> FeaturePassage {
    let mut first_only = Vec::new();
    let mut second_only = Vec::new();
    let mut detours = Vec::new();
    let mut third_values = Vec::new();
    let mut unchanged = Vec::new();
    for ((left, center), right) in source
        .current_word
        .iter()
        .zip(&middle.current_word)
        .zip(&target.current_word)
    {
        let left_value = feature_value(&left.state, feature);
        let center_value = feature_value(&center.state, feature);
        let right_value = feature_value(&right.state, feature);
        let first_changes = left_value != center_value;
        let second_changes = center_value != right_value;
        let endpoint_changes = left_value != right_value;
        match (first_changes, second_changes, endpoint_changes) {
            (false, false, false) => unchanged.push(left.ordinal),
            (true, false, true) => first_only.push(left.ordinal),
            (false, true, true) => second_only.push(left.ordinal),
            (true, true, false) => detours.push(left.ordinal),
            (true, true, true) => third_values.push(left.ordinal),
            _ => unreachable!("feature equality makes every other case impossible"),
        }
    }
    FeaturePassage {
        feature,
        first_leg_only_ordinals: first_only,
        second_leg_only_ordinals: second_only,
        detour_ordinals: detours,
        third_value_ordinals: third_values,
        unchanged_ordinals: unchanged,
    }
}

fn interval_contains(container: &RatInterval, contained: &RatInterval) -> bool {
    container.lower <= contained.lower && container.upper >= contained.upper
}

fn build_edges(faces: &[ReceiverFace]) -> Vec<EdgeTransport> {
    let mut edges = Vec::new();
    for from in 0..faces.len() {
        for to in 0..faces.len() {
            if from == to {
                continue;
            }
            let from_face = &faces[from];
            let to_face = &faces[to];
            let current_changes = from_face
                .current_word
                .iter()
                .zip(&to_face.current_word)
                .filter_map(|(left, right)| {
                    if left.state == right.state {
                        None
                    } else {
                        Some(StateChange {
                            ordinal: left.ordinal,
                            changed_features: changed_features(&left.state, &right.state),
                            from: left.state.clone(),
                            to: right.state.clone(),
                        })
                    }
                })
                .collect();
            let refinement_changes = from_face
                .refinement_word
                .iter()
                .zip(&to_face.refinement_word)
                .filter_map(|(left, right)| {
                    if left.side == right.side {
                        None
                    } else {
                        Some(RefinementChange {
                            grain: left.grain,
                            from: left.side.clone(),
                            to: right.side.clone(),
                        })
                    }
                })
                .collect();
            edges.push(EdgeTransport {
                from,
                to,
                delta_sigma: to_face.representative_receiver.sigma.midpoint()
                    - from_face.representative_receiver.sigma.midpoint(),
                delta_tau: to_face.representative_receiver.tau.midpoint()
                    - from_face.representative_receiver.tau.midpoint(),
                zero_ordinate_difference_receiver: to_face
                    .zero_receiver
                    .tau
                    .subtract(&from_face.zero_receiver.tau),
                refinement_changes,
                current_changes,
                primitive_under_receiver_words: true,
                detour_free_factorizations: Vec::new(),
            });
        }
    }
    edges
}

fn triangle(faces: &[ReceiverFace], from: usize, via: usize, to: usize) -> TriangleTransport {
    let source = &faces[from];
    let middle = &faces[via];
    let target = &faces[to];
    let mut direct = Vec::new();
    let mut mediated = Vec::new();
    let mut first_only = Vec::new();
    let mut second_only = Vec::new();
    let mut detours = Vec::new();
    let mut third_states = Vec::new();
    let mut unchanged = Vec::new();

    for ((left, center), right) in source
        .current_word
        .iter()
        .zip(&middle.current_word)
        .zip(&target.current_word)
    {
        let ordinal = left.ordinal;
        let first_changes = left.state != center.state;
        let second_changes = center.state != right.state;
        let endpoint_changes = left.state != right.state;
        if endpoint_changes {
            direct.push(ordinal);
        }
        if first_changes || second_changes {
            mediated.push(ordinal);
        }
        match (first_changes, second_changes, endpoint_changes) {
            (false, false, false) => unchanged.push(ordinal),
            (true, false, true) => first_only.push(ordinal),
            (false, true, true) => second_only.push(ordinal),
            (true, true, false) => detours.push(ordinal),
            (true, true, true) => third_states.push(ordinal),
            _ => unreachable!("state equality makes every other case impossible"),
        }
    }

    let feature_passages = CURRENT_FEATURES
        .into_iter()
        .map(|feature| feature_passage(feature, source, middle, target))
        .collect::<Vec<_>>();
    let feature_defect_ordinals = feature_passages
        .iter()
        .flat_map(|passage| {
            passage
                .detour_ordinals
                .iter()
                .chain(&passage.third_value_ordinals)
                .copied()
        })
        .collect::<BTreeSet<_>>();
    let mixed_retriangulations = third_states
        .iter()
        .filter(|ordinal| !feature_defect_ordinals.contains(ordinal))
        .copied()
        .collect::<Vec<_>>();

    let mut refinement_detours = Vec::new();
    let mut refinement_third_states = Vec::new();
    for ((left, center), right) in source
        .refinement_word
        .iter()
        .zip(&middle.refinement_word)
        .zip(&target.refinement_word)
    {
        if left.side == right.side && center.side != left.side {
            refinement_detours.push(left.grain);
        } else if left.side != right.side && center.side != left.side && center.side != right.side {
            refinement_third_states.push(left.grain);
        }
    }

    let first_delta = middle.representative_receiver.tau.midpoint()
        - source.representative_receiver.tau.midpoint();
    let second_delta = target.representative_receiver.tau.midpoint()
        - middle.representative_receiver.tau.midpoint();
    let direct_delta = target.representative_receiver.tau.midpoint()
        - source.representative_receiver.tau.midpoint();
    let mediated_delta = first_delta + second_delta;

    let direct_interval = target.zero_receiver.tau.subtract(&source.zero_receiver.tau);
    let mediated_interval = middle
        .zero_receiver
        .tau
        .subtract(&source.zero_receiver.tau)
        .add(&target.zero_receiver.tau.subtract(&middle.zero_receiver.tau));
    let excess_width = mediated_interval.width() - direct_interval.width();
    let detour_free = feature_defect_ordinals.is_empty()
        && refinement_detours.is_empty()
        && refinement_third_states.is_empty();

    TriangleTransport {
        from,
        via,
        to,
        direct_change_ordinals: direct,
        mediated_support_ordinals: mediated,
        first_leg_only_ordinals: first_only,
        second_leg_only_ordinals: second_only,
        detour_ordinals: detours,
        third_state_ordinals: third_states,
        mixed_retriangulation_ordinals: mixed_retriangulations,
        unchanged_ordinals: unchanged,
        feature_passages,
        refinement_detour_grains: refinement_detours,
        refinement_third_state_grains: refinement_third_states,
        endpoint_current_exact: source.current_word.len() == target.current_word.len(),
        symbolic_phase_delta_direct: direct_delta.clone(),
        symbolic_phase_delta_mediated: mediated_delta.clone(),
        symbolic_phase_control_closes: direct_delta == mediated_delta,
        detour_free_factorization: detour_free,
        interval_dependency_foil: IntervalDependencyFoil {
            direct_difference: direct_interval.clone(),
            mediated_sum: mediated_interval.clone(),
            mediated_contains_direct: interval_contains(&mediated_interval, &direct_interval),
            excess_width,
            interpretation: "The mediated interval forgets that the same intermediate zero occurs with opposite signs. Its extra width is dependency loss in the box quotient, not intrinsic transport curvature.".to_owned(),
        },
    }
}

fn build_triangles(faces: &[ReceiverFace]) -> Vec<TriangleTransport> {
    let mut triangles = Vec::new();
    for from in 0..faces.len() {
        for via in 0..faces.len() {
            for to in 0..faces.len() {
                if from == via || via == to || from == to {
                    continue;
                }
                triangles.push(triangle(faces, from, via, to));
            }
        }
    }
    triangles
}

fn grade_edge_factorizations(edges: &mut [EdgeTransport], triangles: &[TriangleTransport]) {
    for edge in edges {
        let through = triangles
            .iter()
            .filter(|triangle| {
                triangle.from == edge.from
                    && triangle.to == edge.to
                    && triangle.detour_free_factorization
            })
            .map(|triangle| triangle.via)
            .collect::<Vec<_>>();
        edge.primitive_under_receiver_words = through.is_empty();
        edge.detour_free_factorizations = through;
    }
}

fn adjacency_from_pairs(receiver_count: usize, pairs: &[(usize, usize)]) -> Vec<Vec<usize>> {
    let mut adjacency = vec![Vec::new(); receiver_count];
    for &(from, to) in pairs {
        adjacency[from].push(to);
    }
    for neighbors in &mut adjacency {
        neighbors.sort_unstable();
    }
    adjacency
}

fn simple_paths(adjacency: &[Vec<usize>], from: usize, to: usize) -> Vec<Vec<usize>> {
    fn visit(
        node: usize,
        target: usize,
        adjacency: &[Vec<usize>],
        path: &mut Vec<usize>,
        occupied: &mut BTreeSet<usize>,
        output: &mut Vec<Vec<usize>>,
    ) {
        if node == target {
            output.push(path.clone());
            return;
        }
        for &neighbor in &adjacency[node] {
            if occupied.insert(neighbor) {
                path.push(neighbor);
                visit(neighbor, target, adjacency, path, occupied, output);
                path.pop();
                occupied.remove(&neighbor);
            }
        }
    }
    let mut output = Vec::new();
    let mut occupied = BTreeSet::from([from]);
    visit(
        from,
        to,
        adjacency,
        &mut vec![from],
        &mut occupied,
        &mut output,
    );
    output.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    output
}

fn path_families_for_adjacency<F>(
    receiver_count: usize,
    adjacency: &[Vec<usize>],
    coherent: F,
) -> Vec<PrimitivePathFamily>
where
    F: Fn(&[usize]) -> bool,
{
    let mut families = Vec::new();
    for from in 0..receiver_count {
        for to in 0..receiver_count {
            if from == to {
                continue;
            }
            let paths = simple_paths(adjacency, from, to)
                .into_iter()
                .filter(|path| coherent(path))
                .collect::<Vec<_>>();
            let causal_degree = paths.first().map(|path| path.len() - 1);
            let shortest_primitive_paths = causal_degree
                .map(|degree| {
                    paths
                        .into_iter()
                        .take_while(|path| path.len() - 1 == degree)
                        .collect()
                })
                .unwrap_or_default();
            families.push(PrimitivePathFamily {
                from,
                to,
                causal_degree,
                shortest_primitive_paths,
            });
        }
    }
    families
}

fn path_is_feature_geodesic(
    path: &[usize],
    faces: &[ReceiverFace],
    feature: CurrentFeature,
) -> bool {
    let source = &faces[path[0]];
    let target = &faces[*path.last().expect("a path has a target")];
    for (ordinal_index, (source_atom, target_atom)) in source
        .current_word
        .iter()
        .zip(&target.current_word)
        .enumerate()
    {
        let source_value = feature_value(&source_atom.state, feature);
        let target_value = feature_value(&target_atom.state, feature);
        for &intermediate in path.iter().skip(1).take(path.len().saturating_sub(2)) {
            let value = feature_value(
                &faces[intermediate].current_word[ordinal_index].state,
                feature,
            );
            if value != source_value && value != target_value {
                return false;
            }
        }
    }
    true
}

fn path_is_complete_geodesic(path: &[usize], faces: &[ReceiverFace]) -> bool {
    if !CURRENT_FEATURES
        .into_iter()
        .all(|feature| path_is_feature_geodesic(path, faces, feature))
    {
        return false;
    }
    let source = &faces[path[0]];
    let target = &faces[*path.last().expect("a path has a target")];
    for (grain_index, (source_step, target_step)) in source
        .refinement_word
        .iter()
        .zip(&target.refinement_word)
        .enumerate()
    {
        for &intermediate in path.iter().skip(1).take(path.len().saturating_sub(2)) {
            let side = &faces[intermediate].refinement_word[grain_index].side;
            if side != &source_step.side && side != &target_step.side {
                return false;
            }
        }
    }
    true
}

fn build_path_families(
    receiver_count: usize,
    edges: &[EdgeTransport],
    faces: &[ReceiverFace],
) -> Vec<PrimitivePathFamily> {
    let primitive_pairs = edges
        .iter()
        .filter(|edge| edge.primitive_under_receiver_words)
        .map(|edge| (edge.from, edge.to))
        .collect::<Vec<_>>();
    let adjacency = adjacency_from_pairs(receiver_count, &primitive_pairs);
    path_families_for_adjacency(receiver_count, &adjacency, |path| {
        path_is_complete_geodesic(path, faces)
    })
}

fn feature_topologies(
    faces: &[ReceiverFace],
    triangles: &[TriangleTransport],
) -> Vec<FeatureTopology> {
    let receiver_count = faces.len();
    CURRENT_FEATURES
        .into_iter()
        .map(|feature| {
            let feature_is_detour_free = |triangle: &TriangleTransport| {
                let passage = triangle
                    .feature_passages
                    .iter()
                    .find(|passage| passage.feature == feature)
                    .expect("every triangle carries every current feature");
                passage.detour_ordinals.is_empty() && passage.third_value_ordinals.is_empty()
            };
            let detour_free_oriented_triangles = triangles
                .iter()
                .filter(|triangle| feature_is_detour_free(triangle))
                .map(|triangle| (triangle.from, triangle.via, triangle.to))
                .collect::<Vec<_>>();
            let curved_oriented_triangles = triangles
                .iter()
                .filter(|triangle| !feature_is_detour_free(triangle))
                .map(|triangle| (triangle.from, triangle.via, triangle.to))
                .collect::<Vec<_>>();
            let mut primitive_edges = Vec::new();
            let mut reducible_edges = Vec::new();
            for from in 0..receiver_count {
                for to in 0..receiver_count {
                    if from == to {
                        continue;
                    }
                    let through = triangles
                        .iter()
                        .filter(|triangle| {
                            triangle.from == from
                                && triangle.to == to
                                && feature_is_detour_free(triangle)
                        })
                        .map(|triangle| triangle.via)
                        .collect::<Vec<_>>();
                    if through.is_empty() {
                        primitive_edges.push((from, to));
                    } else {
                        reducible_edges.push(ReducibleEdge { from, to, through });
                    }
                }
            }
            let adjacency = adjacency_from_pairs(receiver_count, &primitive_edges);
            let primitive_path_families =
                path_families_for_adjacency(receiver_count, &adjacency, |path| {
                    path_is_feature_geodesic(path, faces, feature)
                });
            FeatureTopology {
                feature,
                primitive_edges,
                reducible_edges,
                detour_free_oriented_triangles,
                curved_oriented_triangles,
                primitive_path_families,
            }
        })
        .collect()
}

fn structural_read(
    faces: &[ReceiverFace],
    edges: &[EdgeTransport],
    triangles: &[TriangleTransport],
    paths: &[PrimitivePathFamily],
) -> StructuralRead {
    StructuralRead {
        receiver_ordinals: faces.iter().map(|face| face.ordinal).collect(),
        primitive_edges: edges
            .iter()
            .filter(|edge| edge.primitive_under_receiver_words)
            .map(|edge| (edge.from, edge.to))
            .collect(),
        reducible_edges: edges
            .iter()
            .filter(|edge| !edge.primitive_under_receiver_words)
            .map(|edge| ReducibleEdge {
                from: edge.from,
                to: edge.to,
                through: edge.detour_free_factorizations.clone(),
            })
            .collect(),
        detour_free_oriented_triangles: triangles
            .iter()
            .filter(|triangle| triangle.detour_free_factorization)
            .map(|triangle| (triangle.from, triangle.via, triangle.to))
            .collect(),
        curved_oriented_triangles: triangles
            .iter()
            .filter(|triangle| !triangle.detour_free_factorization)
            .map(|triangle| (triangle.from, triangle.via, triangle.to))
            .collect(),
        unreachable_through_primitive_edges: paths
            .iter()
            .filter(|path| path.causal_degree.is_none())
            .map(|path| (path.from, path.to))
            .collect(),
        feature_topologies: feature_topologies(faces, triangles),
    }
}

fn source_hash(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    format!("{:x}", digest.finalize())
}

fn build_report(bytes: &[u8], atlas: &SourceAtlas) -> Result<ZeroTransportComplex, String> {
    require(
        atlas.schema == "laboratory.holonic-eta-ratio-atlas.v1",
        "the source is not the expected eta ratio atlas",
    )?;
    require(
        atlas.zero_lineages.len() >= 3,
        "a transport complex requires at least three receiver lineages",
    )?;
    let source_ordinals = source_ordinals(&atlas.zero_lineages)?;
    let receiver_faces = build_receiver_faces(&atlas.zero_lineages)?;
    let mut edge_transports = build_edges(&receiver_faces);
    let triangle_transports = build_triangles(&receiver_faces);
    require(
        triangle_transports
            .iter()
            .all(|triangle| triangle.symbolic_phase_control_closes),
        "the exact midpoint phase-difference control failed to compose",
    )?;
    require(
        triangle_transports
            .iter()
            .all(|triangle| triangle.endpoint_current_exact),
        "a triangle does not return the declared endpoint current",
    )?;
    require(
        triangle_transports.iter().all(|triangle| {
            triangle.interval_dependency_foil.mediated_contains_direct
                && !triangle.interval_dependency_foil.excess_width.is_negative()
        }),
        "an interval dependency foil does not contain its direct difference",
    )?;
    grade_edge_factorizations(&mut edge_transports, &triangle_transports);
    let primitive_path_families =
        build_path_families(receiver_faces.len(), &edge_transports, &receiver_faces);
    let structural_read = structural_read(
        &receiver_faces,
        &edge_transports,
        &triangle_transports,
        &primitive_path_families,
    );

    Ok(ZeroTransportComplex {
        schema: "laboratory.holonic-zero-transport-complex.v1".to_owned(),
        source_schema: atlas.schema.clone(),
        source_sha256: source_hash(bytes),
        arithmetic: format!(
            "{}; this derived complex uses only exact integer, rational, interval, sign, and finite-word operations",
            atlas.arithmetic
        ),
        boundary: "Five independently certified zero-bearing receivers are the vertices. Their rational midpoint eta currents are representative receiver faces, not substituted zero coordinates. Pair transport is the complete ordered change of those faces. Each six-feature atom remains whole in testimony, while compositional grading is feature-local: recombining endpoint features is retriangulation; leaving and returning or assuming a third feature value is an interior defect. Interval-width growth is separately typed as quotient dependency loss.".to_owned(),
        source_ordinals,
        receiver_faces,
        edge_transports,
        triangle_transports,
        primitive_path_families,
        structural_read,
    })
}

fn read_source(path: &Path) -> Result<(Vec<u8>, SourceAtlas), String> {
    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    let encoded = std::str::from_utf8(&bytes).map_err(|error| error.to_string())?;
    let atlas = ron::from_str(encoded).map_err(|error| error.to_string())?;
    Ok((bytes, atlas))
}

fn write_report(path: &Path, report: &ZeroTransportComplex) -> Result<(), String> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    let pretty = ron::ser::PrettyConfig::new()
        .depth_limit(128)
        .separate_tuple_members(true)
        .enumerate_arrays(true);
    let encoded = ron::ser::to_string_pretty(report, pretty).map_err(|error| error.to_string())?;
    fs::write(path, encoded).map_err(|error| error.to_string())
}

fn verify(source: &Path, report_path: &Path) -> Result<(), String> {
    let (source_bytes, source_atlas) = read_source(source)?;
    let expected = build_report(&source_bytes, &source_atlas)?;
    let encoded = fs::read_to_string(report_path).map_err(|error| error.to_string())?;
    let stored: ZeroTransportComplex =
        ron::from_str(&encoded).map_err(|error| error.to_string())?;
    require(
        stored == expected,
        "the stored transport complex does not re-derive",
    )?;
    println!(
        "VERIFIED schema={} receivers={} edges={} triangles={} primitive_edges={} curved_triangles={}",
        stored.schema,
        stored.receiver_faces.len(),
        stored.edge_transports.len(),
        stored.triangle_transports.len(),
        stored.structural_read.primitive_edges.len(),
        stored.structural_read.curved_oriented_triangles.len(),
    );
    Ok(())
}

fn defined_feature_ordinals(
    report: &ZeroTransportComplex,
    triangle: &TriangleTransport,
    feature: CurrentFeature,
) -> Vec<u32> {
    let source = &report.receiver_faces[triangle.from];
    let middle = &report.receiver_faces[triangle.via];
    let target = &report.receiver_faces[triangle.to];
    source
        .current_word
        .iter()
        .zip(&middle.current_word)
        .zip(&target.current_word)
        .filter_map(|((left, center), right)| {
            (feature_value(&left.state, feature).is_some()
                && feature_value(&center.state, feature).is_some()
                && feature_value(&right.state, feature).is_some())
            .then_some(left.ordinal)
        })
        .collect()
}

fn maximal_coherent_spans(
    report: &ZeroTransportComplex,
    triangle: &TriangleTransport,
    passage: &FeaturePassage,
) -> Vec<(u32, u32)> {
    let defects = passage
        .detour_ordinals
        .iter()
        .chain(&passage.third_value_ordinals)
        .copied()
        .collect::<BTreeSet<_>>();
    let coherent = defined_feature_ordinals(report, triangle, passage.feature)
        .into_iter()
        .filter(|ordinal| !defects.contains(ordinal))
        .collect::<Vec<_>>();
    let mut spans = Vec::new();
    for ordinal in coherent {
        match spans.last_mut() {
            Some((_, end)) if ordinal == *end + 1 => *end = ordinal,
            _ => spans.push((ordinal, ordinal)),
        }
    }
    spans
}

fn factorization(report: &ZeroTransportComplex, ordinal: u32) -> String {
    let source = report
        .source_ordinals
        .iter()
        .find(|source| source.ordinal == ordinal)
        .expect("every current ordinal has source testimony");
    if source.prime_valuations.is_empty() {
        return ordinal.to_string();
    }
    source
        .prime_valuations
        .iter()
        .map(|valuation| {
            if valuation.exponent == 1 {
                valuation.prime.to_string()
            } else {
                format!("{}^{}", valuation.prime, valuation.exponent)
            }
        })
        .collect::<Vec<_>>()
        .join("*")
}

fn formatted_ordinal_support(report: &ZeroTransportComplex, ordinals: &[u32]) -> String {
    ordinals
        .iter()
        .map(|ordinal| format!("{ordinal}={}", factorization(report, *ordinal)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn changed_feature_support(
    left: &ReceiverFace,
    right: &ReceiverFace,
    feature: CurrentFeature,
) -> Vec<u32> {
    left.current_word
        .iter()
        .zip(&right.current_word)
        .filter_map(|(left, right)| {
            (feature_value(&left.state, feature) != feature_value(&right.state, feature))
                .then_some(left.ordinal)
        })
        .collect()
}

fn pair_support_signature(left: &ReceiverFace, right: &ReceiverFace) -> (Vec<Vec<u32>>, Vec<u32>) {
    let features = CURRENT_FEATURES
        .into_iter()
        .map(|feature| changed_feature_support(left, right, feature))
        .collect();
    let refinements = left
        .refinement_word
        .iter()
        .zip(&right.refinement_word)
        .filter_map(|(left, right)| (left.side != right.side).then_some(left.grain))
        .collect();
    (features, refinements)
}

fn summarize(report_path: &Path) -> Result<(), String> {
    let encoded = fs::read_to_string(report_path).map_err(|error| error.to_string())?;
    let report: ZeroTransportComplex =
        ron::from_str(&encoded).map_err(|error| error.to_string())?;
    println!(
        "COMPLEX schema={} receivers={} exact_current_extent={}",
        report.schema,
        report.receiver_faces.len(),
        report
            .receiver_faces
            .first()
            .map(|face| face.current_word.len())
            .unwrap_or(0),
    );
    for face in &report.receiver_faces {
        let negative_turns = face
            .current_word
            .iter()
            .filter(|atom| atom.state.turn_to_successor == Some(CertifiedSign::Negative))
            .map(|atom| atom.ordinal)
            .collect::<Vec<_>>();
        println!(
            "RECEIVER {} tau={} negative_turns=[{}]",
            face.ordinal,
            face.zero_receiver.tau,
            formatted_ordinal_support(&report, &negative_turns),
        );
    }
    let phase_controls_close = report
        .triangle_transports
        .iter()
        .filter(|triangle| triangle.symbolic_phase_control_closes)
        .count();
    let interval_excesses = report
        .triangle_transports
        .iter()
        .map(|triangle| format_rat(&triangle.interval_dependency_foil.excess_width))
        .collect::<BTreeSet<_>>();
    println!(
        "CONTROLS phase_telescopes={}/{} interval_excesses={:?}",
        phase_controls_close,
        report.triangle_transports.len(),
        interval_excesses,
    );
    println!(
        "WHOLE_FACE primitive_edges={} reducible_edges={} detour_free_triangles={} curved_triangles={}",
        report.structural_read.primitive_edges.len(),
        report.structural_read.reducible_edges.len(),
        report.structural_read.detour_free_oriented_triangles.len(),
        report.structural_read.curved_oriented_triangles.len(),
    );
    let mut pair_signatures = Vec::new();
    for from in 0..report.receiver_faces.len() {
        for to in (from + 1)..report.receiver_faces.len() {
            let left = &report.receiver_faces[from];
            let right = &report.receiver_faces[to];
            let (feature_supports, refinement_support) = pair_support_signature(left, right);
            let turn_support = &feature_supports[4];
            let edge = report
                .edge_transports
                .iter()
                .find(|edge| edge.from == from && edge.to == to)
                .expect("every ordered receiver pair has an edge");
            println!(
                "PAIR {}<->{} delta_tau={} refinement_grains={:?} feature_change_extents={:?} turn_support=[{}]",
                from,
                to,
                edge.zero_ordinate_difference_receiver,
                refinement_support,
                feature_supports.iter().map(Vec::len).collect::<Vec<_>>(),
                formatted_ordinal_support(&report, turn_support),
            );
            pair_signatures.push(((from, to), (feature_supports, refinement_support)));
        }
    }
    let pair_collisions = pair_signatures
        .iter()
        .enumerate()
        .flat_map(|(left_index, (left_pair, left_signature))| {
            pair_signatures.iter().skip(left_index + 1).filter_map(
                move |(right_pair, right_signature)| {
                    (left_signature == right_signature).then_some((*left_pair, *right_pair))
                },
            )
        })
        .collect::<Vec<_>>();
    println!(
        "PAIR_SUPPORT_IDENTITY unordered_pairs={} collisions={:?}",
        pair_signatures.len(),
        pair_collisions,
    );
    for topology in &report.structural_read.feature_topologies {
        let third_value_passages = report
            .triangle_transports
            .iter()
            .filter_map(|triangle| {
                let passage = triangle
                    .feature_passages
                    .iter()
                    .find(|passage| passage.feature == topology.feature)
                    .expect("every triangle carries every feature");
                (!passage.third_value_ordinals.is_empty()).then_some((
                    triangle.from,
                    triangle.via,
                    triangle.to,
                    passage.third_value_ordinals.clone(),
                ))
            })
            .collect::<Vec<_>>();
        println!(
            "FEATURE {:?} primitive_edges={} reducible_edges={:?} detour_free_triangles={} curved_triangles={} third_value_passages={:?}",
            topology.feature,
            topology.primitive_edges.len(),
            topology.reducible_edges,
            topology.detour_free_oriented_triangles.len(),
            topology.curved_oriented_triangles.len(),
            third_value_passages,
        );
        for edge in &topology.reducible_edges {
            for &via in &edge.through {
                let triangle = report
                    .triangle_transports
                    .iter()
                    .find(|triangle| {
                        triangle.from == edge.from && triangle.via == via && triangle.to == edge.to
                    })
                    .expect("a reducible edge names an existing triangle");
                let passage = triangle
                    .feature_passages
                    .iter()
                    .find(|passage| passage.feature == topology.feature)
                    .expect("every triangle carries every feature");
                println!(
                    "  FACTORIZATION {}->{}->{} first=[{}] second=[{}] detours={:?} third={:?} whole_detours={:?} whole_third={:?} mixed_retriangulations={:?}",
                    edge.from,
                    via,
                    edge.to,
                    formatted_ordinal_support(&report, &passage.first_leg_only_ordinals),
                    formatted_ordinal_support(&report, &passage.second_leg_only_ordinals),
                    passage.detour_ordinals,
                    passage.third_value_ordinals,
                    triangle.detour_ordinals,
                    triangle.third_state_ordinals,
                    triangle.mixed_retriangulation_ordinals,
                );
            }
        }
        for family in topology
            .primitive_path_families
            .iter()
            .filter(|family| family.causal_degree != Some(1))
        {
            println!(
                "  COHERENT_PATH {}->{} degree={:?} paths={:?}",
                family.from, family.to, family.causal_degree, family.shortest_primitive_paths,
            );
        }

        let mut local = report
            .triangle_transports
            .iter()
            .map(|triangle| {
                let passage = triangle
                    .feature_passages
                    .iter()
                    .find(|passage| passage.feature == topology.feature)
                    .expect("every triangle carries every feature");
                let spans = maximal_coherent_spans(&report, triangle, passage);
                let longest = spans
                    .iter()
                    .map(|(start, end)| end - start + 1)
                    .max()
                    .unwrap_or(0);
                (
                    longest,
                    triangle.from,
                    triangle.via,
                    triangle.to,
                    spans,
                    passage.detour_ordinals.clone(),
                    passage.third_value_ordinals.clone(),
                )
            })
            .collect::<Vec<_>>();
        local.sort_by(|left, right| {
            right
                .0
                .cmp(&left.0)
                .then((left.1, left.2, left.3).cmp(&(right.1, right.2, right.3)))
        });
        for (extent, from, via, to, spans, detours, third) in local.into_iter().take(3) {
            println!(
                "  LOCAL {}->{}->{} longest={} spans={:?} defects={:?} third={:?}",
                from, via, to, extent, spans, detours, third,
            );
        }
    }
    Ok(())
}

fn print_read(report: &ZeroTransportComplex, output: &Path) {
    println!(
        "exact zero transport: receivers={} edges={} oriented_triangles={}",
        report.receiver_faces.len(),
        report.edge_transports.len(),
        report.triangle_transports.len(),
    );
    println!(
        "primitive_edges={:?}",
        report.structural_read.primitive_edges
    );
    println!(
        "reducible_edges={:?}",
        report.structural_read.reducible_edges
    );
    println!(
        "detour_free_triangles={:?}",
        report.structural_read.detour_free_oriented_triangles
    );
    println!(
        "curved_triangles={:?}",
        report.structural_read.curved_oriented_triangles
    );
    for topology in &report.structural_read.feature_topologies {
        println!(
            "FEATURE {:?} primitive_edges={:?} reducible_edges={:?} detour_free_triangles={:?} curved_triangles={:?}",
            topology.feature,
            topology.primitive_edges,
            topology.reducible_edges,
            topology.detour_free_oriented_triangles,
            topology.curved_oriented_triangles,
        );
    }
    let mut ranked = report.triangle_transports.iter().collect::<Vec<_>>();
    ranked.sort_by(|left, right| {
        let left_extent = left
            .feature_passages
            .iter()
            .map(|passage| passage.detour_ordinals.len() + passage.third_value_ordinals.len())
            .sum::<usize>()
            + left.refinement_detour_grains.len()
            + left.refinement_third_state_grains.len();
        let right_extent = right
            .feature_passages
            .iter()
            .map(|passage| passage.detour_ordinals.len() + passage.third_value_ordinals.len())
            .sum::<usize>()
            + right.refinement_detour_grains.len()
            + right.refinement_third_state_grains.len();
        right_extent
            .cmp(&left_extent)
            .then((left.from, left.via, left.to).cmp(&(right.from, right.via, right.to)))
    });
    for triangle in ranked.into_iter().take(12) {
        println!(
            "TRIANGLE {}->{}->{} joint_detours={:?} joint_third_states={:?} mixed_retriangulations={:?} refinement_detours={:?} interval_excess={}",
            triangle.from,
            triangle.via,
            triangle.to,
            triangle.detour_ordinals,
            triangle.third_state_ordinals,
            triangle.mixed_retriangulation_ordinals,
            triangle.refinement_detour_grains,
            format_rat(&triangle.interval_dependency_foil.excess_width),
        );
        for passage in &triangle.feature_passages {
            if passage.detour_ordinals.is_empty() && passage.third_value_ordinals.is_empty() {
                continue;
            }
            println!(
                "  {:?} detours={:?} third_values={:?}",
                passage.feature, passage.detour_ordinals, passage.third_value_ordinals,
            );
        }
    }
    for family in &report.primitive_path_families {
        println!(
            "PATH {}->{} degree={:?} words={:?}",
            family.from, family.to, family.causal_degree, family.shortest_primitive_paths,
        );
    }
    println!("artifact={}", output.display());
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments.first().map(String::as_str) == Some("summarize") {
        let report = arguments
            .get(1)
            .map(PathBuf::from)
            .ok_or_else(|| "summarize requires the transport report".to_owned())?;
        return summarize(&report);
    }
    if arguments.first().map(String::as_str) == Some("verify") {
        let source = arguments
            .get(1)
            .map(PathBuf::from)
            .ok_or_else(|| "verify requires the raw source atlas".to_owned())?;
        let report = arguments
            .get(2)
            .map(PathBuf::from)
            .ok_or_else(|| "verify requires the transport report".to_owned())?;
        return verify(&source, &report);
    }
    let source = arguments
        .first()
        .map(PathBuf::from)
        .ok_or_else(|| "generation requires the raw source atlas".to_owned())?;
    let output = arguments
        .get(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("holonic-zero-transport-complex.ron"));
    let (source_bytes, source_atlas) = read_source(&source)?;
    let report = build_report(&source_bytes, &source_atlas)?;
    write_report(&output, &report)?;
    print_read(&report, &output);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state(value: CertifiedSign) -> CurrentState {
        CurrentState {
            contribution_real: value,
            contribution_imaginary: CertifiedSign::Positive,
            partial_real: CertifiedSign::Positive,
            partial_imaginary: CertifiedSign::Positive,
            turn_to_successor: Some(CertifiedSign::Positive),
            radial_change_to_successor: Some(CertifiedSign::Negative),
        }
    }

    #[test]
    fn a_mediated_excursion_is_not_endpoint_curvature() {
        let source = state(CertifiedSign::Negative);
        let middle = state(CertifiedSign::Positive);
        let target = state(CertifiedSign::Negative);
        assert_eq!(source, target);
        assert_ne!(source, middle);
        assert_ne!(middle, target);
    }

    #[test]
    fn exact_midpoint_differences_telescope() {
        let a = relational_geometry::rat(113, 8);
        let b = relational_geometry::rat(1345, 64);
        let c = relational_geometry::rat(25, 1);
        assert_eq!((&b - &a) + (&c - &b), c - a);
    }

    #[test]
    fn box_subtraction_loses_shared_dependency() {
        let a = RatInterval::new(
            relational_geometry::rat(0, 1),
            relational_geometry::rat(1, 1),
        );
        let b = RatInterval::new(
            relational_geometry::rat(2, 1),
            relational_geometry::rat(3, 1),
        );
        let c = RatInterval::new(
            relational_geometry::rat(4, 1),
            relational_geometry::rat(5, 1),
        );
        let direct = c.subtract(&a);
        let mediated = b.subtract(&a).add(&c.subtract(&b));
        assert!(interval_contains(&mediated, &direct));
        assert!(mediated.width() > direct.width());
    }

    #[test]
    fn turn_is_the_exact_oriented_area_determinant() {
        let east = ComplexInterval::point(relational_geometry::RatComplex::new(
            relational_geometry::rat(1, 1),
            relational_geometry::rat(0, 1),
        ));
        let north = ComplexInterval::point(relational_geometry::RatComplex::new(
            relational_geometry::rat(0, 1),
            relational_geometry::rat(1, 1),
        ));
        assert_eq!(turn(&east, &north), CertifiedSign::Positive);
        assert_eq!(turn(&north, &east), CertifiedSign::Negative);
        assert_eq!(turn(&east, &east), CertifiedSign::Zero);
    }
}
