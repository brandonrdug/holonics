use std::collections::BTreeMap;

/// One complete native ordered-word trace returned from the card after one terminal read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceNativeTrace {
    /// Row-major `[starting occurrence][word boundary]`, including the entering state.
    pub native_trace: Vec<u32>,
    pub trace_stride: usize,
    pub starting_occurrences: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Plural ordered words and their exact ragged traces returned by one resident card front.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceRaggedNativeTrace {
    /// Concatenated traces. Each interval is selected by `trace_offsets[i..=i + 1]`.
    pub native_trace: Vec<u32>,
    pub trace_offsets: Vec<u32>,
    pub front_count: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Every finite predecessor/successor/ablation recurrence returned after one exterior difference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceReturnedRecurrences {
    /// Row-major traces with stride `state_count + 1`; each length selects its exact prefix.
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub ablated_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub ablated_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub committed: bool,
    pub control_predecessor: u32,
    pub control_successor: u32,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One returned receiver covector and its complete local cultivation passages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceDynamicMorphology {
    pub returned_adjoint: Vec<i64>,
    pub predecessor_action: Vec<u32>,
    pub successor_action: Vec<u32>,
    pub withdrawn_action: Vec<u32>,
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub committed: bool,
    pub supported_state: Option<u32>,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Compact successor, predecessor route, and shared-generator withdrawal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceCondensedRecurrences {
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub visited_words: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One shared heterogeneous generator and its global and local withdrawals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceHeterogeneousFusion {
    /// Family-major, port-major cells.
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    /// Row-major `[cell][withdrawn port]`.
    pub local_ablated_consequence: Vec<u32>,
    pub families: usize,
    pub ports: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Complete source correspondence multiplicity at each anchor/port cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceMediaCandidateCounts {
    /// Anchor-major, port-minor.
    pub candidate_counts: Vec<u32>,
    pub anchors: usize,
    pub ports: usize,
    pub pairs: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_pair_visits: u128,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Compact joint-media consequence and shared/local withdrawals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceJointMediaTransport {
    pub joint_anchor: Vec<u32>,
    pub shared_ablated_joint_anchor: Vec<u32>,
    /// Anchor-major, withdrawn-port-minor.
    pub local_ablated_joint_anchor: Vec<u32>,
    /// Family-major, port-major cells.
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    /// Cell-major, withdrawn-port-minor.
    pub local_ablated_consequence: Vec<u32>,
    pub anchors: usize,
    pub families: usize,
    pub ports: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Retained-context, derivation, and mathematical-media fronts after typed reduction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceProductionAperture {
    pub context_trace: Vec<u32>,
    pub context_boundary_withdrawn_trace: Vec<u32>,
    pub context_trace_stride: usize,
    pub derivation_predecessor_trace: Vec<u32>,
    pub derivation_successor_trace: Vec<u32>,
    pub derivation_selected_trace: Vec<u32>,
    pub derivation_generator_withdrawn_trace: Vec<u32>,
    pub derivation_predecessor_lengths: Vec<u32>,
    pub derivation_successor_lengths: Vec<u32>,
    pub derivation_selected_lengths: Vec<u32>,
    pub derivation_generator_withdrawn_lengths: Vec<u32>,
    pub derivation_trace_stride: usize,
    pub media_species_totals: Vec<u64>,
    pub media_shared_withdrawn_totals: Vec<u64>,
    /// Species-major, withdrawn-port-minor.
    pub media_local_withdrawn_totals: Vec<u64>,
    pub media_joint_anchors: u64,
    pub total_joint_incidence: u64,
    pub oriented_difference: i64,
    pub difference_magnitude: u64,
    pub difference_hand: i32,
    pub selected_cultivation_state: u32,
    pub context_fronts: usize,
    pub derivation_fronts: usize,
    pub media_anchors: usize,
    pub media_species: usize,
    pub media_ports: usize,
    pub committed: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Homogeneous quadratic sections transported through complete integer chart maps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceQuadraticSectionTransport {
    /// Section-major `(x^2, xy, y^2)` coefficient faces after substitution.
    pub transported_coefficients: Vec<i64>,
    pub invariant: Vec<u32>,
    /// `0` expanded coefficient route, `1` cultivated condensed route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub sections: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Multiple exact fixed-section families and their complete withdrawals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceFixedSectionFamilies {
    /// Family-major exact returned coordinates.
    pub transported_sections: Vec<i64>,
    pub constraint_held: Vec<u32>,
    pub invariant: Vec<u32>,
    /// `0` expanded action, `1` cultivated fixed-section route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub joint_cultivated: bool,
    /// One entry per locally withdrawn family.
    pub local_ablated_joint: Vec<u32>,
    pub families: usize,
    pub dimension: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub predicted_local_semantic_work: Vec<u64>,
    pub predicted_local_semantic_span: Vec<u64>,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Fixed-section families after repeated dense actions condense into one shared relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceNativeFixedSectionFamilies {
    pub transported_sections: Vec<i64>,
    pub constraint_residuals: Vec<i64>,
    pub constraint_held: Vec<u32>,
    pub invariant: Vec<u32>,
    /// `0` expanded native generator, `1` cultivated fixed-section route, `2` obstruction.
    pub selected_route: Vec<u32>,
    pub ablated_route: Vec<u32>,
    pub joint_cultivated: bool,
    pub local_ablated_joint: Vec<u32>,
    pub families: usize,
    pub dimension: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub predicted_local_semantic_work: Vec<u64>,
    pub predicted_local_semantic_span: Vec<u64>,
    pub semantic_work: u128,
    pub semantic_span: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// Recurrent physical passage and all admitted heterogeneous faces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceInferenceEcology {
    pub predecessor_trace: Vec<u32>,
    pub successor_trace: Vec<u32>,
    pub withdrawn_trace: Vec<u32>,
    pub selected_trace: Vec<u32>,
    pub predecessor_lengths: Vec<u32>,
    pub successor_lengths: Vec<u32>,
    pub withdrawn_lengths: Vec<u32>,
    pub selected_lengths: Vec<u32>,
    pub trace_stride: usize,
    pub predecessor_consequence: Vec<u32>,
    pub successor_consequence: Vec<u32>,
    pub selected_consequence: Vec<u32>,
    pub shared_ablated_consequence: Vec<u32>,
    pub local_ablated_consequence: Vec<u32>,
    pub families: usize,
    pub ports: usize,
    pub committed: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub active_lanes: u32,
    pub visited_words: usize,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One addressed material/operation pullback and unchanged I5 conduct.
#[derive(Debug, PartialEq, Eq)]
pub struct DeviceMaterialOperationWorldTube {
    pub payload_classes: Vec<u32>,
    pub payload_comparisons: Vec<u32>,
    pub face_staging_events: Vec<u64>,
    pub face_terminal_events: Vec<u64>,
    pub contact_left_classes: Vec<u32>,
    pub contact_right_classes: Vec<u32>,
    pub contact_relations: Vec<u32>,
    pub recurrence_staging_events: Vec<u64>,
    pub recurrence_terminal_events: Vec<u64>,
    pub inference: DeviceInferenceEcology,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One exact contact population and its matched cross-presentation successor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceContactPassage {
    pub contact_classes: Vec<u8>,
    pub paired_classes: Vec<u8>,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// One complete pair population with contact and simultaneous optical-role words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceOpticalIncidencePassage {
    pub contact_classes: Vec<u8>,
    pub incidence_words: Vec<u32>,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
}

/// What the card returned for one surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceSaturation {
    pub horizon: usize,
    pub classes: usize,
    pub shells: usize,
    pub classes_at_one: usize,
    /// The final class of every site, in the order the sites were supplied.
    pub site_class: Vec<u32>,
}

/// Which chart of the cover enacted a quotient. A realization coordinate, never a holon.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotientCarrier {
    Cpu,
    Device,
}

/// One step of an exact quotient: dense class of every cell and its population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quotient {
    pub cell_class: Vec<u32>,
    pub classes: usize,
    pub carrier: QuotientCarrier,
}

impl Quotient {
    /// True when two quotients induce the same equivalence on cells.
    pub fn same_partition_as(&self, other: &Quotient) -> bool {
        if self.cell_class.len() != other.cell_class.len() || self.classes != other.classes {
            return false;
        }
        let mut forward: BTreeMap<u32, u32> = BTreeMap::new();
        let mut backward: BTreeMap<u32, u32> = BTreeMap::new();
        for (mine, theirs) in self.cell_class.iter().zip(&other.cell_class) {
            if *forward.entry(*mine).or_insert(*theirs) != *theirs
                || *backward.entry(*theirs).or_insert(*mine) != *mine
            {
                return false;
            }
        }
        true
    }
}

/// The exact quotient on the cpu. The reference every carrier is required to equal.
pub fn quotient_on_cpu(classes: &[u32], keys: &[u64]) -> Quotient {
    let mut dense: BTreeMap<(u32, u64), u32> = BTreeMap::new();
    let mut cell_class = Vec::with_capacity(classes.len());
    for (class, key) in classes.iter().zip(keys) {
        let next = dense.len() as u32 + 1;
        cell_class.push(*dense.entry((*class, *key)).or_insert(next));
    }
    Quotient {
        classes: dense.len(),
        cell_class,
        carrier: QuotientCarrier::Cpu,
    }
}
