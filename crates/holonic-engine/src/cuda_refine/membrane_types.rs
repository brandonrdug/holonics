use crate::ExactComplexWaveCurrent;
use crate::addressed_current::{
    AddressedCurrentPassage, AddressedCurrentSection, AddressedGeneratedPortJunctionPassage,
};
use crate::exact_linear::ExactRatMatrix;
use crate::factored_moment::{
    AddressedDiagonalCurrentStep, FactoredMomentFoundation, FactoredMomentSection,
    SparseQuadraticMomentFoundation,
};
use num_bigint::{BigInt, BigUint};
use relational_geometry::Rat;
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ResidentMembraneInteriorReturn {
    pub left_cell: u32,
    pub right_cell: u32,
    pub family_overlaps: Vec<Rat>,
    pub native_radiation: ExactComplexWaveCurrent,
    pub injected_boundary_current: ExactComplexWaveCurrent,
    pub returned_radiation: ExactComplexWaveCurrent,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub cell_selected_or_ranked: bool,
    pub boundary_injection_depended_on_native_radiation: bool,
}

/// One recurrent fine-boundary support conducted by the already-resident membrane constitution.
/// Exterior factor arrays are successor incidence, not a host evaluation of the constitutive law.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactorSupportBoundaryReturn {
    pub context_factors: Vec<u32>,
    pub context_factor_currents: Vec<(u32, u64)>,
    pub target_factors: Vec<u32>,
    pub recurrence_multiplicity: u64,
    pub family_overlaps: Vec<Rat>,
    pub returned_response: ExactComplexWaveCurrent,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// One support of a complete oriented boundary section.  `port` is an apparatus-local address;
/// every support in the joint call is conducted before any port current returns to the host.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentBoundaryChainSupport {
    pub port: u32,
    /// Exact second moment multiplying reflected self-contact.
    pub reflected_quadratic_scale: BigUint,
    /// Exact moment multiplying reflected/action contact and receiver overlap.
    pub action_pair_scale: BigUint,
    /// Exact second moment multiplying action self-contact.
    pub action_quadratic_scale: BigUint,
    /// The entering boundary potential reflected into the native factor chart.
    pub reflected_factor_current: Vec<(u32, BigUint)>,
    /// Primitive signed coordinates of `U_i J - J`, already scaled back to the exact integral
    /// action section by the caller.  An empty section is the exact zero action difference.
    pub action_factor_current: Vec<(u32, BigInt)>,
}

/// The addressed occurrence of one current population resident inside the operation complex.
/// This is continuation testimony, not ownership of the buffers and not identity by digest alone.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentCurrentAddress {
    pub operation_complex_identity_sha256: String,
    pub device_context_identity: usize,
    pub generation: u64,
    pub section_population: usize,
}

/// The addressed occurrence of one exact factored-moment image resident inside the operation
/// complex.  Derived image population replaces source-family population in the hot address.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentAddress {
    pub operation_complex_identity_sha256: String,
    pub section_identity_sha256: String,
    pub device_context_identity: usize,
    pub generation: u64,
    pub factor_population: u32,
    pub image_population: u32,
}

/// Foundation return for the native image occurrence.  The complete source family and its
/// source-to-image map remain cold reconstruction testimony in `foundation`; `target_address`
/// alone addresses the hot resident state.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentFoundationReturn {
    pub foundation: FactoredMomentFoundation,
    pub target_address: ResidentFactoredMomentAddress,
    pub device: String,
    pub context_identity: usize,
    pub host_ingress_octets: u64,
    pub resident_octets: u64,
    pub source_current_retained_hot: bool,
    pub ambient_covariance_materialized: bool,
}

/// Foundation return for the fixed native symmetric pair-current.  The source occurrence family
/// remains solely in the cold reconstruction fibre; the hot address names only the derived pair
/// carrier and its exact coefficient current.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSparseQuadraticMomentFoundationReturn {
    pub foundation: SparseQuadraticMomentFoundation,
    /// Present when a source-neutral relational current crossed the mounted sparse incidence and
    /// joined this root-state quadratic section before recurrence. The receipt is structural
    /// testimony; the signed factor current remains resident as the reconstruction fibre.
    pub relational_current: Option<ResidentSparseRelationalCurrentReceipt>,
    pub target_address: ResidentFactoredMomentAddress,
    pub device: String,
    pub context_identity: usize,
    pub host_ingress_octets: u64,
    pub resident_octets: u64,
    pub source_current_retained_hot: bool,
    pub ambient_covariance_materialized: bool,
}

/// Cold apparatus chart of the source-neutral relational holons. Every term retains the three
/// chronological phase populations; the resident kernel derives the two-coordinate quotient
/// `(emanation - ingress, return - ingress)` rather than accepting a caller-authored phase angle.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSparseRelationalCurrentAtlas {
    pub identity_sha256: String,
    pub row_offsets: Vec<u64>,
    pub term_factors: Vec<u32>,
    pub term_ingress_population: Vec<u64>,
    pub term_emanation_population: Vec<u64>,
    pub term_return_population: Vec<u64>,
    /// Complete row addresses in the same order as `row_offsets`. They are reconstruction
    /// testimony only and never enter CUDA addressing or native equality by their spelling.
    pub row_reconstruction_addresses: Vec<String>,
}

/// Exact resident receipt for one `X -> B X -> K(B X) -> B^dagger K B X` passage. Positive
/// projective ingress and the returned signed two-coordinate current remain different carrier
/// faces. The signed current may join only as an addressed receiver of the evolving target-fibre
/// current; `root_positive_collapse` must therefore remain false.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSparseRelationalCurrentReceipt {
    pub schema: String,
    pub incidence_identity_sha256: String,
    pub incidence_population: u64,
    pub row_population: u32,
    pub factor_population: u32,
    pub constitutive_family_population: u32,
    pub constitutive_family_identity_sha256: String,
    pub causal_adjoint_identity_sha256: String,
    pub source_current_identity_sha256: String,
    pub returned_current_identity_sha256: String,
    pub addressed_state_identity_sha256: String,
    pub addressed_state_population: usize,
    pub present_state_population: usize,
    pub root_state: u32,
    pub returned_factor_bound: BigUint,
    pub factor_limb_count: usize,
    pub receiver_radical: bool,
    pub local_balance_closes: bool,
    pub root_positive_collapse: bool,
    pub addressed_target_receiver_joined: bool,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Foundation return for a fixed pair current formed directly from ordered native diagonal
/// crossings. The chronology and generator presentation are cold reconstruction testimony; the
/// hot state owns only the fixed action and its accumulated coefficient section.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSparseQuadraticChronologyFoundationReturn {
    pub schema: String,
    pub chronology_reconstruction_fibre: Vec<AddressedDiagonalCurrentStep>,
    pub generator_targets: Vec<Vec<u32>>,
    pub target_address: ResidentFactoredMomentAddress,
    pub device: String,
    pub context_identity: usize,
    pub chronology_population: u32,
    pub pair_population: u32,
    pub coefficient_limb_count: u32,
    pub host_ingress_octets: u64,
    pub resident_octets: u64,
    pub source_current_retained_hot: bool,
    pub ambient_covariance_materialized: bool,
    pub terminal_synchronizations: u64,
}

/// Mount receipt for one plural addressed functional-pair receiver occurrence. The exterior
/// complexes retain their reconstruction fibres; the resident chart owns shared functionals and
/// ordered term incidence only.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAddressedFactoredReceiverFrameReturn {
    pub identity_sha256: String,
    pub occurrence_population: u32,
    pub functional_population: u32,
    pub receiver_population: u32,
    pub term_population: u64,
    pub device: String,
    pub context_identity: usize,
    pub host_ingress_octets: u64,
    pub resident_octets: u64,
    pub ambient_factor_square_materialized: bool,
}

/// Address of the plural transported incidence prior to exact image refactorization.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentTransportAddress {
    pub operation_complex_identity_sha256: String,
    pub transport_identity_sha256: String,
    pub source_section_identity_sha256: String,
    pub device_context_identity: usize,
    pub source_generation: u64,
    pub target_generation: u64,
    pub generator_population: u32,
    pub source_image_population: u32,
    pub transported_row_population: u32,
    pub factor_population: u32,
}

/// One exact generator/source-image occurrence in the resident transported front.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentTransportOccurrence {
    pub generator: u32,
    pub source_image: u32,
    pub transported_row: u32,
}

/// Terminal inspection receipt for the R4Q2B apparatus gate. Production refactorization consumes
/// the resident transport directly and does not request this exterior matrix face.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentTransportReturn {
    pub source_address: ResidentFactoredMomentAddress,
    pub transport_address: ResidentFactoredMomentTransportAddress,
    pub generator_targets: Vec<Vec<u32>>,
    pub occurrences: Vec<ResidentFactoredMomentTransportOccurrence>,
    pub transported_incidence: ExactRatMatrix,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub successor_host_ingress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Address of the finite-chart rank witness. No host-selected rank or pivot enters this address;
/// the witness becomes an exact rank only when the later factorization square closes.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentRankAddress {
    pub operation_complex_identity_sha256: String,
    pub transport_identity_sha256: String,
    pub device_context_identity: usize,
    pub source_generation: u64,
    pub target_generation: u64,
    pub transported_row_population: u32,
    pub factor_population: u32,
    pub chart_population: u32,
    pub minor_bound_bits: u64,
    pub chart_product_bits: u64,
}

/// Terminal R4Q2C-rank observer. It is available only after the exact factorization square has
/// admitted the candidate, so `exact_rank` names the completed lower/upper rank sandwich rather
/// than a probabilistic modular estimate. Production never invokes this exterior face.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentRankReturn {
    pub address: ResidentFactoredMomentRankAddress,
    pub primes: Vec<u32>,
    pub modular_ranks: Vec<u32>,
    pub selected_chart: u32,
    pub exact_rank: u32,
    pub basis_rows: Vec<u32>,
    pub basis_factors: Vec<u32>,
    pub minor_bound: BigUint,
    pub chart_product: BigUint,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub intermediate_host_egress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub host_selected_rank_or_pivot: bool,
    pub probabilistic_rank: bool,
}

/// Address of the resident signed coordinate reconstruction. It names the determinant, joining
/// numerator, and constitutive numerator as one still-unobserved exact fibre.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentCoordinateAddress {
    pub operation_complex_identity_sha256: String,
    pub transport_identity_sha256: String,
    pub device_context_identity: usize,
    pub source_generation: u64,
    pub target_generation: u64,
    pub transported_row_population: u32,
    pub factor_population: u32,
    pub maximal_rank: u32,
    pub chart_population: u32,
    pub reconstruction_value_population: u32,
    pub absolute_bound_bits: u64,
    pub chart_product_bits: u64,
}

/// Terminal diagnostic face of R4Q2C. Production square verification and image replacement read
/// the same resident signed fibre directly and do not call this observer.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentCoordinateReturn {
    pub address: ResidentFactoredMomentCoordinateAddress,
    pub primes: Vec<u32>,
    pub good_chart_population: u32,
    pub determinant: BigInt,
    pub joining_numerator: ExactRatMatrix,
    pub constitutive_numerator: ExactRatMatrix,
    pub absolute_bound: BigUint,
    pub chart_product: BigUint,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub intermediate_host_egress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub host_crt_reconstruction: bool,
    pub host_selected_coordinate_chart: bool,
}

/// Address of the exact staged target image. The exact image rank remains device-owned until the
/// candidate composes with the resident receiver return.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentDescentAddress {
    pub operation_complex_identity_sha256: String,
    pub transport_identity_sha256: String,
    pub section_lineage_identity_sha256: String,
    pub device_context_identity: usize,
    pub source_generation: u64,
    pub target_generation: u64,
    pub factor_population: u32,
    pub image_rank_capacity: u32,
    pub chart_population: u32,
}

/// Terminal diagnostic of the on-card square closure and staged target. The production receiver
/// passage consumes the candidate directly and therefore does not call this observer.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentDescentReturn {
    pub address: ResidentFactoredMomentDescentAddress,
    pub exact_rank: u32,
    pub basis_rows: Vec<u32>,
    pub basis_factors: Vec<u32>,
    pub joining_map: ExactRatMatrix,
    pub target: FactoredMomentSection,
    pub chart_witnesses: Vec<u8>,
    pub admitted: bool,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub intermediate_host_egress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub host_rational_continuation: bool,
    pub source_replaced_before_device_admission: bool,
}

/// Address of the receiver family conducted through the device-admitted descended image.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentReceiverAddress {
    pub operation_complex_identity_sha256: String,
    pub section_lineage_identity_sha256: String,
    pub receiver_frame_identity_sha256: String,
    pub receiver_occurrence_identity_sha256: String,
    pub device_context_identity: usize,
    pub source_generation: u64,
    pub target_generation: u64,
    pub factor_population: u32,
    pub receiver_population: u32,
}

/// Terminal R4Q2C+D return. The target buffers become the sole resident image only after this
/// observer sees the device admission, square witnesses, and complete receiver family together.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentReceiverReturn {
    pub address: ResidentFactoredMomentReceiverAddress,
    pub source_address: ResidentFactoredMomentAddress,
    pub target_address: ResidentFactoredMomentAddress,
    pub receiver_coordinates: Vec<Rat>,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub apparatus_shape_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub atomic_image_replacement: bool,
    pub source_released_only_after_device_admission: bool,
    /// The hot successor is the exact compact image through which the declared receiver family
    /// factors.  Ordered source histories remain reconstruction testimony and do not become the
    /// recurrent state population.
    pub receiver_history_quotient_rested: bool,
    pub rooted_history_retained_hot: bool,
    pub ambient_factor_square_materialized: bool,
    pub host_rational_continuation: bool,
}

/// The device return of one dynamic factored-current passage.  Only exactly equal integral rows
/// condense; proportional rows retain their distinct scale and quadratic weight.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAddressedCurrentPassageReturn {
    pub passage: AddressedCurrentPassage,
    pub source_address: ResidentCurrentAddress,
    pub target_address: ResidentCurrentAddress,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub source_current_mounted_this_pass: bool,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Terminal return of the exact selected generated-port continuation.  The source current stays
/// live until every native receiver has completed; only then does this target family replace it
/// as the one resident current occurrence.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentGeneratedPortCurrentPassageReturn {
    pub passage: AddressedGeneratedPortJunctionPassage,
    /// Exact nonzero local-current rows enacted by the resident card before the target-site
    /// junction.  `passage.occurrences` retains the complete population including radicals;
    /// these rows retain the productive face/slot-to-factor fibre without replaying generator
    /// transport or restriction on the host.
    #[serde(skip_serializing)]
    pub local_currents: Vec<ResidentGeneratedPortLocalCurrent>,
    pub source_address: ResidentCurrentAddress,
    pub target_address: ResidentCurrentAddress,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    /// Resident joining addresses returned before the target is observed. These are apparatus
    /// coordinates only; no current coefficient, receiver value or source surface is present.
    pub intermediate_joining_address_egress_octets: u64,
    /// The scalar allocation extent returned between resident words.
    pub intermediate_apparatus_shape_egress_octets: u64,
    /// Native current/receiver content crossing before the terminal return. Production requires
    /// literal zero even when joining and allocation addresses cross.
    pub intermediate_semantic_egress_octets: u64,
    /// Exact coefficient/current testimony returned only after the resident successor exists.
    /// It closes this local circulation and may found a later occurrence; it is not hidden as
    /// joining traffic and it never computes the successor on the host.
    pub terminal_semantic_egress_octets: u64,
    /// True only in an explicitly requested one-time conformance pass. Production never executes
    /// the apparatus-neutral reference as a fallback or a second successor owner.
    pub reference_ecology_compared: bool,
    pub source_current_mounted_this_pass: bool,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// One device-enacted local current before target-site aggregation.  The indices are boundary
/// maps into the encompassing `AddressedGeneratedPortJunctionPassage`; they are not semantic or
/// apparatus scheduling labels.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentGeneratedPortLocalCurrent {
    pub source_section: u32,
    pub selected_slot: u32,
    pub target_section: u32,
    pub factor_current: Vec<(u32, BigUint)>,
}

/// One exterior boundary restriction.  `port` is an apparatus-local address shared by every
/// descended generator face at that exterior mouth.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentQuadraticMomentRestriction {
    pub port: u32,
    pub factor_current: Vec<(u32, BigUint)>,
}

/// The exact total restriction incidence mounted beside the resident membrane constitution.
/// `u32::MAX` denotes an absent state/port pair; every other entry addresses one transition whose
/// sparse factor section occupies the corresponding offset interval.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentBoundaryRestrictionAtlas {
    pub state_count: u32,
    pub universal_port_count: u32,
    pub state_port_transition: Vec<u32>,
    /// `transition_targets[t]` is the exact successor standing of transition `t`.
    pub transition_targets: Vec<u32>,
    pub transition_factor_offsets: Vec<u64>,
    pub transition_factors: Vec<u32>,
    pub transition_currents: Vec<BigUint>,
}

/// One later boundary aperture into the already-resident total restriction atlas.  Ports are in
/// local output order and carry their universal rested addresses as current lineage.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentBoundaryRestrictionFront {
    pub boundary_states: Vec<u32>,
    pub universal_ports: Vec<u32>,
}

/// Production crosses a boundary aperture into the resident atlas.  The direct sparse family is
/// retained only as an exact reconstruction/equality witness.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub enum ResidentQuadraticMomentRestrictionSource {
    ResidentBoundary(ResidentBoundaryRestrictionFront),
    DirectWitness(Vec<ResidentQuadraticMomentRestriction>),
}

/// The complete sparse axes required to form and contract the present quadratic receiver on the
/// resident card.  `generator_targets[g * factors + source]` is the descended target of `source`.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentQuadraticMomentFront {
    pub contexts: Vec<AddressedCurrentSection>,
    /// Absent only on the first production contact or a direct witness. A later resident contact
    /// must name the exact current occurrence whose buffers it continues.
    pub resident_source: Option<ResidentCurrentAddress>,
    /// Present after source-family foundation. It is mutually exclusive with hot `contexts` and
    /// names the exact factored image whose receiver conducts this front.
    pub resident_image: Option<ResidentFactoredMomentAddress>,
    pub restrictions: ResidentQuadraticMomentRestrictionSource,
    pub generator_targets: Vec<u32>,
    pub generator_count: u32,
    /// Complete source-neutral current of a distinct returned occurrence. `None` is the identity
    /// presentation at initial ingress.  This is input-conditioned current, not an exterior port,
    /// token, or selector over the fixed internal generator action family.
    pub presented_current: Option<Vec<(u32, BigUint)>>,
}

/// Exact identity and population receipt for the resident factored receiver-history operation
/// complex.  The hot term is enacted as a weighted pair of linear readings; source contexts,
/// restriction incidence and generator action remain the complete reconstruction lineage.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredReceiverHistoryReceipt {
    pub schema: String,
    pub identity_sha256: String,
    pub receiver_face_identity_sha256: String,
    pub restriction_atlas_identity_sha256: String,
    pub generator_action_identity_sha256: String,
    pub native_factor_population: u32,
    pub constitutive_family_population: u32,
    pub receiver_population: u32,
    pub receiver_class_population: u32,
    pub generator_population: u32,
    pub boundary_state_population: u32,
    pub boundary_transition_population: u32,
}

/// Exact receipt for the query-independent receiver/history compression mounted with the rested
/// Athena morphology. Counts are shadows of the retained q/U/fibre population; the compression
/// identity commits the complete structural owner and is never used as equality.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentReceiverHistoryCompressionReceipt {
    pub schema: String,
    pub compression_identity_sha256: String,
    pub operation_complex_identity_sha256: String,
    pub device: String,
    pub context_identity: usize,
    pub source_population: usize,
    pub native_population: usize,
    pub quotient_assignment_population: usize,
    pub receiver_factor_population: usize,
    pub generator_population: usize,
    pub source_transport_population: usize,
    pub native_transport_population: usize,
    pub reconstruction_fibre_population: usize,
    pub reconstruction_source_population: usize,
    pub first_separator_population: usize,
    pub separator_word_population: usize,
    pub device_generator_squares_commute: bool,
    pub device_reconstruction_fibres_commute: bool,
    pub ordered_words_exact_by_generator_induction: bool,
    pub mounted_before_exterior_current: bool,
    pub resident_octets: u64,
    pub mount_host_ingress_octets: u64,
    pub launches: u64,
    pub synchronizations: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Exact device return of one primitive integral observable frame, its present receiver factors,
/// and one descended generator action.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentObservableIntegralFormReturn {
    pub coordinates: Vec<BigInt>,
    pub present_receivers: Vec<BigInt>,
    pub transported_coordinates: Vec<BigInt>,
    pub generator: u32,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub synchronizations: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentBoundaryChainSupportReturn {
    pub port: u32,
    /// The reflected ingress current paired with itself in every oriented constitutive family.
    /// This remains distinct from the action difference below; the phase receiver consumes both
    /// exact sections rather than a prematurely summed complex scalar.
    pub reflected_family_overlaps: Vec<Rat>,
    /// The finite integration-by-reflection pairing of `J` with `U_i J - J` in every family.
    pub family_overlaps: Vec<Rat>,
    /// One exact overlap coordinate for every mounted receiver face, in mounted receiver order.
    pub receiver_overlaps: Vec<Rat>,
    /// The corresponding nonnegative action norms, in the same mounted receiver order.
    pub receiver_action_norms: Vec<BigUint>,
    pub returned_response: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentBoundaryChainPortReturn {
    pub port: u32,
    pub returned_response: ExactComplexWaveCurrent,
    pub lies_in_joint_port_kernel: bool,
    pub lies_in_receiver_phase_front: bool,
}

/// One exact per-port contraction returned by the resident quadratic moment gate.  `moment` is
/// the lawful quotient for this declared receiver family; the source axes remain its exterior
/// reconstruction fibre and are not identified by this return.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentQuadraticMomentPortReturn {
    pub port: u32,
    pub moment: Vec<BigUint>,
    pub reflected_family_overlaps: Vec<BigInt>,
    pub family_overlaps: Vec<BigInt>,
    pub receiver_overlaps: Vec<BigInt>,
    pub receiver_action_norms: Vec<BigUint>,
}

/// Exact one-dimensional exterior receiver over the complete native phase front.  The signed
/// coordinates are `Re(conj(J_in) R_p)` in one common oriented current-squared chart.  This is a
/// situated receiver quotient, not a physical-power claim and not a replacement for the retained
/// per-family/per-receiver phase complex.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentSituatedReceiverPairingReturn {
    /// The declared dual chart which returned these coordinates.  Native recurrence uses the
    /// complete ingress quadratic moment; the older membrane path retains its exact exterior
    /// complex-current pairing as a distinct receiver face.
    pub receiver_chart: String,
    pub coordinate_denominator: BigInt,
    pub coordinates: Vec<BigInt>,
    /// Exact self-pairing of the transported native current in every situated port chart.
    pub current_self_pairings: Vec<BigUint>,
    /// Exact self-pairing of the ingress receiver in every situated port chart.
    pub ingress_self_pairings: Vec<BigUint>,
    /// Exact product of the two self-pairings used to compare the corresponding squared
    /// compatibility coordinate. Empty only for the older exterior-complex-current chart.
    pub squared_norm_products: Vec<BigUint>,
    /// Complete oriented complex pairing between the target current and the source-neutral
    /// causal-adjoint current.  The real coordinate is the fixed receiver chart used by the
    /// phase-sensitive front; the imaginary coordinate is retained so that this chart does not
    /// identify distinct pre-locking Complex-Parametron phases.
    pub relational_oriented_real_coordinates: Vec<BigInt>,
    pub relational_oriented_imaginary_coordinates: Vec<BigInt>,
    /// Phase-insensitive `|<X',R>|^2` shadow retained as a separate projective receiver face.
    /// It may never replace the oriented pair above.
    pub relational_modulus_squared_coordinates: Vec<BigUint>,
    /// Exact target-current and relational-current self pairings for the relational receiver.
    /// Their product is the projective denominator paired with
    /// `relational_modulus_squared_coordinates`.
    pub relational_target_self_pairings: Vec<BigUint>,
    pub relational_current_self_pairings: Vec<BigUint>,
    pub relational_squared_norm_products: Vec<BigUint>,
    /// Exact native addressed face chart.  Empty only for the older port-only receiver.
    pub face_source_states: Vec<u32>,
    pub face_ports: Vec<u32>,
    pub face_generators: Vec<u32>,
    pub front_faces: Vec<u32>,
    pub front_ports: Vec<u32>,
    pub front_is_unique: bool,
    /// Complete addressed faces admitted by the native phase receiver before any situated
    /// projective measurement.
    pub native_phase_front_faces: Vec<u32>,
    /// Faces whose rigorous integer score intervals were not strictly dominated and therefore
    /// paid the arbitrary-width exact contraction. Empty when this acceleration was not used.
    pub projective_candidate_faces: Vec<u32>,
    pub projective_interval_limb_count: usize,
    pub projective_interval_obstruction_reopened_front: bool,
    pub complete_native_phase_front_retained: bool,
    pub ingress_moment_reconstruction_fibre_retained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentQuadraticMomentReturn {
    pub factored_receiver_history: ResidentFactoredReceiverHistoryReceipt,
    pub resident_current: Option<ResidentCurrentAddress>,
    pub conditioned_current: Option<ResidentGeneratedPortCurrentPassageReturn>,
    /// The occurrence-local relational current after it has crossed the same selected
    /// generator/restriction world-line as `conditioned_current`.  This is causal lineage for
    /// continuation equality, not an apparatus address or an exterior semantic label.
    pub relational_current: Option<ResidentSparseRelationalCurrentReceipt>,
    /// Common positive chart denominator for every overlap coordinate in `ports`.  The port
    /// values are its signed/nonnegative numerators; keeping the chart explicit prevents a
    /// rational image receiver from masquerading as an integral source-family reading.
    pub receiver_coordinate_denominator: BigInt,
    pub ports: Vec<ResidentQuadraticMomentPortReturn>,
    /// Complete addressed receiver faces used by native continuation.
    pub port_returns: Vec<ResidentBoundaryChainPortReturn>,
    /// Exact physical boundary-port quotient of `port_returns`; generator and source-state faces
    /// remain in the complete addressed family above.
    pub boundary_port_returns: Vec<ResidentBoundaryChainPortReturn>,
    pub entering_current: ExactComplexWaveCurrent,
    pub total_returned_current: ExactComplexWaveCurrent,
    pub stored_difference: ExactComplexWaveCurrent,
    pub local_balance_closes: bool,
    pub phase_locked_port_population: usize,
    pub phase_front_is_unique: bool,
    pub situated_receiver_pairing: Option<ResidentSituatedReceiverPairingReturn>,
    /// Complete sparse support of the already-founded successor before any receiver quotient.
    /// Indices address `situated_receiver_pairing.face_*`; the complement in
    /// `complete_successor_face_population` is the exact zero-support fibre.  These coordinates
    /// are current support, not a phase score or an exterior realization choice.
    pub complete_successor_faces: Vec<u32>,
    pub complete_successor_face_population: usize,
    /// Factors in the exact local chart through which this receiver factors.
    pub active_factor_population: usize,
    /// Factors in the complete rested native carrier.
    pub native_factor_population: usize,
    /// Whether the ambient factor-square matrix was explicitly requested and returned.
    pub moment_field_materialized: bool,
    /// The sparse rank-one presentation was retained as the reconstruction face.
    pub moment_factorization_retained: bool,
    pub context_population: usize,
    pub restriction_population: usize,
    pub generator_population: usize,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// One terminal return in which an admitted image receiver has already crossed the existing
/// radiation, phase, and balance owners before its source is released.  `image.target_address`
/// is the sole hot continuation; `boundary` is the exterior receiver testimony of that same deed.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentFactoredMomentBoundaryReturn {
    pub image: ResidentFactoredMomentReceiverReturn,
    pub boundary: ResidentQuadraticMomentReturn,
}

/// One resident `interior -> boundary ports -> balance` word.  The complete support population
/// crosses three device-dependent launches and one terminal synchronization.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentJointBoundaryChainReturn {
    pub support_returns: Vec<ResidentBoundaryChainSupportReturn>,
    pub port_returns: Vec<ResidentBoundaryChainPortReturn>,
    pub entering_current: ExactComplexWaveCurrent,
    pub total_returned_current: ExactComplexWaveCurrent,
    pub stored_difference: ExactComplexWaveCurrent,
    pub local_balance_closes: bool,
    pub phase_locked_port_population: usize,
    pub phase_front_is_unique: bool,
    pub device: String,
    pub context_identity: usize,
    pub launches: u64,
    pub device_dependency_edges: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}
