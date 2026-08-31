use super::membrane_types::{
    ResidentFactoredMomentAddress, ResidentFactoredReceiverHistoryReceipt,
    ResidentGeneratedPortCurrentPassageReturn, ResidentReceiverHistoryCompressionReceipt,
    ResidentSparseRelationalCurrentReceipt,
};
use super::{Buffer, CuDevicePtr};
use crate::factored_moment::SparseQuadraticMomentAction;
use crate::receiver_history_compression::AddressedPrimitiveReceiverFrame;
use crate::receiver_history_compression::ReceiverHistoryCompression;

use num_bigint::{BigInt, BigUint};

pub(super) struct SparsePairActionIngress {
    pub(super) pair_factors: Vec<u32>,
    pub(super) pair_row_offsets: Vec<u64>,
    pub(super) target_offsets: Vec<u64>,
    pub(super) source_pairs: Vec<u32>,
    pub(super) multiplicities: Vec<u8>,
    pub(super) generator_target_offsets: Vec<u64>,
    pub(super) generator_source_pairs: Vec<u32>,
    pub(super) generator_multiplicities: Vec<u8>,
    pub(super) maximal_incoming_multiplicity: BigUint,
}

/// One immutable sparse `B` chart resident beside the singular membrane word.
pub(super) struct ResidentSparseRelationalCurrentAtlasMount {
    pub(super) identity_sha256: String,
    pub(super) causal_adjoint_identity_sha256: String,
    pub(super) constitutive_family_identity_sha256: String,
    pub(super) row_population: u32,
    pub(super) term_population: u64,
    pub(super) row_offsets: Buffer,
    pub(super) term_rows: Buffer,
    pub(super) term_factors: Buffer,
    pub(super) term_ingress_population: Buffer,
    pub(super) term_emanation_population: Buffer,
    pub(super) term_return_population: Buffer,
    pub(super) _row_reconstruction_addresses: Buffer,
    pub(super) maximal_row_phase_mass: u64,
    pub(super) maximal_factor_phase_mass: u64,
    pub(super) resident_octets: u64,
}

/// The occurrence-local signed relational current. It is destroyed at the next exterior
/// occurrence while its invariant atlas remains mounted.
pub(super) struct ResidentSparseRelationalCurrentState {
    pub(super) receipt: ResidentSparseRelationalCurrentReceipt,
    pub(super) state_present: Buffer,
    pub(super) states: Buffer,
    pub(super) state_count: usize,
    /// The bounded bootstrap face exists only before the first arbitrary-limb continuation.
    /// It is an apparatus witness, never the productive recurrence carrier.
    pub(super) bounded_i64_face_valid: bool,
    /// Keeps the bounded bootstrap buffers alive until every queued conversion has consumed them.
    #[allow(dead_code)]
    pub(super) factor_real: Buffer,
    #[allow(dead_code)]
    pub(super) factor_imaginary: Buffer,
    pub(super) factor_real_sign: Buffer,
    pub(super) factor_real_limbs: Buffer,
    pub(super) factor_imaginary_sign: Buffer,
    pub(super) factor_imaginary_limbs: Buffer,
    pub(super) factor_limb_count: usize,
    pub(super) returned_factor_bound: BigUint,
}

/// Occurrence-local exact receiver workspace for the compact rank-one carrier.  Every buffer is
/// a device section; only the terminal receiver coordinates cross after the complete word.
pub(super) struct ResidentFactorizedRelationalWorkspace {
    pub(super) transported_current: Buffer,
    pub(super) transported_state_present: Buffer,
    pub(super) transported_states: Buffer,
    pub(super) transported_relational_real_sign: Buffer,
    pub(super) transported_relational_real_limbs: Buffer,
    pub(super) transported_relational_imaginary_sign: Buffer,
    pub(super) transported_relational_imaginary_limbs: Buffer,
    pub(super) partial_overlap: Buffer,
    pub(super) partial_target_norm: Buffer,
    pub(super) dot_real_signs: Buffer,
    pub(super) dot_real: Buffer,
    pub(super) dot_imaginary_signs: Buffer,
    pub(super) dot_imaginary: Buffer,
    pub(super) partial_first_scratch: Buffer,
    pub(super) partial_second_scratch: Buffer,
    pub(super) partial_third_scratch: Buffer,
    pub(super) relational_norm: Buffer,
    pub(super) norm_first_scratch: Buffer,
    pub(super) norm_second_scratch: Buffer,
    pub(super) reduce_first_scratch: Buffer,
    pub(super) reduce_second_scratch: Buffer,
    pub(super) reduce_third_scratch: Buffer,
    pub(super) obstruction: Buffer,
    pub(super) limb_count: usize,
    pub(super) transported_limb_count: usize,
    pub(super) transported_relational_limb_count: usize,
    pub(super) resident_working_octets: u64,
}

/// Occurrence-local transport of the standing sparse relational current through one admitted
/// generator family.  This is the causal-adjoint companion of the linear factor transport; it is
/// founded before the target junction and consumed by that same junction.  No receiver workspace
/// or source/path response rectangle is part of this owner.
pub(super) struct ResidentSparseRelationalGeneratorTransport {
    pub(super) real_sign: Buffer,
    pub(super) real_limbs: Buffer,
    pub(super) imaginary_sign: Buffer,
    pub(super) imaginary_limbs: Buffer,
    pub(super) obstruction: Buffer,
    pub(super) state_present_pointer: CuDevicePtr,
    pub(super) states_pointer: CuDevicePtr,
    pub(super) state_count: usize,
    pub(super) limb_count: usize,
    pub(super) receipt: ResidentSparseRelationalCurrentReceipt,
    pub(super) returned_factor_bound: BigUint,
}

/// The sparse inverse-incidence fibre retained between the committed target junction and its
/// later receiver.  Candidate rows are reconstruction testimony only: the continuing current is
/// already the target-indexed `ResidentFactoredCurrentState` named by `returned.target_address`.
pub(super) struct ResidentCompletedTargetObservationAperture {
    pub(super) returned: ResidentGeneratedPortCurrentPassageReturn,
    pub(super) selected_faces: Buffer,
    pub(super) candidate_selected_slots: Buffer,
    pub(super) candidate_to_target: Buffer,
    pub(super) selected_slot_count: usize,
    pub(super) candidate_count: usize,
    pub(super) local_face_population: usize,
}

/// Occurrence-local realization of the sparse pushforward from committed target sites to one
/// receiver face per local `(port,generator)` incidence.  No target-by-face rectangle is stored.
pub(super) struct ResidentCompletedTargetObserverWorkspace {
    /// Raw pointers into these buffers remain arguments of queued observer kernels; ownership here
    /// is their CUDA lifetime boundary even when Rust never reads the buffers again.
    #[allow(dead_code)]
    pub(super) face_current: Buffer,
    #[allow(dead_code)]
    pub(super) face_relational_real_sign: Buffer,
    #[allow(dead_code)]
    pub(super) face_relational_real_limbs: Buffer,
    #[allow(dead_code)]
    pub(super) face_relational_imaginary_sign: Buffer,
    #[allow(dead_code)]
    pub(super) face_relational_imaginary_limbs: Buffer,
    pub(super) relational_dot_real_sign: Buffer,
    pub(super) relational_dot_real_limbs: Buffer,
    pub(super) relational_dot_imaginary_sign: Buffer,
    pub(super) relational_dot_imaginary_limbs: Buffer,
    pub(super) target_norm_limbs: Buffer,
    pub(super) relational_norm_limbs: Buffer,
    pub(super) norm_product_limbs: Buffer,
    pub(super) first_scratch: Buffer,
    #[allow(dead_code)]
    pub(super) second_scratch: Buffer,
    #[allow(dead_code)]
    pub(super) third_scratch: Buffer,
    pub(super) limb_count: usize,
    pub(super) obstruction: Buffer,
    pub(super) resident_working_octets: u64,
}

/// One source-neutral generator/receiver action mounted beside the resident membrane constitution.
/// These buffers are invariant across every later boundary front; only changed moment and boundary
/// coordinates may cross as successor ingress.
pub(super) struct ResidentQuadraticActionMount {
    pub(super) identity_sha256: String,
    pub(super) generator_targets: Vec<u32>,
    pub(super) generator_count: u32,
    pub(super) receiver_class_count: u32,
    pub(super) native_generator_targets: Buffer,
    pub(super) native_factor_receiver_classes: Buffer,
    pub(super) receiver_class_bases: Buffer,
    pub(super) source_class_factor_offsets: Buffer,
    pub(super) source_class_factors: Buffer,
    pub(super) generator_class_factor_offsets: Buffer,
    pub(super) generator_class_factors: Buffer,
}

/// The total rested native boundary restriction atlas.  Its source incidence crosses once at
/// mount; a later current supplies only the boundary states and exterior ports which meet it.
pub(super) struct ResidentBoundaryRestrictionAtlasMount {
    pub(super) identity_sha256: String,
    pub(super) state_count: u32,
    pub(super) universal_port_count: u32,
    pub(super) transition_count: u32,
    pub(super) restriction_limb_count: u32,
    pub(super) maximal_current: BigUint,
    pub(super) state_port_transition: Buffer,
    pub(super) transition_targets: Buffer,
    pub(super) transition_factor_offsets: Buffer,
    pub(super) transition_factors: Buffer,
    pub(super) transition_current_limbs: Buffer,
}

/// The one production operation complex obtained by binding the already-resident restriction,
/// receiver, constitutive and generator owners.  It owns no ambient matrix and allocates no
/// second current population: its identities make those existing axes one executable carrier.
pub(super) struct ResidentFactoredReceiverHistoryMount {
    pub(super) receipt: ResidentFactoredReceiverHistoryReceipt,
    pub(super) compression: Option<ResidentReceiverHistoryCompressionMount>,
    pub(super) current: Option<ResidentFactoredCurrentState>,
    pub(super) image: Option<ResidentFactoredMomentState>,
    pub(super) sparse_pair: Option<ResidentSparseQuadraticMomentState>,
    pub(super) transported_image: Option<ResidentTransportedFactoredMomentIncidence>,
}

/// The one exact receiver/history quotient mounted before any exterior occurrence. The Rust owner
/// retains the complete structural law; these buffers are its single-card realization and never
/// become a second equality authority.
pub(super) struct ResidentReceiverHistoryCompressionMount {
    pub(super) exact: ReceiverHistoryCompression,
    pub(super) receipt: ResidentReceiverHistoryCompressionReceipt,
    pub(super) _source_population: Buffer,
    pub(super) _native_population: Buffer,
    pub(super) _quotient_by_source: Buffer,
    pub(super) _receiver_factor_native: Buffer,
    pub(super) _receiver_factor_receiver: Buffer,
    pub(super) _receiver_factor_observation: Buffer,
    pub(super) _generator_source_offsets: Buffer,
    pub(super) _source_edge_from: Buffer,
    pub(super) _source_edge_to: Buffer,
    pub(super) _native_generator_targets: Buffer,
    pub(super) _fibre_native_by_source: Buffer,
    pub(super) _separator_left: Buffer,
    pub(super) _separator_right: Buffer,
    pub(super) _separator_word_offsets: Buffer,
    pub(super) _separator_word: Buffer,
    pub(super) _separator_witness_present: Buffer,
    pub(super) _separator_witness_receiver: Buffer,
    pub(super) _separator_witness_left: Buffer,
    pub(super) _separator_witness_right: Buffer,
    pub(super) _separator_terminus: Buffer,
}

/// The fixed native pair-current carrier and its resident inverse generator incidence.  The
/// apparatus-neutral action is retained only as cold shape/reconstruction testimony; recurrence
/// reads the CSR buffers and the current coefficients exclusively on the card.
pub(super) struct ResidentSparseQuadraticMomentState {
    pub(super) generation: u64,
    pub(super) section_identity_sha256: String,
    /// Active direct-sum blocks of the current.  `state_ids_host[block]` is the exact native
    /// boundary state carried by coefficient row `block`; repeated state ids remain distinct
    /// addressed branch occurrences until a later declared receiver condenses them.
    pub(super) state_population: u32,
    pub(super) coefficient_state_capacity: u32,
    pub(super) state_ids_host: Vec<u32>,
    pub(super) state_ids: Buffer,
    pub(super) factor_population: u32,
    pub(super) pair_population: u32,
    pub(super) coefficient_limb_count: u32,
    pub(super) maximal_coefficient: BigUint,
    /// State-major `[state block][upper pair]` exact current.
    pub(super) coefficients: Buffer,
    /// The immutable ingress moment acting as the situated dual receiver throughout this one
    /// circulation.  It shares the fixed pair carrier but is not a rollback copy of the changing
    /// current; its distinct role is witnessed by the returned contraction and it leaves with
    /// the occurrence.
    pub(super) situated_receiver_coefficients: Buffer,
    pub(super) situated_receiver_limb_count: u32,
    pub(super) maximal_situated_receiver_coefficient: BigUint,
    /// Packed `(left, right)` factor addresses for every fixed symmetric pair.  This is native
    /// carrier incidence required by the returned membrane action, not an exterior label.
    pub(super) pair_factors: Buffer,
    /// CSR row boundary for the lexicographically ordered upper-pair carrier.  It is the exact
    /// resident address map `(left,right) -> pair occurrence`, including absent sparse faces.
    pub(super) pair_row_offsets: Buffer,
    pub(super) target_offsets: Buffer,
    pub(super) source_pairs: Buffer,
    pub(super) multiplicities: Buffer,
    /// Generator-major inverse incidence.  The aggregate CSR above is retained only for the
    /// older declared direct-sum receiver; native recurrence keeps every `T_g C T_g^T` branch
    /// addressed until a returned `(port,generator)` face performs the lawful condensation.
    pub(super) generator_target_offsets: Buffer,
    pub(super) generator_source_pairs: Buffer,
    pub(super) generator_multiplicities: Buffer,
    pub(super) maximal_incoming_multiplicity: BigUint,
    pub(super) action: SparseQuadraticMomentAction,
    pub(super) resident_octets: u64,
}

/// Apparatus chart of one fixed pair action. Every vector is derived from the exact action; none
/// of its extents is a caller-supplied rank or a semantic population.
pub(super) struct ResidentExactRationalMatrix {
    pub(super) rows: u32,
    pub(super) columns: u32,
    pub(super) numerator_limb_count: u32,
    pub(super) denominator_limb_count: u32,
    pub(super) common_denominator: BigInt,
    pub(super) maximal_numerator: BigInt,
    pub(super) numerator_signs: Buffer,
    pub(super) numerator_limbs: Buffer,
    pub(super) denominator_limbs: Buffer,
    pub(super) resident_octets: u64,
}

/// One exact integral matrix carried without manufacturing a denominator axis.  This carrier is
/// used by the rooted productive incidence spine; the compact rational chart below remains the
/// independently addressed reconstruction/refactor presentation of the same moment.
pub(super) struct ResidentIntegralMatrix {
    pub(super) rows: u32,
    pub(super) columns: u32,
    pub(super) numerator_limb_count: u32,
    pub(super) maximal_numerator: BigInt,
    pub(super) signs: Buffer,
    pub(super) limbs: Buffer,
    pub(super) resident_octets: u64,
}

/// Rooted productive presentation `E^T (direct_sum H_root) E`.  Its history and root-coordinate
/// addresses are not identified with the compact target-image coordinates even when both return
/// the same complete moment.
pub(super) struct ResidentFactoredConstitutiveSpine {
    pub(super) root_rank: u32,
    pub(super) history_population: u32,
    pub(super) root_constitutive: ResidentExactRationalMatrix,
    pub(super) effective_incidence: ResidentIntegralMatrix,
    pub(super) history_weight_limb_count: u32,
    pub(super) maximal_history_weight: BigUint,
    pub(super) history_weights: Buffer,
    pub(super) reconstruction_fibre: Vec<ResidentFactoredHistoryQuotientPassage>,
}

/// The next addressed incidence of the rooted spine while the compact target chart is still an
/// admission candidate.
pub(super) struct ResidentTransportedConstitutiveSpine {
    pub(super) root_rank: u32,
    pub(super) history_population: u32,
    pub(super) effective_incidence: ResidentIntegralMatrix,
    pub(super) history_weight_limb_count: u32,
    pub(super) maximal_history_weight: BigUint,
    pub(super) history_weights: Buffer,
    pub(super) quotient_passage: Option<ResidentFactoredHistoryQuotientPassage>,
}

/// Weight and reconstruction testimony accompanying a rooted incidence carried in the primary
/// transport buffers.  Standard compact/refactor passages need a second incidence and therefore
/// use [`ResidentTransportedConstitutiveSpine`]; direct rooted continuation already owns its
/// productive incidence in `ResidentTransportedFactoredMomentIncidence::{signs,limbs}` and keeps
/// only this non-duplicated continuation fibre beside it.
pub(super) struct ResidentTransportedFactoredHistory {
    pub(super) root_rank: u32,
    pub(super) history_population: u32,
    pub(super) history_weight_limb_count: u32,
    pub(super) maximal_history_weight: BigUint,
    pub(super) history_weights: Buffer,
    pub(super) quotient_passage: Option<ResidentFactoredHistoryQuotientPassage>,
}

/// Complete candidate-history to condensed-history boundary map for one plural passage.  It is
/// reconstruction testimony and never selects a productive receiver.
pub(super) struct ResidentFactoredHistoryQuotientPassage {
    pub(super) source_history_population: u32,
    pub(super) generator_population: u32,
    pub(super) presented_history_population: u32,
    pub(super) target_history_population: u32,
    /// Retains the complete candidate fibre on the card beside the productive quotient.
    #[allow(dead_code)]
    pub(super) candidate_to_target: Buffer,
}

/// The native quadratic image occurrence.  The addressed source-current family is deliberately
/// absent: it remains in `FactoredMomentFoundation::reconstruction_fibre`, while later hot
/// conduct owns only `B` and `H` from `B^T H B`.
pub(super) struct ResidentFactoredMomentState {
    pub(super) generation: u64,
    pub(super) section_identity_sha256: String,
    pub(super) factor_population: u32,
    /// Population of the current productive incidence presentation.  It equals `image_rank` at a
    /// compact checkpoint and the rooted effective-incidence row population between checkpoints.
    pub(super) productive_population: u32,
    /// Generation represented by the retained compact reconstruction checkpoint below.
    pub(super) compact_generation: u64,
    pub(super) image_rank: u32,
    pub(super) basis_factors: Vec<u32>,
    pub(super) incidence: ResidentExactRationalMatrix,
    pub(super) constitutive: ResidentExactRationalMatrix,
    pub(super) constitutive_spine: Option<ResidentFactoredConstitutiveSpine>,
}

/// One not-yet-refactored plural image front.  Row order is
/// `(generator, source_image)` and is therefore itself the complete occurrence population.
pub(super) struct ResidentTransportedFactoredMomentIncidence {
    pub(super) transport_identity_sha256: String,
    pub(super) source_address: ResidentFactoredMomentAddress,
    pub(super) target_generation: u64,
    pub(super) generator_population: u32,
    pub(super) transported_row_population: u32,
    pub(super) factor_population: u32,
    pub(super) numerator_limb_count: u32,
    pub(super) maximal_numerator: BigInt,
    pub(super) signs: Buffer,
    pub(super) limbs: Buffer,
    pub(super) overflow: Buffer,
    pub(super) productive_admitted: Buffer,
    pub(super) productive_receiver: Option<ResidentFactoredMomentReceiverState>,
    pub(super) constitutive_spine: Option<ResidentTransportedConstitutiveSpine>,
    pub(super) productive_history: Option<ResidentTransportedFactoredHistory>,
    pub(super) rank_atlas: Option<ResidentFactoredMomentRankAtlas>,
    /// Returned membrane action queued after the current boundary receivers.  The unconditioned
    /// `limbs` stay alive until the terminal synchronization because those earlier launches read
    /// them; only this conditioned section may become the next hot current.
    pub(super) sparse_conditioned: Option<ResidentSparseQuadraticConditionedCurrent>,
    /// Occurrence-local native receiver section founded directly on the fixed pair carrier.
    /// This replaces an equivalent host expansion into sparse functional-pair terms.
    pub(super) sparse_native_boundary: Option<ResidentSparseQuadraticNativeBoundary>,
    pub(super) resident_octets: u64,
    /// True only for the fixed symmetric pair-current route.  Its `limbs` are the exact target
    /// pair coefficients and its receiver already has denominator one; no image refactor exists.
    pub(super) sparse_pair_completion: bool,
}

pub(super) struct ResidentSparseQuadraticConditionedCurrent {
    pub(super) state_population: u32,
    pub(super) coefficient_state_capacity: u32,
    pub(super) state_population_device: Buffer,
    pub(super) state_ids_host: Vec<u32>,
    pub(super) state_ids: Buffer,
    pub(super) coefficient_limb_count: u32,
    pub(super) maximal_coefficient: BigUint,
    pub(super) coefficients: Buffer,
    /// Device arguments already queued against these allocations outlive the staging call.
    #[allow(dead_code)]
    pub(super) returned_port_selection: Buffer,
    #[allow(dead_code)]
    pub(super) work_buffers: Vec<Buffer>,
    pub(super) relational_continuation: Option<ResidentSparseRelationalConditionedCurrent>,
    pub(super) launches: u64,
    pub(super) synchronizations: u64,
    pub(super) apparatus_shape_host_egress_octets: u64,
}

/// The signed Complex-Parametron return carried through the same selected addressed-face direct
/// sum as its companion quadratic moment.  It remains staged beside the source current until the
/// terminal receiver admits the common target fibre, then becomes the sole continuing relation.
pub(super) struct ResidentSparseRelationalConditionedCurrent {
    pub(super) state_present: Buffer,
    pub(super) states: Buffer,
    pub(super) state_ids_host: Vec<u32>,
    pub(super) state_count: usize,
    pub(super) factor_real_sign: Buffer,
    pub(super) factor_real_limbs: Buffer,
    pub(super) factor_imaginary_sign: Buffer,
    pub(super) factor_imaginary_limbs: Buffer,
    pub(super) factor_limb_count: usize,
    pub(super) returned_factor_bound: BigUint,
    #[allow(dead_code)]
    pub(super) work_buffers: Vec<Buffer>,
    pub(super) launches: u64,
    pub(super) resident_octets: u64,
}

pub(super) struct ResidentSparseQuadraticNativeBoundary {
    pub(super) identity_sha256: String,
    /// Exterior physical port population.  It is a receiver shadow and does not enumerate the
    /// native addressed front.
    pub(super) port_population: u32,
    /// Native front population `(port,generator)`.
    pub(super) face_population: u32,
    pub(super) face_ports_host: Vec<u32>,
    pub(super) face_generators_host: Vec<u32>,
    pub(super) face_source_states_host: Vec<u32>,
    pub(super) restriction_limb_count: u32,
    pub(super) maximal_restriction: BigUint,
    pub(super) restrictions: Buffer,
    pub(super) restriction_present: Buffer,
    pub(super) restriction_target_states: Buffer,
    pub(super) support_ports: Buffer,
    pub(super) support_ports_host: Vec<u32>,
    pub(super) support_receiver_classes: Buffer,
    pub(super) support_quadratic_scales: Buffer,
    pub(super) situated_limb_count: u32,
    pub(super) situated_bound: BigUint,
    pub(super) situated_signs: Buffer,
    pub(super) situated_limbs: Buffer,
    pub(super) situated_current_norm_bound: BigUint,
    pub(super) situated_current_norm_limbs: Buffer,
    pub(super) situated_ingress_norm_bound: BigUint,
    pub(super) situated_ingress_norm_limbs: Buffer,
    /// The signed source-neutral relational return is not folded into the positive quadratic
    /// carrier.  It crosses the same addressed state/port/generator boundary as an independent
    /// Complex-Parametron receiver and may therefore separate a projective tie without erasing
    /// relative phase or its reconstruction fibre.
    pub(super) relational_receiver: Option<ResidentSparseRelationalBoundaryReceiver>,
    pub(super) resident_octets: u64,
    pub(super) working_octets: u64,
    #[allow(dead_code)]
    pub(super) work_buffers: Vec<Buffer>,
}

/// One exact boundary receiver of the resident `B^dagger K B` current.  For every addressed
/// `(source-state, port, generator)` face it retains
///
/// `A = Re <deltaX_g deltaX_g^dagger, C_f>`,
/// `B = ||C_f||^2`, and `C = ||deltaX_g deltaX_g^dagger||^2`, where both
/// `deltaX_g = T_g deltaX` and `C_f = D_p T_g C_s T_g^dagger D_p` occupy the same target fibre.
///
/// The projective comparison is only a later receiver over these three sections.  The complete
/// signed complex factor current remains owned by `ResidentSparseRelationalCurrentState`.
pub(super) struct ResidentSparseRelationalBoundaryReceiver {
    pub(super) identity_sha256: String,
    pub(super) limb_count: u32,
    pub(super) compatibility_bound: BigUint,
    pub(super) compatibility_signs: Buffer,
    pub(super) compatibility_limbs: Buffer,
    pub(super) transported_norm_bound: BigUint,
    pub(super) transported_norm_limbs: Buffer,
    pub(super) ingress_norm_bound: BigUint,
    pub(super) ingress_norm_limbs: Buffer,
    pub(super) resident_octets: u64,
    pub(super) working_octets: u64,
    pub(super) launches: u64,
    #[allow(dead_code)]
    pub(super) work_buffers: Vec<Buffer>,
}

/// One finite receiver chart over the resident transported frame.  Its nonzero minor supplies the
/// lower leg of an exact rank sandwich; the later reconstructed factorization square supplies the
/// upper leg.  The witness rank and minor remain on the card until that square admits them.
pub(super) struct ResidentFactoredMomentRankAtlas {
    pub(super) primes_host_testimony: Vec<u32>,
    pub(super) minor_bound: BigUint,
    pub(super) chart_product: BigUint,
    pub(super) primes: Buffer,
    pub(super) work: Buffer,
    pub(super) row_addresses: Buffer,
    pub(super) ranks: Buffer,
    pub(super) pivot_rows: Buffer,
    pub(super) pivot_columns: Buffer,
    pub(super) selected_chart: Buffer,
    pub(super) selected_rank: Buffer,
    pub(super) selected_rows: Buffer,
    pub(super) selected_columns: Buffer,
    pub(super) coordinates: Option<ResidentFactoredMomentCoordinateAtlas>,
    pub(super) resident_octets: u64,
}

/// The exact coordinate and constitutive pullback fibre founded from the selected integral
/// minor. Every reconstruction value remains resident as signed arbitrary-width magnitude until
/// the two commuting-square kernels admit atomic image replacement.
pub(super) struct ResidentFactoredMomentCoordinateAtlas {
    pub(super) primes_host_testimony: Vec<u32>,
    pub(super) absolute_bound: BigUint,
    pub(super) signed_reconstruction_bound: BigUint,
    pub(super) chart_product: BigUint,
    pub(super) value_count: u32,
    pub(super) maximal_rank: u32,
    pub(super) crt_limb_count: u32,
    pub(super) bound_limb_count: u32,
    pub(super) launches: u64,
    pub(super) primes: Buffer,
    pub(super) augmented_work: Buffer,
    pub(super) chart_good: Buffer,
    pub(super) chart_residues: Buffer,
    pub(super) good_count: Buffer,
    pub(super) prefix_product: Buffer,
    pub(super) prefix_inverse: Buffer,
    pub(super) active_chart: Buffer,
    pub(super) total_product: Buffer,
    pub(super) half_product: Buffer,
    pub(super) absolute_bound_limbs: Buffer,
    pub(super) signed_reconstruction_bound_limbs: Buffer,
    pub(super) reconstructed_signs: Buffer,
    pub(super) reconstructed_limbs: Buffer,
    pub(super) candidate: Option<ResidentFactoredMomentCandidate>,
    pub(super) resident_octets: u64,
}

/// One staged exact image delta. The source image remains the sole immutable standing while the
/// card verifies and admits these buffers; the following resident receiver passage consumes the
/// device-owned `admitted` boundary before the host releases the source.
pub(super) struct ResidentFactoredMomentCandidate {
    pub(super) section_lineage_identity_sha256: String,
    pub(super) target_generation: u64,
    pub(super) image_rank_capacity: u32,
    pub(super) incidence_limb_count: u32,
    pub(super) constitutive_limb_count: u32,
    pub(super) denominator_limb_count: u32,
    pub(super) maximal_incidence_numerator: BigInt,
    pub(super) maximal_constitutive_numerator: BigInt,
    pub(super) denominator_bound: BigUint,
    pub(super) incidence_signs: Buffer,
    pub(super) incidence_limbs: Buffer,
    pub(super) incidence_denominator_limbs: Buffer,
    pub(super) constitutive_signs: Buffer,
    pub(super) constitutive_limbs: Buffer,
    pub(super) denominator_limbs: Buffer,
    pub(super) denominator_scratch: Buffer,
    /// Exact finite-chart work fibres. They exist only until the sufficient family has closed
    /// both squares and an admitted receiver current crosses the reconstruction boundary.
    pub(super) square_transported_residues: Option<Buffer>,
    pub(super) square_constitutive_residues: Option<Buffer>,
    pub(super) chart_witnesses: Buffer,
    pub(super) admitted: Buffer,
    pub(super) receiver: Option<ResidentFactoredMomentReceiverState>,
    pub(super) launches: u64,
    pub(super) resident_octets: u64,
}

/// One complete addressed primitive receiver family contracted against the admitted target image.
pub(super) struct ResidentFactoredMomentReceiverState {
    pub(super) identity_sha256: String,
    pub(super) section_lineage_identity_sha256: String,
    pub(super) frame_identity_sha256: String,
    pub(super) receiver_population: u32,
    pub(super) output_limb_count: u32,
    pub(super) output_bound: BigUint,
    /// The constitutive denominator of the exact pullback chart used for contraction.  The
    /// target image may rest in a different, equivalent rational chart.
    pub(super) output_denominator: Option<BigInt>,
    pub(super) output_signs: Buffer,
    pub(super) output_limbs: Buffer,
    pub(super) launches: u64,
    pub(super) apparatus_shape_host_egress_octets: u64,
    pub(super) resident_octets: u64,
}

/// The continuing exact rank-one family owned by the factored receiver-history operation
/// complex.  Its buffers move into each successor and are replaced by the descended target;
/// there is never a sibling host-owned hot current.
pub(super) struct ResidentFactoredCurrentState {
    pub(super) generation: u64,
    pub(super) context_count: u32,
    pub(super) current_limb_count: u32,
    pub(super) weight_limb_count: u32,
    pub(super) maximal_current: BigUint,
    pub(super) maximal_weight: BigUint,
    pub(super) active_factors: Vec<u32>,
    pub(super) boundary_state_present: Buffer,
    pub(super) boundary_states: Buffer,
    pub(super) current_limbs: Buffer,
    pub(super) weight_limbs: Buffer,
}

/// One exact primitive integral receiver frame mounted beside the moment current.  Its sparse
/// forms and descended factors are invariant across successor fronts.
pub(super) struct ResidentObservableIntegralFormMount {
    pub(super) identity_sha256: String,
    pub(super) form_count: u32,
    pub(super) generator_count: u32,
    pub(super) present_receiver_count: u32,
    pub(super) coefficient_limb_count: u32,
    pub(super) scale_limb_count: u32,
    pub(super) maximal_form_entry_population: u64,
    pub(super) maximal_coefficient: BigUint,
    pub(super) maximal_scale: BigUint,
    pub(super) form_entry_offsets: Buffer,
    pub(super) form_entry_rows: Buffer,
    pub(super) form_entry_columns: Buffer,
    pub(super) form_entry_signs: Buffer,
    pub(super) form_entry_limbs: Buffer,
    pub(super) present_factor_sources: Buffer,
    pub(super) present_factor_scale_signs: Buffer,
    pub(super) present_factor_scale_limbs: Buffer,
    pub(super) generator_factor_sources: Buffer,
    pub(super) generator_factor_scale_signs: Buffer,
    pub(super) generator_factor_scale_limbs: Buffer,
}

/// One exterior receiver occurrence retained as shared sparse functionals and addressed term
/// incidence. This is the direct dual face of the image section; it never expands a functional
/// pair into an ambient factor-square matrix.
pub(super) struct ResidentAddressedFactoredReceiverMount {
    pub(super) identity_sha256: String,
    /// Primitive receiver complexes after exact projective restriction factorization.
    pub(super) occurrence_count: u32,
    /// Exterior support occurrences reconstructed from primitive complexes and their scales.
    pub(super) support_count: u32,
    pub(super) family_count: u32,
    pub(super) opaque_receiver_count: u32,
    pub(super) generator_count: u32,
    pub(super) functional_count: u32,
    pub(super) pair_count: u32,
    pub(super) receiver_count: u32,
    pub(super) term_count: u64,
    pub(super) functional_limb_count: u32,
    pub(super) term_limb_count: u32,
    pub(super) maximal_functional_entry_population: u64,
    pub(super) maximal_receiver_term_population: u64,
    pub(super) maximal_functional_coefficient: BigUint,
    pub(super) functional_offsets: Buffer,
    pub(super) functional_factors: Buffer,
    pub(super) functional_signs: Buffer,
    pub(super) functional_limbs: Buffer,
    pub(super) receiver_factor_offsets: Buffer,
    pub(super) pair_left_functionals: Buffer,
    pub(super) pair_right_functionals: Buffer,
    pub(super) receiver_factor_pairs: Buffer,
    pub(super) receiver_factor_signs: Buffer,
    pub(super) receiver_factor_limbs: Buffer,
    /// Exact exterior-port incidence of each receiver occurrence. This is boundary lineage for
    /// radiation aggregation, never an internal semantic class or a continuation selector.
    pub(super) occurrence_ports: Buffer,
    pub(super) occurrence_ports_host: Vec<u32>,
    pub(super) support_receiver_classes: Buffer,
    pub(super) support_quadratic_scale_limbs: Buffer,
    pub(super) support_quadratic_scale_limb_count: u32,
    pub(super) maximal_support_quadratic_scale: BigUint,
    pub(super) occurrence_receiver_offsets_host: Vec<u32>,
    pub(super) occurrence_term_offsets_host: Vec<u64>,
    pub(super) sparse_pair_receivers: Option<ResidentSparseQuadraticReceiverMount>,
    pub(super) sparse_pair_boundary_conditioners:
        Option<ResidentSparseQuadraticBoundaryConditionerMount>,
    /// Cold complete fibre retained beside the mounted sparse receiver face.
    #[allow(dead_code)]
    pub(super) reconstruction_fibre: AddressedPrimitiveReceiverFrame,
    pub(super) resident_octets: u64,
}

pub(super) struct ResidentSparseQuadraticReceiverMount {
    pub(super) receiver_offsets: Buffer,
    pub(super) pair_coordinates: Buffer,
    pub(super) coefficient_signs: Buffer,
    pub(super) coefficient_limbs: Buffer,
    pub(super) coefficient_limb_count: u32,
    pub(super) maximal_receiver_l1: BigUint,
}

/// The exact local factor restriction carried by every currently visible exterior port.  This is
/// mounted beside the addressed receiver frame and acts only after that receiver has returned a
/// unique port.  Its width is the native factor population; the port axis remains an exterior
/// boundary chart.
pub(super) struct ResidentSparseQuadraticBoundaryConditionerMount {
    pub(super) port_population: u32,
    pub(super) factor_population: u32,
    pub(super) coefficient_limb_count: u32,
    pub(super) maximal_coefficient: BigUint,
    pub(super) coefficients: Buffer,
    pub(super) identity_sha256: String,
}
