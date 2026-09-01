//! Native outward radiation and its later exterior prose chart.
//!
//! A receiver aperture is frozen from rested incidence before any request arrives.  Exterior
//! octets become one exact boundary current without token, word, deed, or semantic classification.
//! The GPU returns the native radiation section first.  Only then may the separately retained
//! relational codec render every cell in the predeclared receiver fibre.

use holonic_engine::{
    cuda_refine::{
        ResidentFactoredMomentReceiverReturn, ResidentFactoredReceiverHistoryReceipt,
        ResidentGeneratedPortCurrentPassageReturn, ResidentQuadraticMomentFront,
        ResidentQuadraticMomentPortReturn, ResidentQuadraticMomentReturn,
    },
    receiver_history_compression::ProjectiveCurrentSection,
    AddressedGeneratedPortSlot, ExactComplexWaveCurrent,
};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

use super::{
    ExteriorOccurrenceFibre, GranularBoundaryBranch, GranularExteriorPort,
    GranularExteriorProjectiveCurrent, GranularHigherBoundaryFace, GranularReconstructionNode,
    MorphologyDerivedCurrentSection,
};

pub const NATIVE_RADIATION_SCHEMA: &str = "soma-life.native-radiation.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorParticipantReceiverChart {
    /// A cold codec coordinate. It is permitted to select the exterior receiver projection, but
    /// never a developmental factor, native cell, constitutive law, or prepared response.
    pub receiver_region: Vec<String>,
    pub participant_alias: (u32, u32),
    pub receiver_faces: Vec<u32>,
    pub receiver_factor_sections: Vec<ReceiverFactorActionSection>,
    pub relational_cell_addresses: Vec<String>,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverFactorActionSection {
    pub factor: u32,
    pub current: ExactComplexWaveCurrent,
    pub caused_population: u64,
    pub oriented_causal_moment: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeRadiationAperture {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub receiver_port_faces: Vec<u32>,
    pub participant_receiver_charts: Vec<ExteriorParticipantReceiverChart>,
    pub relation_receiver_charts: Vec<ExteriorRelationReceiverChart>,
    pub relational_cell_indices: Vec<usize>,
    pub relational_cell_addresses: Vec<String>,
    /// Oriented 2-cell boundaries aligned with `relational_cell_addresses`.  This is the actual
    /// simplicial contact chart used for a returned local star; source-factor co-occurrence is a
    /// separate affine receiver and cannot substitute for shared boundary incidence.
    pub relational_cell_boundaries: Vec<Vec<u32>>,
    pub left_contact_cell: String,
    pub right_contact_cell: String,
    pub target_query_was_visible_when_frozen: bool,
    pub deed_or_semantic_mode_supplied: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorRelationReceiverChart {
    pub receiver_region: Vec<String>,
    pub receiver_face: u32,
    pub receiver_factor_sections: Vec<ReceiverFactorActionSection>,
    pub identity_sha256: String,
}

/// Exact exterior current of a complete caused octet population.  The two coordinates are total
/// mass and oriented adjacent change; neither is a token or semantic feature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorActionCurrent {
    pub occurrence: String,
    pub caused_octet_population: u64,
    pub section: ExactComplexWaveCurrent,
    pub current: ExactComplexWaveCurrent,
    pub source_sha256: String,
    /// Ordered exterior source lineage.  A later request may be preceded by a genuinely returned
    /// surface without flattening the two caused occurrences into one ambiguous receiver string.
    pub source_components: Vec<ExteriorSourceComponent>,
    /// Complete moved exterior incidence for this crossing. It is consumed by native radiation
    /// and is never written into rested morphology or used as a native address.
    #[serde(skip_serializing)]
    pub(super) causal_octets: Vec<u8>,
    /// The codec's plural relation-phase fibres as caused octet populations. They are retained
    /// separately so their boundaries are not flattened into a semantic label or native key.
    #[serde(skip_serializing)]
    pub(super) causal_relation_phase_octets: Vec<Vec<u8>>,
    /// Cold receiver coordinates returned by the declared relational boundary codec. They may
    /// choose an exterior projection but cannot choose the native response.
    pub receiver_regions: Vec<Vec<String>>,
    /// Exterior relation testimony retained for reconstruction and audit. Native conduct below
    /// does not branch on these labels.
    pub relation_phase_words: Vec<String>,
    pub boundary_codec_applied: bool,
    pub native_tokenization_performed: bool,
    pub semantic_classification_performed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorSourceComponent {
    pub occurrence: String,
    pub caused_octet_population: u64,
    pub source_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeRadiationSection {
    pub schema: String,
    pub aperture_identity_sha256: String,
    pub rested_identity_sha256: String,
    pub exterior_occurrence: String,
    /// Exact cold-lineage identity of the exterior source which caused this native section.
    /// The source bytes remain exterior; this digest binds the returned section to their complete
    /// fibre without promoting the exterior spelling into a native coordinate.
    pub exterior_source_sha256: String,
    /// A refinement successor retains the exact prior native radiation and is restricted to its
    /// affine local star.  Ordinary ingress has no predecessor here.
    pub predecessor_radiation_identity_sha256: Option<String>,
    pub carried_relational_cell_addresses: Vec<String>,
    pub native_ordered_word: Vec<holonic_engine::receiver_exact_compression::InputId>,
    pub family_overlaps: Vec<Rat>,
    pub native_radiation: ExactComplexWaveCurrent,
    pub injected_boundary_current: ExactComplexWaveCurrent,
    pub returned_radiation: ExactComplexWaveCurrent,
    pub participant_receiver_chart_identity_sha256: String,
    pub participant_alias: (u32, u32),
    pub relation_receiver_chart_identities_sha256: Vec<String>,
    pub unresolved_relation_phase_words: Vec<String>,
    /// Digest and population of the complete port-resolved radiation section before a cold
    /// exterior receiver chooses its emitted face.  The full exact field remains live below so a
    /// successor can form its situated difference without factoring through the predecessor's
    /// already-condensed surface.
    pub relational_cell_radiation_identity_sha256: String,
    pub relational_cell_radiation_population: u32,
    #[serde(skip_serializing)]
    pub(super) relational_cell_radiation: Vec<NativeRelationalCellRadiation>,
    pub emitted_relational_cell_addresses: Vec<String>,
    pub retained_relational_cell_fibre: Vec<String>,
    pub renderer_has_not_run: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalCellRadiation {
    pub(super) cell_address: String,
    pub(super) returned_current: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorRadiationSurface {
    pub radiation_identity_sha256: String,
    pub exterior_occurrence: String,
    pub text: String,
    pub text_sha256: String,
    pub rendered_cell_addresses: Vec<String>,
    pub candidate_search_performed: bool,
    pub stored_sentence_selected: bool,
    pub expected_answer_consulted: bool,
}

/// One cold exterior higher face with its exact reconstruction fibre and shared per-port moment
/// contraction retained.  Plural generator faces at one port share the same receiver quotient;
/// their distinct lineage remains in `boundary`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularRadiationBranch {
    pub higher_face: GranularHigherBoundaryFace,
    pub exterior_port: GranularExteriorPort,
    pub exterior_passage: Vec<GranularExteriorPort>,
    pub boundary: GranularBoundaryBranch,
    pub resident_current: ResidentQuadraticMomentPortReturn,
    pub returned_response: ExactComplexWaveCurrent,
    pub lies_in_port_kernel: bool,
    pub lies_in_receiver_phase_front: bool,
}

/// The fine outward boundary before any word, clause, or semantic renderer exists.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularRadiationSection {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub entered_octet_population: u64,
    pub reached_state: u32,
    pub reached_matched_length: u32,
    pub greatest_productive_matched_length: Option<u32>,
    pub crossed_structural_ports: Vec<GranularExteriorPort>,
    pub branches: Vec<GranularRadiationBranch>,
    pub visible_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub visible_ports: Vec<GranularExteriorPort>,
    pub visible_passages: Vec<Vec<GranularExteriorPort>>,
    pub kernel_ports: Vec<GranularExteriorPort>,
    /// One complete resident port-resolved circulation.  Supports and ports are retained rather
    /// than reduced to the winning exterior face; storage carries the exact unreturned current.
    pub resident_joint_current: ResidentQuadraticMomentReturn,
    /// Present after the source-family foundation. This is the exact source-to-target image
    /// world-line whose receiver produced `resident_joint_current`; only its target continues.
    pub resident_image_passage: Option<ResidentFactoredMomentReceiverReturn>,
    /// Exact sparse rank-one presentation of the local moment, retained beside its addressed
    /// reconstruction DAG so a richer receiver can reopen the condensed family.
    pub quadratic_moment_factorization: ResidentQuadraticMomentFront,
    pub reconstruction_dag: Vec<GranularReconstructionNode>,
    pub exact_decoded_higher_face: Option<GranularHigherBoundaryFace>,
    pub exact_decoded_port: Option<GranularExteriorPort>,
    pub exact_decoded_passage: Option<Vec<GranularExteriorPort>>,
    pub plural_receiver_insufficiency: bool,
    pub complete_reconstruction_fibre_retained: bool,
    pub word_or_clause_renderer_ran: bool,
    pub identity_sha256: String,
}

/// The actual-membrane equality gate for the factored receiver-history operation complex.  The
/// resident presentation and cold direct restriction witness traverse the same mounted body; this
/// receipt retains the exact semantic equality and the distinct apparatus costs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FactoredReceiverHistoryGateReceipt {
    pub schema: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub operation_complex: ResidentFactoredReceiverHistoryReceipt,
    pub resident_restriction_population: usize,
    pub direct_restriction_population: usize,
    pub exact_direct_versus_resident_consequence: bool,
    pub exact_direct_versus_factored_consequence: bool,
    pub exact_direct_versus_descended_transport: bool,
    pub exact_direct_versus_resident_transport: bool,
    pub source_current_section_population: usize,
    pub first_target_current_section_population: usize,
    pub second_target_current_section_population: usize,
    pub resident_current_generations: [u64; 3],
    pub resident_joining_addresses_close: bool,
    pub resident_image_generations: [u64; 3],
    pub resident_image_joining_addresses_close: bool,
    pub resident_image_receiver_population: usize,
    pub exact_direct_versus_resident_image_receivers: bool,
    pub resident_image_atomic_replacements: bool,
    pub resident_image_source_release_after_device_admission: bool,
    pub resident_image_host_rational_continuation: bool,
    pub resident_image_apparatus_shape_host_egress_octets: u64,
    pub resident_image_intermediate_host_egress_octets: u64,
    pub resident_image_launches: u64,
    pub resident_image_synchronizations: u64,
    pub factored_present_receiver_population: usize,
    pub ambient_covariance_materialized: bool,
    pub source_family_rescanned_by_successor: bool,
    pub resident_transport_source_context_population: usize,
    pub resident_transport_candidate_context_population: usize,
    pub resident_transport_target_context_population: usize,
    pub resident_transport_reconstruction_edge_population: usize,
    pub resident_successor_transport_target_context_population: usize,
    pub resident_successor_transport_reconstruction_edge_population: usize,
    pub resident_successor_transport_host_ingress_octets: u64,
    pub same_card_context: bool,
    pub resident_successor_host_ingress_octets: u64,
    pub direct_successor_host_ingress_octets: u64,
    pub resident_intermediate_host_egress_octets: u64,
    pub resident_invariant_transport_reuploaded: bool,
    pub resident_cpu_semantic_replay_after_device: bool,
    pub resident_launches: u64,
    pub resident_synchronizations: u64,
    pub resident_transport_launches: u64,
    pub resident_transport_synchronizations: u64,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub enum GranularEmanativeTerminal {
    Closure,
    RecurrentFactorizedMoment {
        continuation_identity_sha256: String,
    },
    PluralReceiverInsufficiency,
}

/// The complete hot recurrence coordinate admitted by the factored receiver-history complex.
/// Equality is structural over the returned boundary consequence and every declared exact
/// receiver coordinate; the source factorization and reconstruction DAG remain outside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct FactoredObservableContinuation {
    operation_complex_identity_sha256: String,
    returned_higher_faces: Vec<GranularHigherBoundaryFace>,
    ports: Vec<ResidentQuadraticMomentPortReturn>,
    port_returns: Vec<holonic_engine::cuda_refine::ResidentBoundaryChainPortReturn>,
    total_returned_current: ExactComplexWaveCurrent,
    stored_difference: ExactComplexWaveCurrent,
    local_balance_closes: bool,
    phase_locked_port_population: usize,
    phase_front_is_unique: bool,
}

impl FactoredObservableContinuation {
    pub(super) fn from_section(section: &GranularRadiationSection) -> Self {
        Self {
            operation_complex_identity_sha256: section
                .resident_joint_current
                .factored_receiver_history
                .identity_sha256
                .clone(),
            returned_higher_faces: section.visible_higher_faces.clone(),
            ports: section.resident_joint_current.ports.clone(),
            port_returns: section.resident_joint_current.port_returns.clone(),
            total_returned_current: section
                .resident_joint_current
                .total_returned_current
                .clone(),
            stored_difference: section.resident_joint_current.stored_difference.clone(),
            local_balance_closes: section.resident_joint_current.local_balance_closes,
            phase_locked_port_population: section
                .resident_joint_current
                .phase_locked_port_population,
            phase_front_is_unique: section.resident_joint_current.phase_front_is_unique,
        }
    }
}

/// One outward recurrence of the same carried Athena section.  Exterior octets are accumulated
/// only after the resident phase receiver returns them; they never enter cultivation or select an
/// interior factor.  Closure, a tied front, or exact projective recurrence terminates the passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularEmanativeResponse {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    /// The complete nondominated higher-face current returned at every causal order. This is a
    /// product of exact finite strata, not an enumerated list of candidate strings.
    pub returned_higher_face_strata: Vec<Vec<GranularHigherBoundaryFace>>,
    /// Present only when every returned stratum determines one exterior port. Plural generators
    /// at that port remain lawful; plural ports keep this reconstruction open.
    pub exact_exterior_passage: Option<Vec<GranularExteriorPort>>,
    pub emitted_octets: Vec<u8>,
    pub exterior_utf8: Option<String>,
    pub sections: Vec<GranularRadiationSection>,
    pub boundary_closure_reached: bool,
    pub terminal: GranularEmanativeTerminal,
    pub renderer_ran_before_native_closure: bool,
    pub identity_sha256: String,
}

/// One exact exterior source fibre beside the response produced from its primitive-ray ingress.
/// The projective current is the hot future-consequence quotient; its source bytes and standing
/// potential identity reopen every omitted path-population and common-scale coordinate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularProjectiveEmanativeReturn {
    pub ingress: GranularExteriorProjectiveCurrent,
    pub response: GranularEmanativeResponse,
}

/// One primitive-ray ingress beside its first resident radiation section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GranularProjectiveRadiationReturn {
    pub ingress: GranularExteriorProjectiveCurrent,
    pub section: GranularRadiationSection,
}

pub const OPEN_WORLD_TUBE_RADIATION_SCHEMA: &str = "soma-life.open-world-tube-radiation.v2";

/// One coordinate of the complete source-neutral outward factor receiver.  The unit incidence is
/// the basis vector of the standing affine factor line, not a behavioral width or authored score.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOutwardPortReturn {
    pub port: u32,
    pub universal_port: u32,
    pub returned_response: ExactComplexWaveCurrent,
    /// Exact situated receiver coordinates over the generator faces carried by this physical
    /// port, in native generator order (and source-state order when that fibre remains plural).
    /// A later codec may declare a chart over these coordinates; their order is not an authored
    /// semantic label.
    pub situated_receiver_coordinates: Vec<BigInt>,
    pub situated_coordinate_denominator: BigInt,
    pub lies_in_outward_radical: bool,
    pub lies_in_receiver_phase_front: bool,
}

/// One exact projective receiver occurrence of the completed generated-port junction.  The local
/// ray and removed scale are absent exactly on a radical occurrence; source, selected slot, port,
/// generator, target and both projective boundary maps remain explicit reconstruction testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratedPortProjectiveOccurrence {
    pub source_context: u32,
    pub source_ray: u32,
    pub selected_slot: u32,
    pub port: u32,
    pub generator: u32,
    pub target_context: Option<u32>,
    pub target_ray: Option<u32>,
    pub removed_scale: BigUint,
}

/// Projective chart of a generated-port junction.  This is deliberately not a generator direct
/// sum: restriction occurs before local currents meet linearly at their addressed target site.
/// The complete occurrence fibre retains that difference and prevents the target-site sum from
/// masquerading as an independent-ray transport.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratedPortProjectivePassage {
    pub schema: String,
    pub factor_population: u32,
    pub port_population: u32,
    pub generator_population: u32,
    pub generator_targets: Vec<u32>,
    pub slots: Vec<AddressedGeneratedPortSlot>,
    pub source: ProjectiveCurrentSection,
    pub target: ProjectiveCurrentSection,
    pub occurrences: Vec<GeneratedPortProjectiveOccurrence>,
    pub complete_reconstruction_fibre_retained: bool,
}

/// One causal order of the open native current.  The current is restricted on the card before its
/// exact generator descent returns; the next order continues only by the returned resident target
/// address and its complete addressed passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpenWorldTubeOrder {
    pub causal_order: u64,
    pub resident_restriction: ResidentQuadraticMomentReturn,
    pub outward_port_returns: Vec<NativeOutwardPortReturn>,
    /// Exact dynamic quotient of the same scale-bearing descent.  Primitive rays are the rested
    /// state; removed scales, weights, edges, and source contexts remain its reconstruction fibre.
    pub projective_descent: GeneratedPortProjectivePassage,
    pub lawful_silence_population: usize,
    pub compulsory_radiation_population: usize,
    pub local_balance_closes: bool,
    pub complete_reconstruction_fibre_retained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", tag = "terminal")]
pub enum NativeOpenWorldTubeTerminal {
    /// Every admitted generator leaves the complete condensed current family invariant, so the
    /// current may return to rest through the exact dynamic quotient.
    DynamicallyCondensedRest {
        resident_current_identity_sha256: String,
        projective_ray_population: usize,
        scale_reconstruction_fibre_retained: bool,
    },
    /// A nonstationary complete current front returned exactly.  It remains an open obstruction;
    /// no turn limit or host timeout is promoted into native closure.
    OpenLaterFront {
        returned_causal_order: u64,
        resident_current_identity_sha256: String,
        projective_ray_population: usize,
        scale_reconstruction_fibre_retained: bool,
    },
}

/// Canonical integral lattice chart of one exact complex exterior current.  The quadratic
/// numerator weights the native frontier; its denominator and oriented components retain the
/// exact rebase, so an integral apparatus coordinate is never mistaken for a quiet scalar.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorCurrentQuadraticLift {
    pub common_denominator: BigUint,
    pub integral_real: BigInt,
    pub integral_imaginary: BigInt,
    pub quadratic_numerator: BigUint,
    pub quadratic_denominator: BigUint,
}

/// One exact exterior-current section carried through the same resident body until dynamic rest
/// or the declared immediate-and-later receiver family returns an exact open front.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpenWorldTubeCurrentReturn {
    pub source_section: u64,
    pub presented_section: ExactComplexWaveCurrent,
    pub presented_current: ExactComplexWaveCurrent,
    pub transported_section: ExactComplexWaveCurrent,
    pub transported_current: ExactComplexWaveCurrent,
    pub exterior_quadratic_lift: ExteriorCurrentQuadraticLift,
    pub orders: Vec<NativeOpenWorldTubeOrder>,
    pub terminal: NativeOpenWorldTubeTerminal,
}

/// Exact serializable testimony of one open sensory occurrence.  The move-owned source object is
/// returned separately in [`NativeOpenWorldTubeReturn`]; only its cold address appears here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpenWorldTubeReceipt {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub exterior_occurrence: String,
    pub exterior_source_sha256: String,
    pub exterior_incidence_sha256: String,
    pub caused_population: u64,
    pub ingress_current_fibre: Vec<MorphologyDerivedCurrentSection>,
    pub frontier_current_fibre: Vec<MorphologyDerivedCurrentSection>,
    pub outward_port_population: usize,
    pub current_returns: Vec<NativeOpenWorldTubeCurrentReturn>,
    pub lawful_silence_present: bool,
    pub compulsory_nonradical_radiation_present: bool,
    pub every_generator_descent_returned_on_card: bool,
    pub exact_dynamic_condensation_or_open_front_returned: bool,
    pub source_fibre_remained_exact: bool,
    pub word_or_clause_renderer_ran: bool,
    pub wake_word_or_vad_gate_present: bool,
    pub timer_or_maximum_turn_present: bool,
    pub host_selected_native_contact: bool,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub identity_sha256: String,
}

/// Move-owned return of the one exterior source beside its native recurrence receipt.
pub struct NativeOpenWorldTubeReturn {
    pub exterior: ExteriorOccurrenceFibre,
    pub receipt: NativeOpenWorldTubeReceipt,
}

mod aperture;
mod factored_history;
mod granular_emanation;
mod open_world;
mod receiver_projection;
mod validation;

use aperture::exterior_boundary_current;
use receiver_projection::{
    derive_participant_receiver_charts, derive_relation_receiver_charts, emitted_relational_front,
    first_quadratic_receiver_projective_separator, first_quadratic_receiver_separator,
    quadratic_receiver_projection_identity_sha256,
};
pub use validation::NativeRadiationError;
use validation::{
    canonical_projective_rays, digest, exterior_current_quadratic_lift, first_founded_contact,
    found_aperture, generated_port_projective_passage, hex_sha256, projective_current_section,
};
