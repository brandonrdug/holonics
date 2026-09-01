use super::*;
pub const SOURCE_NEUTRAL_ECOLOGY_REST_SCHEMA: &str = "soma-life.source-neutral-ecology-rest.v5";
pub(super) const SOURCE_NEUTRAL_ACOUSTIC_MORPHOLOGY_SCHEMA: &str =
    "soma-life.source-neutral-acoustic-incidence.v1";
pub(super) const SOURCE_NEUTRAL_OPTICAL_MORPHOLOGY_SCHEMA: &str =
    "soma-life.source-neutral-optical-incidence.v1";

#[derive(Debug, Error)]
pub enum SourceNeutralEcologyError {
    #[error("the continuing native ecology is malformed: {0}")]
    Body(String),
    #[error("the granular organ is malformed: {0}")]
    Granular(String),
    #[error("the source-neutral sensory morphology is malformed")]
    Sensory,
    #[error("the source-neutral ecology wire is malformed: {0}")]
    Wire(String),
    #[error("the resident apparatus refused the source-neutral ecology body: {0}")]
    Apparatus(String),
}

/// Reusable acoustic port incidence after historical founding coordinates have left the hot
/// morphology.  It carries no samples, waveform, source radiation, or predecessor identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralAcousticMorphology {
    pub(super) schema: String,
    pub(super) ordered_ports: Vec<(u32, u32)>,
    pub(super) quadrature_population: u32,
    pub(super) phase_extent: u32,
    pub(super) identity_sha256: String,
}

/// Reusable optical port/scale incidence after historical founding coordinates have left the hot
/// morphology.  It carries no raster, pixel template, label route, or predecessor identity.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralOpticalMorphology {
    pub(super) schema: String,
    pub(super) ordered_ports: Vec<(u32, u32)>,
    pub(super) lattice_width: u32,
    pub(super) lattice_height_per_order: u32,
    pub(super) scale_spans: Vec<u32>,
    pub(super) identity_sha256: String,
}

/// One source-neutral cultivation branch retained in the continuing ecology. Delivery population
/// identities have departed; the native pullback, thread, covector, and return operator remain.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralCultivationBranch {
    pub branch: usize,
    pub k3_pullback_address: String,
    pub thread_address: String,
    pub returned_covector: Vec<Rat>,
    pub local_population: usize,
    pub exact_fibre_population: usize,
    pub return_operator_identity_sha256: String,
}

/// One genuinely returned difference after its developmental occurrence identity has departed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralReturnedDeposit {
    pub difference_identity_sha256: String,
    pub thread_address: String,
    pub winding_coefficients: Vec<Rat>,
    pub return_operator_identity_sha256: String,
    pub native_receipt: NativeThreadDepositReceipt,
}

/// Exact source-neutral receipt for one later situated difference entering the same ecology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralReturnedDifferenceReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub difference_identity_sha256: String,
    pub thread_address: String,
    pub returned_covector: Vec<Rat>,
    pub native_receipt: NativeThreadDepositReceipt,
    pub granular_identity_sha256: String,
    pub relational_identity_sha256: String,
    pub realization_identity_sha256: String,
    pub acoustic_identity_sha256: String,
    pub optical_identity_sha256: String,
    pub morphologies_preserved: bool,
    pub source_detached_before_rest: bool,
}

/// Move-owned inverse of the newest source-neutral returned difference. Restoration consumes the
/// native deposit; no second body or hidden morphology copy remains beside the predecessor.
#[derive(Debug, PartialEq, Eq)]
pub struct SourceNeutralReturnedDifferenceWithdrawal {
    pub(super) original_rest_identity_sha256: String,
    pub(super) predecessor_rest_identity_sha256: String,
    pub(super) returned: SourceNeutralReturnedDeposit,
    pub(super) native_deposit: NativeThreadDeposit,
}

/// The recurrent returned ecology after predecessor-wire and delivery identities have been
/// quotiented away. The complete native spool body and deposit receipts remain executable.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralReturnedEcology {
    pub(super) schema: String,
    pub(super) ecology: NativeSituatedSpoolBundle,
    pub(super) branches: Vec<SourceNeutralCultivationBranch>,
    pub(super) predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    pub(super) returned_deposits: Vec<SourceNeutralReturnedDeposit>,
    pub(super) identity_sha256: String,
}

/// The one continuing ecology body after the reversible developmental chart has departed.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralEcologyRest {
    pub(super) schema: String,
    pub(super) body: SourceNeutralReturnedEcology,
    pub(super) granular: NativeGranularPotential,
    pub(super) relational: SourceNeutralRelationalMorphology,
    pub(super) realization: SourceNeutralExteriorRealizationMorphology,
    pub(super) acoustic: SourceNeutralAcousticMorphology,
    pub(super) optical: SourceNeutralOpticalMorphology,
    pub(super) identity_sha256: String,
}

/// The one move-owned source-neutral ecology body after its invariant incidence, constitutive
/// families, receiver faces, and boundary atlas have crossed the resident card.
pub struct ResidentSourceNeutralEcology {
    pub(super) rest: SourceNeutralEcologyRest,
    pub(super) resident: ResidentMembraneInteriorWord,
    pub(super) receiver_history: SourceNeutralReceiverHistoryConstitution,
    pub(super) realization_site_history: SourceNeutralExteriorSiteHistoryQuotient,
}

/// Source-neutral receiver constitution retained beside the one resident body. These are exact
/// native incidence charts derived before any release question is mounted; no codec label or
/// requested surface can alter them.
pub(super) struct SourceNeutralReceiverHistoryConstitution {
    pub(super) factor_capacity: Vec<u64>,
    pub(super) generator_ids: Vec<InputId>,
    pub(super) generators: Vec<Vec<u32>>,
    pub(super) compression: ReceiverHistoryCompression,
    pub(super) resident_compression: ResidentReceiverHistoryCompressionReceipt,
}

/// Native fine radiation after projective ingress, generator transport, exact equal-section
/// condensation, and resident Complex-Parametron contraction.  No exterior surface codec has yet
/// acted on this section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralResidentRadiationSection {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub ingress_current_identity_sha256: String,
    pub entered_octet_population: u64,
    pub crossed_structural_ports: Vec<GranularExteriorPort>,
    pub boundary_front: Vec<u32>,
    /// The complete fine boundary incidence before the exterior port quotient. Distinct
    /// generator faces at one port remain distinct branches.
    pub branches: Vec<SourceNeutralRadiationBranch>,
    /// The nondominated receiver phase front. A unique port may still carry plural generator
    /// lineage. This complete native front is retained even when the situated exterior receiver
    /// resolves a smaller continuation fibre.
    pub phase_front_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub phase_front_ports: Vec<GranularExteriorPort>,
    /// The maximum fibre of the declared exterior receiver pairing over the native phase front.
    /// It is a situated quotient, not a replacement for the native front; exact ties remain
    /// plural and therefore obstruct rather than being broken by an address or codec label.
    pub situated_receiver_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub situated_receiver_ports: Vec<GranularExteriorPort>,
    /// Complete reacted successor founded before the situated/projective observer.  These are
    /// the two addressed boundary legs of the resident generated-port current passage, not the
    /// observer-selected phase front.
    pub complete_successor_addressed_faces: Vec<GranularAddressedHigherBoundaryFace>,
    /// Exact zero-support complement in `boundary × port × generator`.
    pub complete_successor_zero_face_population: usize,
    pub radiation: ResidentQuadraticMomentReturn,
    pub reconstruction_dag: Vec<GranularReconstructionNode>,
    pub native_section_identity_sha256: String,
    pub source_codec_consulted: bool,
    pub exterior_reconstruction_fibre_reachable: bool,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

impl SourceNeutralResidentRadiationSection {
    /// Exact equality at the native conduct receiver.  CUDA context handles, launch counts,
    /// synchronization counts, transfer quantities and other remount apparatus testimony are not
    /// causal coordinates of this receiver; they remain available in `radiation` and may differ.
    /// This method compares the actual stable fields used by the native-section identity rather
    /// than treating digest equality as source equality.
    pub fn same_native_receiver_consequence(&self, other: &Self) -> bool {
        let self_conditioned = self
            .radiation
            .conditioned_current
            .as_ref()
            .map(|conditioned| &conditioned.passage);
        let other_conditioned = other
            .radiation
            .conditioned_current
            .as_ref()
            .map(|conditioned| &conditioned.passage);
        self.schema == other.schema
            && self.rest_identity_sha256 == other.rest_identity_sha256
            && self.ingress_current_identity_sha256 == other.ingress_current_identity_sha256
            && self.entered_octet_population == other.entered_octet_population
            && self.crossed_structural_ports == other.crossed_structural_ports
            && self.boundary_front == other.boundary_front
            && self.branches == other.branches
            && self.phase_front_higher_faces == other.phase_front_higher_faces
            && self.phase_front_ports == other.phase_front_ports
            && self.situated_receiver_higher_faces == other.situated_receiver_higher_faces
            && self.situated_receiver_ports == other.situated_receiver_ports
            && self.complete_successor_addressed_faces == other.complete_successor_addressed_faces
            && self.complete_successor_zero_face_population
                == other.complete_successor_zero_face_population
            && self_conditioned == other_conditioned
            && self.radiation.receiver_coordinate_denominator
                == other.radiation.receiver_coordinate_denominator
            && self.radiation.ports == other.radiation.ports
            && self.radiation.port_returns == other.radiation.port_returns
            && self.radiation.entering_current == other.radiation.entering_current
            && self.radiation.total_returned_current == other.radiation.total_returned_current
            && self.radiation.stored_difference == other.radiation.stored_difference
            && self.radiation.local_balance_closes == other.radiation.local_balance_closes
            && self.radiation.phase_locked_port_population
                == other.radiation.phase_locked_port_population
            && self.radiation.phase_front_is_unique == other.radiation.phase_front_is_unique
            && self.radiation.situated_receiver_pairing == other.radiation.situated_receiver_pairing
            && self.radiation.complete_successor_faces == other.radiation.complete_successor_faces
            && self.radiation.complete_successor_face_population
                == other.radiation.complete_successor_face_population
            && self.radiation.active_factor_population == other.radiation.active_factor_population
            && self.radiation.native_factor_population == other.radiation.native_factor_population
            && self.radiation.moment_field_materialized == other.radiation.moment_field_materialized
            && self.radiation.moment_factorization_retained
                == other.radiation.moment_factorization_retained
            && self.radiation.context_population == other.radiation.context_population
            && self.radiation.restriction_population == other.radiation.restriction_population
            && self.radiation.generator_population == other.radiation.generator_population
            && self.reconstruction_dag == other.reconstruction_dag
            && self.native_section_identity_sha256 == other.native_section_identity_sha256
            && self.source_codec_consulted == other.source_codec_consulted
            && self.exterior_reconstruction_fibre_reachable
                == other.exterior_reconstruction_fibre_reachable
            && self.invariant_transport_reuploaded == other.invariant_transport_reuploaded
            && self.cpu_semantic_replay_after_device == other.cpu_semantic_replay_after_device
    }
}

/// Native recurrence after the one source-family quadratic image has replaced that family on the
/// card. The optional foundation occurs exactly once and retains the source-to-image fibre as cold
/// testimony; every later section carries only the continuing resident image address and its
/// exact receiver return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralFactoredRadiationSection {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub ingress_current_identity_sha256: String,
    pub entered_octet_population: u64,
    pub crossed_structural_ports: Vec<GranularExteriorPort>,
    pub boundary_front: Vec<u32>,
    pub branches: Vec<SourceNeutralRadiationBranch>,
    pub phase_front_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub phase_front_ports: Vec<GranularExteriorPort>,
    pub situated_receiver_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub situated_receiver_ports: Vec<GranularExteriorPort>,
    /// Complete productive native successor with both boundary legs.  This population is founded
    /// before observation and alone may carry the resident image into the next order.
    pub complete_successor_addressed_faces: Vec<GranularAddressedHigherBoundaryFace>,
    /// Exact zero-support complement within the addressed face chart.
    pub complete_successor_zero_face_population: usize,
    pub factored_foundation: Option<ResidentSparseQuadraticMomentFoundationReturn>,
    pub factored_image_passage: ResidentFactoredMomentReceiverReturn,
    pub radiation: ResidentQuadraticMomentReturn,
    pub reconstruction_dag: Vec<GranularReconstructionNode>,
    pub native_section_identity_sha256: String,
    pub source_codec_consulted: bool,
    pub exterior_reconstruction_fibre_reachable: bool,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// One native higher-boundary branch joined to its exact resident receiver return. This is still
/// pre-codec topology: `exterior_port` is a boundary-face coordinate, not generated text.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralRadiationBranch {
    pub local_port: u32,
    pub higher_face: GranularHigherBoundaryFace,
    pub exterior_port: GranularExteriorPort,
    pub boundary: GranularBoundaryBranch,
    pub resident_current: ResidentQuadraticMomentPortReturn,
    pub returned_response: ExactComplexWaveCurrent,
    pub lies_in_port_kernel: bool,
    pub lies_in_receiver_phase_front: bool,
    pub lies_in_situated_receiver_front: bool,
}

/// Join the completed native response chart to the addressed generated-port target sections.
/// This is an internal carrier presentation for the realization boundary: exterior port and
/// generator numbers remain anonymous incidence coordinates, and no displayed surface enters.
pub(super) fn native_oriented_realization_faces(
    section: &SourceNeutralResidentRadiationSection,
    passage: &AddressedGeneratedPortJunctionPassage,
    resident_local_currents: &[ResidentGeneratedPortLocalCurrent],
) -> Result<Vec<SourceNeutralNativeOrientedFace>, SourceNeutralEcologyError> {
    let pairing = section
        .radiation
        .situated_receiver_pairing
        .as_ref()
        .ok_or_else(|| {
            SourceNeutralEcologyError::Apparatus(
                "the native section omitted its oriented relational pairing".to_owned(),
            )
        })?;
    let population = pairing.relational_oriented_real_coordinates.len();
    if population == 0
        || pairing.relational_oriented_imaginary_coordinates.len() != population
        || pairing.face_source_states.len() != population
        || pairing.face_ports.len() != population
        || pairing.face_generators.len() != population
        || pairing.coordinate_denominator.is_zero()
        || pairing.coordinate_denominator.is_negative()
        || pairing.front_faces.is_empty()
        || pairing
            .front_faces
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || pairing
            .front_faces
            .iter()
            .any(|face| *face as usize >= population)
        || passage.generator_population == 0
    {
        if holonic_engine::cuda_refine::trace_configuration().holonics_uar2_trace {
            eprintln!(
                "oriented-native-chart refusal real={} imaginary={} states={} ports={} generators={} denominator={} passage-generators={}",
                population,
                pairing.relational_oriented_imaginary_coordinates.len(),
                pairing.face_source_states.len(),
                pairing.face_ports.len(),
                pairing.face_generators.len(),
                pairing.coordinate_denominator,
                passage.generator_population,
            );
        }
        return Err(SourceNeutralEcologyError::Apparatus(
            "the native oriented response chart is incomplete".to_owned(),
        ));
    }
    let mut faces = Vec::new();
    for mode in pairing
        .front_faces
        .iter()
        .copied()
        .map(|mode| mode as usize)
    {
        let source_state = (pairing.face_source_states[mode] != u32::MAX)
            .then_some(pairing.face_source_states[mode]);
        let native_port = pairing.face_ports[mode];
        let native_generator = pairing.face_generators[mode];
        let selected_slots = passage
            .slots
            .iter()
            .enumerate()
            .filter(|slot| {
                slot.1.port == native_port
                    && slot.1.generator == native_generator
                    && source_state.is_none_or(|source| slot.1.source_boundary_state == source)
            })
            .map(|(selected_slot, _)| selected_slot as u32)
            .collect::<BTreeSet<_>>();
        let local_currents = resident_local_currents
            .iter()
            .filter(|current| selected_slots.contains(&current.selected_slot))
            .map(|current| {
                if current.source_section as usize >= passage.source.len() {
                    return Err(SourceNeutralEcologyError::Apparatus(
                        "the resident local current lost its addressed source boundary".to_owned(),
                    ));
                }
                let target_state = passage
                    .target
                    .get(current.target_section as usize)
                    .and_then(|section| section.boundary_state)
                    .ok_or_else(|| {
                        SourceNeutralEcologyError::Apparatus(
                            "the resident local current lost its addressed target boundary"
                                .to_owned(),
                        )
                    })?;
                Ok((
                    target_state,
                    SourceNeutralNativeOrientedLocalCurrent {
                        source_section: current.source_section,
                        selected_slot: current.selected_slot,
                        target_section: current.target_section,
                        factor_current: current.factor_current.clone(),
                    },
                ))
            })
            .collect::<Result<Vec<_>, SourceNeutralEcologyError>>()?;
        let target_states = local_currents
            .iter()
            .map(|(target_state, _)| *target_state)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let local_currents = local_currents
            .into_iter()
            .map(|(_, current)| current)
            .collect::<Vec<_>>();
        // An absent target is an exact radical face already retained by the native section and
        // zero-support complement. It cannot become productive realization current.
        if target_states.is_empty() {
            continue;
        }
        let oriented_current = ExactComplexWaveCurrent::new(
            Rat::new(
                pairing.relational_oriented_real_coordinates[mode].clone(),
                pairing.coordinate_denominator.clone(),
            ),
            Rat::new(
                pairing.relational_oriented_imaginary_coordinates[mode].clone(),
                pairing.coordinate_denominator.clone(),
            ),
        );
        let local_face = native_port
            .checked_mul(passage.generator_population)
            .and_then(|base| base.checked_add(native_generator))
            .ok_or_else(|| {
                SourceNeutralEcologyError::Apparatus(
                    "the native oriented face exceeded its address".to_owned(),
                )
            })?;
        let branch_returned_current = section
            .branches
            .iter()
            .find(|branch| branch.local_port == local_face)
            .map(|branch| branch.returned_response.clone());
        faces.push(SourceNeutralNativeOrientedFace {
            mode: u32::try_from(mode).map_err(|_| {
                SourceNeutralEcologyError::Apparatus(
                    "the native oriented face population exceeded its address".to_owned(),
                )
            })?,
            source_state,
            native_port,
            native_generator,
            target_states,
            local_currents,
            oriented_current,
            branch_returned_current,
        });
    }
    if faces.is_empty() {
        return Err(SourceNeutralEcologyError::Apparatus(
            "the native oriented response lies entirely in the realization radical".to_owned(),
        ));
    }
    Ok(faces)
}

/// One causal-order incidence of the cold universal byte/glyph receiver. The native section and
/// its complete reconstruction DAG remain the inverse fibre; the codec adds no lexical standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorCodecOrder {
    pub causal_order: u64,
    pub emission_occurrence: Option<String>,
    pub emission_identity_sha256: Option<String>,
    pub native_section_identity_sha256: String,
    pub phase_front_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub situated_receiver_higher_faces: Vec<GranularHigherBoundaryFace>,
    /// Exact recurrence receipt for the complete native-section-to-boundary current passage.
    /// The one live circulation owns the current itself.  Historical orders retain the operator,
    /// both current commitments, every port potential, and the cold replay coordinates instead of
    /// cloning the complete sparse current into every order.
    pub realization: SourceNeutralExteriorRealizationOrderReceipt,
    pub exact_exterior_port: Option<GranularExteriorPort>,
    pub emitted_octet_position: Option<u64>,
    pub reconstruction_node_addresses: Vec<u32>,
}

/// One compact exact receipt for an oriented realization-current step.  It is not the productive
/// state and cannot be used as a selected-port continuation.  The complete source current is the
/// prior live passage (or the retained founding native section at order zero), the immutable
/// realization morphology supplies the local operator, and `causal_order` determines the ordered
/// replay.  The two structural commitments close that reconstruction while `target_current`
/// retains every exterior receiver coordinate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorRealizationOrderReceipt {
    pub schema: String,
    pub causal_order: u64,
    pub morphology_identity_sha256: String,
    pub native_section_identity_sha256: String,
    pub native_current_passage_identity_sha256: String,
    pub source_port: u16,
    pub selected_target_port: u16,
    pub source_factor_population: usize,
    pub source_site_population: usize,
    pub target_factor_population: usize,
    pub target_site_population: usize,
    pub target_current: Vec<(u16, num_rational::Ratio<BigUint>)>,
    pub source_site_current_identity_sha256: String,
    pub target_site_current_identity_sha256: String,
    pub entering_phase_numerator: BigUint,
    pub entering_phase_denominator: BigUint,
    pub returned_phase_numerator: BigUint,
    pub returned_phase_denominator: BigUint,
    pub complete_reconstruction_fibre_retained: bool,
    pub source_codec_consulted: bool,
    pub source_surface_reachable: bool,
    pub identity_sha256: String,
}

impl SourceNeutralExteriorRealizationOrderReceipt {
    pub(super) fn from_passage(
        causal_order: u64,
        passage: &SourceNeutralExteriorRealizationPassage,
    ) -> Self {
        let target_current = passage
            .target_current
            .iter()
            .map(|current| (current.target_port, current.current.clone()))
            .collect::<Vec<_>>();
        let source_site_current_identity_sha256 = digest(&(
            "soma-life.source-neutral-realization-source-site-current.v1",
            passage.morphology_identity_sha256.as_str(),
            &passage.site_current,
        ));
        let target_site_current_identity_sha256 = digest(&(
            "soma-life.source-neutral-realization-target-site-current.v1",
            passage.morphology_identity_sha256.as_str(),
            &passage.returned_site_current,
        ));
        let schema = "soma-life.source-neutral-exterior-realization-order-receipt.v1".to_owned();
        let mut receipt = Self {
            schema,
            causal_order,
            morphology_identity_sha256: passage.morphology_identity_sha256.clone(),
            native_section_identity_sha256: passage.native_section_identity_sha256.clone(),
            native_current_passage_identity_sha256: passage
                .native_current_passage_identity_sha256
                .clone(),
            source_port: passage.source_port,
            selected_target_port: passage.selected_target_port,
            source_factor_population: passage.factor_current.len(),
            source_site_population: passage.site_current.len(),
            target_factor_population: passage.returned_factor_current.len(),
            target_site_population: passage.returned_site_current.len(),
            target_current,
            source_site_current_identity_sha256,
            target_site_current_identity_sha256,
            entering_phase_numerator: passage.entering_phase_numerator.clone(),
            entering_phase_denominator: passage.entering_phase_denominator.clone(),
            returned_phase_numerator: passage.returned_phase_numerator.clone(),
            returned_phase_denominator: passage.returned_phase_denominator.clone(),
            complete_reconstruction_fibre_retained: passage.complete_reconstruction_fibre_retained,
            source_codec_consulted: passage.source_codec_consulted,
            source_surface_reachable: passage.source_surface_reachable,
            identity_sha256: String::new(),
        };
        receipt.identity_sha256 = digest(&(
            (
                receipt.schema.as_str(),
                receipt.causal_order,
                receipt.morphology_identity_sha256.as_str(),
                receipt.native_section_identity_sha256.as_str(),
                receipt.native_current_passage_identity_sha256.as_str(),
                receipt.source_port,
                receipt.selected_target_port,
                receipt.source_factor_population,
                receipt.source_site_population,
                receipt.target_factor_population,
                receipt.target_site_population,
            ),
            (
                &receipt.target_current,
                receipt.source_site_current_identity_sha256.as_str(),
                receipt.target_site_current_identity_sha256.as_str(),
                &receipt.entering_phase_numerator,
                &receipt.entering_phase_denominator,
                &receipt.returned_phase_numerator,
                &receipt.returned_phase_denominator,
                receipt.complete_reconstruction_fibre_retained,
                receipt.source_codec_consulted,
                receipt.source_surface_reachable,
            ),
        ));
        receipt
    }
}

/// One complete fixed-morphology feedback occurrence.  The realized exterior face and its later
/// returned occurrence remain distinct; only the source-neutral native current crosses the next
/// HNN step, while the exact exterior fibre stays cold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorInferenceReturn {
    pub causal_order: u64,
    pub emitting_native_section_identity_sha256: String,
    pub emission_occurrence: String,
    pub emitted_port: GranularExteriorPort,
    pub returned_occurrence: String,
    pub returned_port: GranularExteriorPort,
    pub returned_native_current_identity_sha256: String,
    pub returned_current_descent: SourceNeutralReturnedCurrentDescent,
    pub cold_fibre_identity_sha256: String,
    pub cold_fibre_reachable_from_productive_body: bool,
    pub morphology_changed: bool,
    pub joined_causal_order: Option<u64>,
    pub joined_native_section_identity_sha256: Option<String>,
    pub joined_conditioned_passage_identity_sha256: Option<String>,
}

/// Exact exterior delivery return for one emitted fine occurrence.  This acknowledges that the
/// boundary face reached its receiver; it does not remount that face as ecology ingress or alter
/// the native body.  The next realization order must join it through the returned local phase and
/// factor section already carried by the realization passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorDeliveryReturn {
    pub schema: String,
    pub causal_order: u64,
    pub emission_identity_sha256: String,
    pub delivery_occurrence: String,
    pub morphology_changed: bool,
    pub semantic_ingress_mounted: bool,
    pub joined_causal_order: Option<u64>,
    pub joined_realization_identity_sha256: Option<String>,
    pub identity_sha256: String,
}

/// Exact descent of one occurrence-conditioned diagonal factor current through the resident
/// receiver/history quotient.  Zero coordinates are included, so fibre constancy and every
/// composite generator square are checked over the complete declared factor population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralReturnedCurrentDescent {
    pub schema: String,
    pub returned_native_current_identity_sha256: String,
    pub compression_identity_sha256: String,
    pub source_current: Vec<(u64, BigUint)>,
    pub native_current: Vec<(u64, BigUint)>,
    pub reconstruction_fibre_identity_sha256: String,
    pub fibre_constant: bool,
    pub generator_composite_squares_commute: bool,
    pub every_word_exact_by_induction: bool,
    pub shortest_separator: Option<(u64, u64)>,
    pub identity_sha256: String,
}

/// One rested branch functional from the complete native factor-current carrier into the
/// standing winding carrier.  `coefficients[f]` is derived from the exact dependent receiver
/// fibre at factor `f`, its orientation, and the branch's Complex-Parametron constitutive current.
/// It is never derived from an exterior port, token, question, or factor ordinal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralWindingBranchFunctional {
    pub branch: usize,
    pub thread_address: String,
    pub constitutive_current: ExactComplexWaveCurrent,
    pub constitutive_norm: Rat,
    pub factor_orientations: Vec<i8>,
    pub coefficients: Vec<Rat>,
    pub total_factor_coverage: bool,
    pub orientation_covariant: bool,
    pub identity_sha256: String,
}

/// Exact cross-organ receiver chart `H : F -> W` used by UAR3.  The complete factor carrier is
/// retained beside this chart; `kernel_dimension` describes the receiver directions it cannot
/// distinguish and is not permission to discard their reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralFactorWindingConstitutiveChart {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub relational_identity_sha256: String,
    pub receiver_history_compression_identity_sha256: String,
    pub factor_native_addresses: Vec<NativeStateId>,
    pub factor_capacities: Vec<u64>,
    pub branch_functionals: Vec<SourceNeutralWindingBranchFunctional>,
    pub operator: ExactRatMatrix,
    pub rank: usize,
    pub kernel_dimension: usize,
    pub total_factor_coverage: bool,
    pub orientation_covariant: bool,
    pub receiver_history_fibres_singleton: bool,
    pub q_descent_complete: bool,
    pub complete_factor_reconstruction_fibre_retained: bool,
    pub exterior_occurrence_consulted: bool,
    pub identity_sha256: String,
}

/// One complete situated receiver face of a signed factor-current difference.  The winding
/// covector is a receiver consequence; `factor_difference` remains the complete source fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralWindingDifference {
    pub schema: String,
    pub chart_identity_sha256: String,
    pub factor_difference: Vec<BigInt>,
    pub returned_winding_covector: Vec<Rat>,
    pub receiver_radical: bool,
    pub complete_factor_reconstruction_fibre_retained: bool,
    pub identity_sha256: String,
}

/// Exact UAR3-D1 return joining one published native emission to a separately caused exterior
/// consequence.  The selected carrier occurrence is an orientation-covariant chart anchor; the
/// complete factor difference remains primary and is never replaced by that anchor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralSituatedDifferenceReceipt {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub emission: SourceNeutralExteriorEmission,
    pub exterior_return: SourceNeutralExteriorInferenceReturn,
    pub factor_winding_chart_identity_sha256: String,
    pub candidate_winding_coordinates: Vec<Rat>,
    pub returned_winding_coordinates: Vec<Rat>,
    pub winding_difference: SourceNeutralWindingDifference,
    pub selected_branch: usize,
    pub selected_branch_thread: String,
    pub selected_factor: u32,
    pub selected_factor_native: NativeStateId,
    pub selected_reconstruction_fibre_address: String,
    pub situated_difference: SituatedDifferenceSection,
    pub complete_factor_reconstruction_fibre_retained: bool,
    pub exterior_source_fibre_reachable_from_productive_body: bool,
    pub identity_sha256: String,
}

/// Move-owned return of the same resident parent together with the completed D1 difference.  It
/// interrupts fixed-morphology recurrence at the genuine world-return seam so cultivation can
/// consume the returned difference without privately echoing it through another inference step.
pub struct SourceNeutralExteriorCultivationReturn {
    pub(super) resident: ResidentSourceNeutralEcology,
    pub(super) receipt: SourceNeutralSituatedDifferenceReceipt,
}

pub(super) struct SourceNeutralSituatedDifferenceBody {
    pub(super) candidate_winding_coordinates: Vec<Rat>,
    pub(super) returned_winding_coordinates: Vec<Rat>,
    pub(super) winding_difference: SourceNeutralWindingDifference,
    pub(super) selected_branch: usize,
    pub(super) selected_branch_thread: String,
    pub(super) selected_factor: u32,
    pub(super) selected_factor_native: NativeStateId,
    pub(super) selected_reconstruction_fibre_address: String,
    pub(super) situated_difference: SituatedDifferenceSection,
}

impl SourceNeutralFactorWindingConstitutiveChart {
    pub(super) fn project_factor_current(
        &self,
        factor_current: &[(u32, BigUint)],
    ) -> Result<Vec<Rat>, SourceNeutralEcologyError> {
        let mut dense = vec![BigInt::ZERO; self.factor_native_addresses.len()];
        let mut seen = BTreeSet::new();
        for (factor, coefficient) in factor_current {
            let at = usize::try_from(*factor).map_err(|_| {
                SourceNeutralEcologyError::Body(
                    "a factor current escaped the constitutive chart address".to_owned(),
                )
            })?;
            if at >= dense.len() || !seen.insert(*factor) {
                return Err(SourceNeutralEcologyError::Body(
                    "a factor current is duplicated or outside the constitutive chart".to_owned(),
                ));
            }
            dense[at] = BigInt::from(coefficient.clone());
        }
        self.operator
            .apply(&dense.into_iter().map(Rat::from_integer).collect::<Vec<_>>())
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))
    }

    /// Apply the rested cross-organ chart to one complete signed factor-current difference.
    /// A zero returned covector is retained as an exact receiver-radical occurrence rather than
    /// being confused with absence of source difference or silently discarded.
    pub fn return_difference(
        &self,
        factor_difference: Vec<BigInt>,
    ) -> Result<SourceNeutralWindingDifference, SourceNeutralEcologyError> {
        if self.exterior_occurrence_consulted
            || !self.complete_factor_reconstruction_fibre_retained
            || !self.total_factor_coverage
            || !self.orientation_covariant
            || !self.q_descent_complete
            || self.rank == 0
            || self.operator.rows() != self.branch_functionals.len()
            || self.operator.columns() != self.factor_native_addresses.len()
            || self.factor_capacities.len() != self.factor_native_addresses.len()
            || factor_difference.len() != self.factor_native_addresses.len()
        {
            return Err(SourceNeutralEcologyError::Body(
                "the factor difference does not inhabit the complete rested constitutive chart"
                    .to_owned(),
            ));
        }
        let rational_difference = factor_difference
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect::<Vec<_>>();
        let returned_winding_covector = self
            .operator
            .apply(&rational_difference)
            .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
        let receiver_radical = returned_winding_covector.iter().all(Zero::is_zero);
        let schema = "soma-life.source-neutral-winding-difference.v1".to_owned();
        let identity_sha256 = digest(&(
            schema.as_str(),
            self.identity_sha256.as_str(),
            &factor_difference,
            &returned_winding_covector,
            receiver_radical,
            true,
        ));
        Ok(SourceNeutralWindingDifference {
            schema,
            chart_identity_sha256: self.identity_sha256.clone(),
            factor_difference,
            returned_winding_covector,
            receiver_radical,
            complete_factor_reconstruction_fibre_retained: true,
            identity_sha256,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "terminal", rename_all = "kebab-case")]
pub enum SourceNeutralExteriorRadiationTerminal {
    Closure,
    /// Exterior apparatus has received this emission but intentionally leaves its return seam
    /// open at the declared process boundary.  This is not native closure or recurrence.
    OpenExteriorAperture {
        causal_order: u64,
        pending_emission_identity_sha256: String,
    },
    RecurrentNativeSection {
        first_seen_causal_order: u64,
        continuation_identity_sha256: String,
    },
    PluralReceiverInsufficiency {
        causal_order: u64,
        unresolved_ports: Vec<GranularExteriorPort>,
    },
    /// Every coordinate of the admitted situated receiver section vanished.  This is an exact
    /// kernel occurrence, not another zero current which can lawfully found a resident word.
    ReceiverRadical {
        causal_order: u64,
        unresolved_higher_faces: Vec<GranularAddressedHigherBoundaryFace>,
    },
}

/// Downstream output-codec passage. Both maps are explicit: each causal order names its native
/// fine section, and every emitted octet position names the order/port which produced it. The
/// source corpus and cold ingress witness are outside this type and outside its dependency path.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorCodecPassage {
    pub schema: String,
    pub codec_identity_sha256: String,
    pub rest_identity_sha256: String,
    pub ingress_current_identity_sha256: String,
    pub orders: Vec<SourceNeutralExteriorCodecOrder>,
    pub emitted_octets: Vec<u8>,
    pub exterior_utf8: Option<String>,
    pub complete_native_sections_retained: bool,
    pub fine_to_exterior_boundary_total: bool,
    pub exterior_to_fine_boundary_exact: bool,
    pub source_codec_consulted: bool,
    pub source_utterance_reachable: bool,
    pub source_witness_reachable: bool,
    pub identity_sha256: String,
}

/// Complete UAR2 recurrence: native fine sections remain primary; the byte/glyph surface is a
/// cold receiver face returned only after native closure or an explicit insufficiency/recurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorRadiation {
    pub schema: String,
    pub native_sections: Vec<SourceNeutralResidentRadiationSection>,
    pub resident_receiver_history: ResidentReceiverHistoryCompressionReceipt,
    pub receiver_history: SourceNeutralContinuationReceiverHistory,
    pub inference_returns: Vec<SourceNeutralExteriorInferenceReturn>,
    pub delivery_returns: Vec<SourceNeutralExteriorDeliveryReturn>,
    pub codec_passage: SourceNeutralExteriorCodecPassage,
    pub terminal: SourceNeutralExteriorRadiationTerminal,
    pub identity_sha256: String,
}

/// One exterior realization which has left the resident ecology deed.  The complete continuation
/// is held by [`SourceNeutralPendingExteriorEmission`]; no following native step is callable until
/// a separately caused return consumes that seam.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralExteriorEmission {
    pub schema: String,
    pub causal_order: u64,
    pub occurrence: String,
    pub native_section_identity_sha256: String,
    pub port: GranularExteriorPort,
    pub emitted_octet_position: Option<u64>,
    pub identity_sha256: String,
}

/// The one move-owned fixed-morphology circulation.  Native continuation state is not cloneable
/// or externally addressable: it can advance only by emitting one face or by consuming the exact
/// pending exterior-return seam.
pub struct SourceNeutralExteriorCirculation {
    pub(super) resident: ResidentSourceNeutralEcology,
    pub(super) ingress_current_identity_sha256: String,
    pub(super) emanation: GranularBoundaryEmanation,
    pub(super) crossed_structural_ports: Vec<GranularExteriorPort>,
    pub(super) continuation_path: Vec<SourceNeutralContinuationState>,
    pub(super) native_sections: Vec<SourceNeutralResidentRadiationSection>,
    pub(super) orders: Vec<SourceNeutralExteriorCodecOrder>,
    pub(super) emitted_octets: Vec<u8>,
    pub(super) inference_returns: Vec<SourceNeutralExteriorInferenceReturn>,
    pub(super) delivery_returns: Vec<SourceNeutralExteriorDeliveryReturn>,
    pub(super) causal_order: u64,
    pub(super) resident_source: Option<ResidentCurrentAddress>,
    pub(super) current_projective: GranularNativeProjectiveCurrent,
    pub(super) presented_current: Option<Vec<(u32, BigUint)>>,
    pub(super) realization_current_identity_sha256: String,
    pub(super) realization_current: BigUint,
    pub(super) active_realization: Option<SourceNeutralExteriorRealizationPassage>,
    pub(super) realization_target_current_address: Option<ResidentCurrentAddress>,
}

/// A realized exterior face with exclusive ownership of its held native successor.  Exterior
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralContinuationReceiverHistory {
    pub compression: ReceiverHistoryCompression,
    pub ordered_word: OrderedWordConsequence,
    pub complete_state_population: usize,
    pub recurrence_generator: InputId,
    pub structural_equality_used: bool,
    pub digest_equality_used: bool,
}

/// Complete apparatus-neutral continuation state. Resident buffer addresses, device identity,
/// launch chronology and digests do not enter equality. The complete C0 passage, receiver fronts,
/// projective consequences and reconstruction DAG do.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct SourceNeutralContinuationState {
    /// Primitive integral ray of the complete homogeneous native receiver section. Generation,
    /// allocation identity, and positive common magnitude remain reconstruction testimony rather
    /// than equality coordinates; opposite orientation remains distinct.
    pub(super) canonical_receiver_section: Vec<BigInt>,
    /// Complete native successor support with both addressed boundary maps.  Rank-one source
    /// decompositions remain in `reconstruction_dag`; they are not hot state coordinates.
    pub(super) complete_successor_addressed_faces: Vec<GranularAddressedHigherBoundaryFace>,
    /// Projective compatibility faces remain typed pairs.  A radical `(0,0)` is not identified
    /// with an orthogonal nonradical `(0,n)`, and no undefined `0/0` scalar is manufactured.
    pub(super) situated_projective_faces: Vec<SourceNeutralProjectiveCompatibility>,
    /// Phase-insensitive modulus shadow of the relational complex pairing.
    pub(super) relational_projective_faces: Vec<SourceNeutralRelationalProjectiveCompatibility>,
    /// Complete pre-locking oriented relational section retained beside that shadow.
    pub(super) relational_oriented_pairings: Vec<SourceNeutralOrientedRelationalPairing>,
    pub(super) phase_front_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub(super) situated_receiver_higher_faces: Vec<GranularHigherBoundaryFace>,
    pub(super) downstream_port_projection: Vec<GranularExteriorPort>,
    /// Complete exterior target-current section returned from the native body before one Dirac
    /// realization meets it.  It participates in continuation equality; the selected surface
    /// alone never does.
    pub(super) exterior_realization_target_current: Vec<(u16, num_rational::Ratio<BigUint>)>,
    pub(super) exterior_realization_continuing_target_current:
        Vec<(u16, num_rational::Ratio<BigUint>)>,
    /// Selected dependent complex section and its complete addressed response/source/target
    /// fibre. These coordinates prevent equal positive shadows with distinct quadrature from
    /// becoming one recurrent state.
    pub(super) returned_complex_realization_section:
        Vec<SourceNeutralExteriorRealizationComplexSiteCurrent>,
    pub(super) returned_complex_realization_contributions:
        Vec<SourceNeutralExteriorRealizationTransportContribution>,
    pub(super) realization_transport_obstructions:
        Vec<SourceNeutralExteriorRealizationTransportObstruction>,
    pub(super) returned_complex_response_factor_currents:
        Vec<SourceNeutralExteriorRealizationOrientedFactorCurrent>,
    pub(super) reconstruction_dag: Vec<GranularReconstructionNode>,
    pub(super) local_balance_closes: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct SourceNeutralProjectiveCompatibility {
    pub(super) sign: i8,
    pub(super) squared_numerator: BigUint,
    pub(super) denominator: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct SourceNeutralRelationalProjectiveCompatibility {
    pub(super) modulus_squared_numerator: BigUint,
    pub(super) denominator: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) struct SourceNeutralOrientedRelationalPairing {
    pub(super) real: BigInt,
    pub(super) imaginary: BigInt,
    pub(super) target_self_pairing: BigUint,
    pub(super) current_self_pairing: BigUint,
}

impl SourceNeutralProjectiveCompatibility {
    pub(super) fn found(coordinate: &BigInt, denominator: &BigUint) -> Self {
        let mut squared_numerator = coordinate.magnitude() * coordinate.magnitude();
        let mut denominator = denominator.clone();
        if !squared_numerator.is_zero() && !denominator.is_zero() {
            let mut left = squared_numerator.clone();
            let mut right = denominator.clone();
            while !right.is_zero() {
                let remainder = &left % &right;
                left = right;
                right = remainder;
            }
            let divisor = left;
            squared_numerator /= &divisor;
            denominator /= divisor;
        } else if squared_numerator.is_zero() && !denominator.is_zero() {
            // Every nonradical zero compatibility belongs to the same exact projective zero.
            denominator = BigUint::from(1_u8);
        }
        Self {
            sign: if coordinate.is_zero() {
                0
            } else if coordinate.sign() == num_bigint::Sign::Minus {
                -1
            } else {
                1
            },
            squared_numerator,
            denominator,
        }
    }
}

impl SourceNeutralRelationalProjectiveCompatibility {
    pub(super) fn found(modulus_squared_numerator: &BigUint, denominator: &BigUint) -> Self {
        let mut modulus_squared_numerator = modulus_squared_numerator.clone();
        let mut denominator = denominator.clone();
        if !modulus_squared_numerator.is_zero() && !denominator.is_zero() {
            let mut left = modulus_squared_numerator.clone();
            let mut right = denominator.clone();
            while !right.is_zero() {
                let remainder = &left % &right;
                left = right;
                right = remainder;
            }
            modulus_squared_numerator /= &left;
            denominator /= left;
        } else if modulus_squared_numerator.is_zero() && !denominator.is_zero() {
            denominator = BigUint::from(1_u8);
        }
        Self {
            modulus_squared_numerator,
            denominator,
        }
    }
}

impl SourceNeutralContinuationState {
    pub(super) fn from_section(
        section: &SourceNeutralResidentRadiationSection,
        realization: &SourceNeutralExteriorRealizationPassage,
    ) -> Result<Self, SourceNeutralEcologyError> {
        let downstream_port_projection = section
            .situated_receiver_higher_faces
            .iter()
            .map(|face| face.port.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let situated = section.radiation.situated_receiver_pairing.as_ref();
        let projective_faces = |coordinates: &[BigInt], denominators: &[BigUint]| {
            coordinates
                .iter()
                .zip(denominators)
                .map(|(coordinate, denominator)| {
                    SourceNeutralProjectiveCompatibility::found(coordinate, denominator)
                })
                .collect::<Vec<_>>()
        };
        let situated_projective_faces = situated
            .filter(|pairing| pairing.coordinates.len() == pairing.squared_norm_products.len())
            .map(|pairing| projective_faces(&pairing.coordinates, &pairing.squared_norm_products))
            .unwrap_or_default();
        let relational_projective_faces = situated
            .filter(|pairing| {
                pairing.relational_modulus_squared_coordinates.len()
                    == pairing.relational_squared_norm_products.len()
            })
            .map(|pairing| {
                pairing
                    .relational_modulus_squared_coordinates
                    .iter()
                    .zip(&pairing.relational_squared_norm_products)
                    .map(|(numerator, denominator)| {
                        SourceNeutralRelationalProjectiveCompatibility::found(
                            numerator,
                            denominator,
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let relational_oriented_pairings = situated
            .filter(|pairing| {
                let population = pairing.relational_oriented_real_coordinates.len();
                population == pairing.relational_oriented_imaginary_coordinates.len()
                    && population == pairing.relational_target_self_pairings.len()
                    && population == pairing.relational_current_self_pairings.len()
            })
            .map(|pairing| {
                pairing
                    .relational_oriented_real_coordinates
                    .iter()
                    .zip(&pairing.relational_oriented_imaginary_coordinates)
                    .zip(&pairing.relational_target_self_pairings)
                    .zip(&pairing.relational_current_self_pairings)
                    .map(
                        |(((real, imaginary), target_self_pairing), current_self_pairing)| {
                            SourceNeutralOrientedRelationalPairing {
                                real: real.clone(),
                                imaginary: imaginary.clone(),
                                target_self_pairing: target_self_pairing.clone(),
                                current_self_pairing: current_self_pairing.clone(),
                            }
                        },
                    )
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        Ok(Self {
            canonical_receiver_section: canonical_positive_projective_resident_receiver_section(
                section,
            )?,
            complete_successor_addressed_faces: section.complete_successor_addressed_faces.clone(),
            situated_projective_faces,
            relational_projective_faces,
            relational_oriented_pairings,
            phase_front_higher_faces: section.phase_front_higher_faces.clone(),
            situated_receiver_higher_faces: section.situated_receiver_higher_faces.clone(),
            downstream_port_projection,
            exterior_realization_target_current: realization
                .target_current
                .iter()
                .map(|target| (target.target_port, target.current.clone()))
                .collect(),
            exterior_realization_continuing_target_current: realization
                .continuing_target_current
                .iter()
                .map(|target| (target.target_port, target.current.clone()))
                .collect(),
            returned_complex_realization_section: realization.returned_complex_site_current.clone(),
            returned_complex_realization_contributions: realization
                .transport_contributions
                .iter()
                .filter(|contribution| {
                    contribution.exterior_target_port == realization.selected_target_port
                })
                .cloned()
                .collect(),
            realization_transport_obstructions: realization.transport_obstructions.clone(),
            returned_complex_response_factor_currents: realization.oriented_factor_current.clone(),
            reconstruction_dag: section.reconstruction_dag.clone(),
            local_balance_closes: section.radiation.local_balance_closes,
        })
    }
}

pub(super) struct SourceNeutralContinuationSystem {
    pub(super) items: Vec<ItemId>,
    pub(super) receivers: Vec<ReceiverId>,
    pub(super) observations: Vec<Vec<Observation>>,
    pub(super) successors: Vec<ItemId>,
    pub(super) recurrence_generator: InputId,
}

/// Query-independent apparatus view of the complete rested factor action. It exists only long
/// enough to found the one exact receiver/history compression during card mount; exterior
/// occurrences cannot alter its items, receivers, inputs, observations, or successors.
pub(super) struct SourceNeutralFactorReceiverHistorySystem {
    pub(super) items: Vec<ItemId>,
    pub(super) receivers: Vec<ReceiverId>,
    pub(super) inputs: Vec<InputId>,
    pub(super) observations: Vec<u64>,
    pub(super) successors: Vec<Vec<u32>>,
}

impl ObservedSystem for SourceNeutralFactorReceiverHistorySystem {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.receivers.clone()
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let item = item.0 as usize;
        let receiver = self
            .receivers
            .iter()
            .position(|candidate| *candidate == receiver)
            .expect("validated rested receiver address");
        Observation(self.observations[item * self.receivers.len() + receiver])
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let generator = self
            .inputs
            .iter()
            .position(|candidate| *candidate == input)?;
        self.successors
            .get(generator)
            .and_then(|targets| targets.get(item.0 as usize))
            .copied()
            .map(|target| ItemId(u64::from(target)))
    }

    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        let generator = self
            .inputs
            .iter()
            .position(|candidate| *candidate == input)?;
        Some(
            self.successors[generator]
                .iter()
                .copied()
                .enumerate()
                .map(|(source, target)| (ItemId(source as u64), ItemId(u64::from(target))))
                .collect(),
        )
    }
}

impl ObservedSystem for SourceNeutralContinuationSystem {
    fn items(&self) -> Vec<ItemId> {
        self.items.clone()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.receivers.clone()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![self.recurrence_generator]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.observations[item.0 as usize][receiver.0 as usize]
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        (input == self.recurrence_generator)
            .then(|| self.successors.get(item.0 as usize).copied())
            .flatten()
    }
}

pub(super) fn exact_receiver_classes<T: Eq>(
    states: &[SourceNeutralContinuationState],
    face: impl Fn(&SourceNeutralContinuationState) -> &T,
) -> Result<Vec<Observation>, SourceNeutralEcologyError> {
    let mut representatives = Vec::<usize>::new();
    states
        .iter()
        .enumerate()
        .map(|(at, state)| {
            let class = representatives
                .iter()
                .position(|representative| face(&states[*representative]) == face(state))
                .unwrap_or_else(|| {
                    representatives.push(at);
                    representatives.len() - 1
                });
            u64::try_from(class).map(Observation).map_err(|_| {
                SourceNeutralEcologyError::Body(
                    "the continuation receiver population exceeded its address".to_owned(),
                )
            })
        })
        .collect()
}

pub(super) fn found_continuation_receiver_history(
    path: &[SourceNeutralContinuationState],
) -> Result<SourceNeutralContinuationReceiverHistory, SourceNeutralEcologyError> {
    if path.is_empty() {
        return Err(SourceNeutralEcologyError::Body(
            "the complete native continuation path is empty".to_owned(),
        ));
    }
    let mut states = Vec::<SourceNeutralContinuationState>::new();
    let mut path_items = Vec::<ItemId>::with_capacity(path.len());
    for state in path {
        let at = states
            .iter()
            .position(|existing| existing == state)
            .unwrap_or_else(|| {
                states.push(state.clone());
                states.len() - 1
            });
        path_items.push(ItemId(u64::try_from(at).map_err(|_| {
            SourceNeutralEcologyError::Body(
                "the continuation state population exceeded its address".to_owned(),
            )
        })?));
    }
    let items = (0..states.len())
        .map(|at| {
            u64::try_from(at).map(ItemId).map_err(|_| {
                SourceNeutralEcologyError::Body(
                    "the continuation state population exceeded its address".to_owned(),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut successors = items.clone();
    let mut assigned = vec![false; states.len()];
    for edge in path_items.windows(2) {
        let from = edge[0].0 as usize;
        if assigned[from] && successors[from] != edge[1] {
            return Err(SourceNeutralEcologyError::Body(
                "one complete continuation state returned plural successors under one admitted current"
                    .to_owned(),
            ));
        }
        successors[from] = edge[1];
        assigned[from] = true;
    }

    let receiver_columns = [
        exact_receiver_classes(&states, |state| &state.canonical_receiver_section)?,
        exact_receiver_classes(&states, |state| &state.complete_successor_addressed_faces)?,
        exact_receiver_classes(&states, |state| &state.phase_front_higher_faces)?,
        exact_receiver_classes(&states, |state| &state.situated_receiver_higher_faces)?,
        exact_receiver_classes(&states, |state| &state.situated_projective_faces)?,
        exact_receiver_classes(&states, |state| &state.relational_projective_faces)?,
        exact_receiver_classes(&states, |state| &state.downstream_port_projection)?,
        exact_receiver_classes(&states, |state| &state.exterior_realization_target_current)?,
        exact_receiver_classes(&states, |state| {
            &state.exterior_realization_continuing_target_current
        })?,
        exact_receiver_classes(&states, |state| &state.returned_complex_realization_section)?,
        exact_receiver_classes(&states, |state| {
            &state.returned_complex_realization_contributions
        })?,
        exact_receiver_classes(&states, |state| &state.realization_transport_obstructions)?,
        exact_receiver_classes(&states, |state| {
            &state.returned_complex_response_factor_currents
        })?,
        exact_receiver_classes(&states, |state| &state.reconstruction_dag)?,
        exact_receiver_classes(&states, |state| &state.local_balance_closes)?,
    ];
    let receivers = (0..receiver_columns.len())
        .map(|at| ReceiverId(at as u64))
        .collect::<Vec<_>>();
    let observations = (0..states.len())
        .map(|state| {
            receiver_columns
                .iter()
                .map(|column| column[state])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let recurrence_generator = InputId(0);
    let system = SourceNeutralContinuationSystem {
        items,
        receivers,
        observations,
        successors,
        recurrence_generator,
    };
    let exact = compress(&system);
    let compression = ReceiverHistoryCompression::found(&system, &exact)
        .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
    let ordered_word = compression
        .ordered_word_consequence(path_items[0], &[recurrence_generator, recurrence_generator])
        .map_err(|error| SourceNeutralEcologyError::Body(error.to_string()))?;
    if !ordered_word.commutes() {
        return Err(SourceNeutralEcologyError::Body(
            "the complete continuation ordered-word square did not commute".to_owned(),
        ));
    }
    Ok(SourceNeutralContinuationReceiverHistory {
        complete_state_population: states.len(),
        compression,
        ordered_word,
        recurrence_generator,
        structural_equality_used: true,
        digest_equality_used: false,
    })
}

#[cfg(test)]
mod continuation_tests {
    use super::*;
    use crate::native_intelligence::SourceNeutralAddressedResponsePairCurrent;

    fn state_with_pair(current: ExactComplexWaveCurrent) -> SourceNeutralContinuationState {
        SourceNeutralContinuationState {
            canonical_receiver_section: vec![BigInt::from(1)],
            complete_successor_addressed_faces: Vec::new(),
            situated_projective_faces: Vec::new(),
            relational_projective_faces: Vec::new(),
            relational_oriented_pairings: Vec::new(),
            phase_front_higher_faces: Vec::new(),
            situated_receiver_higher_faces: Vec::new(),
            downstream_port_projection: Vec::new(),
            exterior_realization_target_current: vec![(
                3,
                num_rational::Ratio::from_integer(BigUint::from(1_u8)),
            )],
            exterior_realization_continuing_target_current: vec![(
                3,
                num_rational::Ratio::from_integer(BigUint::from(1_u8)),
            )],
            returned_complex_realization_section: Vec::new(),
            returned_complex_realization_contributions: vec![
                SourceNeutralExteriorRealizationTransportContribution {
                    exterior_target_port: 3,
                    source_carrier: 0,
                    source_site: 0,
                    source_local_port: 0,
                    source_realization_state: 0,
                    target_carrier: 1,
                    target_site: 1,
                    target_local_source_port: 3,
                    target_realization_state: Some(0),
                    factor: 0,
                    phase: 0,
                    incidence_coefficient: num_rational::Ratio::from_integer(BigUint::from(1_u8)),
                },
            ],
            realization_transport_obstructions: Vec::new(),
            returned_complex_response_factor_currents: vec![
                SourceNeutralExteriorRealizationOrientedFactorCurrent {
                    factor: 0,
                    current: current.clone(),
                    pair_currents: vec![SourceNeutralAddressedResponsePairCurrent {
                        response_face: 0,
                        native_port: 0,
                        native_generator: 0,
                        source_section: 0,
                        selected_slot: 0,
                        target_section: 0,
                        factor: 0,
                        current,
                    }],
                },
            ],
            reconstruction_dag: Vec::new(),
            local_balance_closes: true,
        }
    }

    #[test]
    fn equal_positive_shadow_with_distinct_quadrature_does_not_recur() {
        let real = state_with_pair(ExactComplexWaveCurrent::one());
        let imaginary = state_with_pair(ExactComplexWaveCurrent::new(
            Rat::zero(),
            Rat::from_integer(BigInt::from(1)),
        ));
        assert_eq!(
            real.returned_complex_response_factor_currents[0]
                .current
                .norm_square(),
            imaginary.returned_complex_response_factor_currents[0]
                .current
                .norm_square()
        );
        assert_ne!(real, imaginary);
        let classes = exact_receiver_classes(&[real, imaginary], |state| {
            &state.returned_complex_response_factor_currents
        })
        .expect("the full complex receiver separates the pair");
        assert_ne!(classes[0], classes[1]);
    }
}
