//! One resident Athena-alpha product aperture over the complete cultivated organ body.
//!
//! The optical, acoustic, granular, recurrent-return, affine, participant, and material
//! morphologies remain one move-owned rest while the coupled, affine, and participant fronts share
//! one CUDA context.  The nested type-state is ownership lineage, not a serialized inference
//! schedule: no organ is withdrawn to make another conductible.

use holonic_engine::{
    cuda_refine::{
        CudaRefineExecutor, ResidentIntegratedFront, ResidentSituatedCurrentCausalFrontReturn,
    },
    AddressedCurrentSection,
};
use num_bigint::BigUint;
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::laboratory_cultivation::{
    project_participant_emanation, render_returned_cells, render_returned_participant_cells,
};
use super::native_relational_potential::NativeDeliveryPhase;
use super::situated_cultivation::derive_recurrent_resident_coupling;
use super::{
    EmanationDeed, GranularExteriorProjectiveCurrent, LaboratoryCultivationError,
    LaboratoryParticipantEmanation, LaboratoryParticipantIngress, MaterialAffineTransportReceipt,
    MaterialFactorizationStanding, MaterialIntegratedResidentApparatusReceipt,
    MaterialNativeFactorization, OpticalProductRest, SituatedCultivatedConductReturn,
};

/// One addressed join between a returned technical section and the cultivated participant/history
/// section carried by the same Athena rest.  The joined cold surface is downstream testimony; the
/// shared affine cells are the actual incidence witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProductTechnicalHistoryEmanation {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub technical_occurrence: String,
    pub participant_ingress_occurrence: String,
    pub technical_current_identity_sha256: String,
    pub history_successor_identity_sha256: String,
    pub technical_factor_support: Vec<u32>,
    pub shared_factor_support: Vec<u32>,
    pub shared_affine_cell_addresses: Vec<String>,
    pub history_phase_class_populations: Vec<(String, Vec<usize>)>,
    pub technical_section_reconstruction_fibre: Vec<String>,
    pub history_unjoined_cell_reconstruction_fibre: Vec<String>,
    pub history_hidden_cell_reconstruction_fibre: Vec<String>,
    pub history_surface_sha256: String,
    pub joined_surface: String,
    pub joined_surface_sha256: String,
    pub identity_sha256: String,
}

/// One fine exterior current returned through the complete cultivated cell field of the resident
/// Athena product.  The full cell-by-context overlap holon remains in `apparatus`; `surface` is a
/// cold rendering of exactly the non-dominated native cell front it returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProductSituatedCurrentEmanation {
    pub schema: String,
    pub rest_identity_sha256: String,
    pub exterior_occurrence: String,
    pub exterior_current_identity_sha256: String,
    pub participant_aperture: bool,
    pub deed: EmanationDeed,
    pub perspective_surface: Option<String>,
    pub selected_cell_addresses: Vec<String>,
    pub selected_affine_sections: Vec<super::LaboratoryCellAffineSection>,
    pub hidden_cell_reconstruction_fibre: Vec<String>,
    pub surface: String,
    pub surface_sha256: String,
    pub identity_sha256: String,
    pub apparatus: ResidentSituatedCurrentCausalFrontReturn,
}

impl ProductTechnicalHistoryEmanation {
    /// Glue a fine-grained technical recurrence to an already returned participant section only
    /// through literal shared native factor incidence. No exterior word, string equality, or
    /// displayed answer can found the join.
    fn found(
        rest: &OpticalProductRest,
        technical: &GranularExteriorProjectiveCurrent,
        history: &LaboratoryParticipantEmanation,
    ) -> Result<Self, LaboratoryCultivationError> {
        if rest.identity() != history.rest_identity_sha256
            || history.selected_cell_addresses.len() != history.selected_affine_sections.len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the technical and history sections do not descend from one Athena rest".to_owned(),
            ));
        }
        let technical_factor_support = technical
            .contexts
            .iter()
            .flat_map(|context| {
                context
                    .factor_current
                    .iter()
                    .map(|coordinate| coordinate.factor)
            })
            .collect::<std::collections::BTreeSet<_>>();
        if technical_factor_support.is_empty() {
            return Err(LaboratoryCultivationError::Correspondence(
                "the technical recurrence returned no native factor current".to_owned(),
            ));
        }
        let mut shared_affine_cell_addresses = Vec::new();
        let mut shared_factor_support = std::collections::BTreeSet::new();
        let mut history_unjoined_cell_reconstruction_fibre = Vec::new();
        let mut history_phase_class_populations = Vec::new();
        for (address, section) in history
            .selected_cell_addresses
            .iter()
            .zip(&history.selected_affine_sections)
        {
            if address != &section.cell_address {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a participant cell escaped its cultivated affine section".to_owned(),
                ));
            }
            if section.landmark_factors.len() != section.occurrence_multiplicities.len() {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a cultivated affine cell lost its factor/multiplicity incidence".to_owned(),
                ));
            }
            let intersection = section
                .landmark_factors
                .iter()
                .copied()
                .filter(|factor| technical_factor_support.contains(factor))
                .collect::<Vec<_>>();
            let cell_current = section
                .landmark_factors
                .iter()
                .copied()
                .zip(section.occurrence_multiplicities.iter().copied())
                .collect::<std::collections::BTreeMap<_, _>>();
            let restrictions = technical
                .contexts
                .iter()
                .map(|context| {
                    context
                        .factor_current
                        .iter()
                        .filter_map(|coordinate| {
                            cell_current.get(&coordinate.factor).map(|multiplicity| {
                                (
                                    coordinate.factor,
                                    &coordinate.incidence * BigUint::from(*multiplicity),
                                )
                            })
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let mut phase_classes = Vec::<(Vec<(u32, BigUint)>, usize)>::new();
            for restriction in restrictions
                .into_iter()
                .filter(|section| !section.is_empty())
            {
                if let Some((_, population)) = phase_classes
                    .iter_mut()
                    .find(|(representative, _)| projectively_equal(representative, &restriction))
                {
                    *population += 1;
                } else {
                    phase_classes.push((restriction, 1));
                }
            }
            let mut phase_populations = phase_classes
                .iter()
                .map(|(_, population)| *population)
                .collect::<Vec<_>>();
            phase_populations.sort_unstable_by(|left, right| right.cmp(left));
            let recurrent_phase_present =
                phase_populations.iter().any(|population| *population > 1);
            history_phase_class_populations.push((address.clone(), phase_populations));
            if intersection.is_empty() || !recurrent_phase_present {
                history_unjoined_cell_reconstruction_fibre.push(address.clone());
            } else {
                shared_affine_cell_addresses.push(address.clone());
                shared_factor_support.extend(intersection);
            }
        }
        shared_affine_cell_addresses.sort();
        shared_affine_cell_addresses.dedup();
        if shared_affine_cell_addresses.is_empty() || shared_factor_support.is_empty() {
            return Err(LaboratoryCultivationError::Correspondence(
                "co-present technical and history sections have no native incidence join"
                    .to_owned(),
            ));
        }
        let technical_section_reconstruction_fibre = technical
            .quadratic_population_reopens_from_source_fibre
            .then(|| {
                vec![
                    format!(
                        "granular-potential/{}",
                        technical.standing_potential_identity_sha256
                    ),
                    format!("exterior-source/{}", technical.exterior_source_sha256),
                ]
            })
            .unwrap_or_default();
        let joined_history_surface = render_returned_participant_cells(
            rest.body().body().body().relational_potential(),
            rest.body().body().body().relational_codec(),
            &shared_affine_cell_addresses,
            &history.perspective_surface,
        )?;
        let joined_surface = joined_history_surface.clone();
        let joined_surface_sha256 = render_digest(joined_surface.as_bytes());
        let technical_factor_support = technical_factor_support.into_iter().collect::<Vec<_>>();
        let shared_factor_support = shared_factor_support.into_iter().collect::<Vec<_>>();
        let identity_sha256 = render_digest(
            &serde_json::to_vec(&(
                "soma-life.product-technical-history-emanation.v2",
                &history.rest_identity_sha256,
                &technical.exterior_occurrence,
                &history.ingress_occurrence,
                &technical.identity_sha256,
                &history.native_successor_identity_sha256,
                &technical_factor_support,
                &shared_factor_support,
                &shared_affine_cell_addresses,
                &history_phase_class_populations,
                &technical_section_reconstruction_fibre,
                &history_unjoined_cell_reconstruction_fibre,
                &history.hidden_participant_cell_fibre,
                &joined_surface_sha256,
            ))
            .map_err(|error| LaboratoryCultivationError::Correspondence(error.to_string()))?,
        );
        Ok(Self {
            schema: "soma-life.product-technical-history-emanation.v2".to_owned(),
            rest_identity_sha256: history.rest_identity_sha256.clone(),
            technical_occurrence: technical.exterior_occurrence.clone(),
            participant_ingress_occurrence: history.ingress_occurrence.clone(),
            technical_current_identity_sha256: technical.identity_sha256.clone(),
            history_successor_identity_sha256: history.native_successor_identity_sha256.clone(),
            technical_factor_support,
            shared_factor_support,
            shared_affine_cell_addresses,
            history_phase_class_populations,
            technical_section_reconstruction_fibre,
            history_unjoined_cell_reconstruction_fibre,
            history_hidden_cell_reconstruction_fibre: history.hidden_participant_cell_fibre.clone(),
            history_surface_sha256: render_digest(joined_history_surface.as_bytes()),
            joined_surface,
            joined_surface_sha256,
            identity_sha256,
        })
    }
}

fn render_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn projectively_equal(left: &[(u32, BigUint)], right: &[(u32, BigUint)]) -> bool {
    if left.len() != right.len() || left.is_empty() {
        return false;
    }
    let left_pivot = &left[0].1;
    let right_pivot = &right[0].1;
    left.iter()
        .zip(right)
        .all(|((left_factor, left_value), (right_factor, right_value))| {
            left_factor == right_factor && left_value * right_pivot == right_value * left_pivot
        })
}

/// The complete Athena-alpha rest under one card-owned product aperture.
pub struct ResidentProductEcology {
    rest: OpticalProductRest,
    factors: Vec<(String, Vec<String>)>,
    expected: Vec<holonic_engine::ExactComplexWaveCurrent>,
    resident: ResidentIntegratedFront,
}

impl OpticalProductRest {
    /// Mount every currently admitted organ without withdrawing or duplicating any nested owner.
    pub fn mount_product(self) -> Result<ResidentProductEcology, LaboratoryCultivationError> {
        self.validate()
            .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let core = self.body().body().body();
        let potential = core.relational_potential();
        let affine_cells = core.affine_cells();
        let participant_faces = potential
            .addressed_participant_subject_faces()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let mut participant_subject = Vec::with_capacity(potential.cells.len());
        let mut copular = Vec::with_capacity(potential.cells.len());
        let mut has_modality = Vec::with_capacity(potential.cells.len());
        let mut has_return = Vec::with_capacity(potential.cells.len());
        let mut landmark_support = Vec::with_capacity(potential.cells.len());
        let mut occurrence_mass = Vec::with_capacity(potential.cells.len());
        let mut last_occurrence = Vec::with_capacity(potential.cells.len());
        for cell in &potential.cells {
            participant_subject.push(u8::from(participant_faces.contains(&cell.subject)));
            copular.push(u8::from(cell.copular));
            has_modality.push(u8::from(cell.modality.is_some()));
            has_return.push(u8::from(
                cell.occurrences
                    .iter()
                    .any(|occurrence| occurrence.phase == NativeDeliveryPhase::Return),
            ));
            landmark_support.push(u32::try_from(cell.factor_support.len()).map_err(|_| {
                LaboratoryCultivationError::Correspondence(
                    "a product participant support escaped the card address line".to_owned(),
                )
            })?);
            occurrence_mass.push(
                cell.occurrence_population()
                    .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            );
            last_occurrence.push(cell.last_delivery_order().ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "a product participant cell lost its causal chronology".to_owned(),
                )
            })?);
        }

        let mut cell_offsets = Vec::with_capacity(affine_cells.len() + 1);
        let mut cell_factors = Vec::new();
        let mut multiplicities = Vec::new();
        let mut cell_total_mass = Vec::with_capacity(affine_cells.len());
        cell_offsets.push(0u64);
        for cell in affine_cells {
            if cell.landmark_factors.len() != cell.occurrence_multiplicities.len() {
                return Err(LaboratoryCultivationError::Correspondence(
                    "a product affine cell lost its factor/multiplicity incidence".to_owned(),
                ));
            }
            let total = cell
                .occurrence_multiplicities
                .iter()
                .try_fold(0u64, |sum, mass| sum.checked_add(*mass))
                .ok_or_else(|| {
                    LaboratoryCultivationError::Correspondence(
                        "the product affine mass overflowed".to_owned(),
                    )
                })?;
            cell_factors.extend(cell.landmark_factors.iter().copied());
            multiplicities.extend(cell.occurrence_multiplicities.iter().copied());
            cell_total_mass.push(total);
            cell_offsets.push(u64::try_from(multiplicities.len()).map_err(|_| {
                LaboratoryCultivationError::Correspondence(
                    "the product affine support escaped the resident offset chart".to_owned(),
                )
            })?);
        }

        let (incidence, front, interactions, factors, expected) =
            derive_recurrent_resident_coupling(core.body())
                .map_err(|error| LaboratoryCultivationError::Situated(error.to_string()))?;
        let resident = ResidentIntegratedFront::mount(
            CudaRefineExecutor::new()
                .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?,
            format!("native-product/{}", self.identity()),
            incidence,
            front,
            interactions,
            &participant_subject,
            &copular,
            &has_modality,
            &has_return,
            &landmark_support,
            &occurrence_mass,
            &last_occurrence,
            &cell_offsets,
            &cell_factors,
            &multiplicities,
            &cell_total_mass,
        )
        .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        Ok(ResidentProductEcology {
            rest: self,
            factors,
            expected,
            resident,
        })
    }
}

impl MaterialFactorizationStanding for OpticalProductRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[super::SituatedCultivationBranch] {
        self.body().body().body().body().branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body().body().body().body().ecology()
    }

    fn material_standing_realization(&self) -> &super::ReceiverHistoryRealizationPassage {
        self.body().body().body().body().realization()
    }

    fn material_affine_transport(
        &self,
        entering_section: &[i64],
    ) -> Result<Option<MaterialAffineTransportReceipt>, String> {
        let core = self.body().body().body();
        let Some(inner) = core.material_affine_transport(entering_section)? else {
            return Ok(None);
        };
        MaterialAffineTransportReceipt::found(
            self.identity().to_owned(),
            entering_section.to_vec(),
            inner.addressed_landmark_population,
            inner.cell_sections,
        )
        .map(Some)
        .map_err(|error| error.to_string())
    }
}

impl ResidentProductEcology {
    /// Return the complete cultivated participant/history section while every admitted organ
    /// remains inside this product owner. The proper-name face is applied only after the resident
    /// participant current has returned its full native cell population.
    pub fn emanate_participant(
        &mut self,
        ingress: LaboratoryParticipantIngress,
    ) -> Result<LaboratoryParticipantEmanation, LaboratoryCultivationError> {
        let deed = match ingress.deed {
            EmanationDeed::Describe => 0,
            EmanationDeed::Identify => 1,
            EmanationDeed::Infer => 2,
            _ => {
                return Err(LaboratoryCultivationError::Correspondence(
                    "the resident participant receiver admits describe, identify, and infer deeds"
                        .to_owned(),
                ));
            }
        };
        let apparatus = self
            .resident
            .conduct_participant(deed)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let affine = self.rest.body().body().body();
        let participant_faces = affine
            .relational_potential()
            .addressed_participant_subject_faces()
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        project_participant_emanation(
            self.rest.identity(),
            affine.relational_potential(),
            affine.relational_codec(),
            affine.affine_cells(),
            &participant_faces,
            ingress,
            apparatus,
        )
    }

    /// Return one exterior projective current through the complete cultivated cell field already
    /// mounted in this product.  The exterior source cannot choose cells: the card contracts every
    /// current context with every native affine cell and returns the complete non-dominated front.
    /// A participant aperture only restricts the receiver family after that contact law; its
    /// proper-name surface is applied by the cold codec after the native section has returned.
    pub fn emanate_situated_current(
        &mut self,
        current: &GranularExteriorProjectiveCurrent,
        participant_aperture: bool,
        deed: EmanationDeed,
        perspective_surface: Option<String>,
    ) -> Result<ProductSituatedCurrentEmanation, LaboratoryCultivationError> {
        let deed_wire = match deed {
            EmanationDeed::Describe => 0,
            EmanationDeed::Identify => 1,
            EmanationDeed::Infer => 2,
            _ => {
                return Err(LaboratoryCultivationError::Correspondence(
                    "the situated current front admits describe, identify, and infer deeds"
                        .to_owned(),
                ));
            }
        };
        if participant_aperture != perspective_surface.is_some()
            || perspective_surface.as_ref().is_some_and(String::is_empty)
            || current.contexts.is_empty()
            || current.standing_potential_identity_sha256
                != self.rest.body().body().granular_potential().identity()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the situated current does not cross this Athena product receiver".to_owned(),
            ));
        }
        if current.integrated_factor_current.is_empty()
            || current.integrated_context_occurrence_population == 0
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the situated exterior occurrence has no integrated path current".to_owned(),
            ));
        }
        let contexts = current
            .contexts
            .iter()
            .map(|context| AddressedCurrentSection {
                boundary_state: Some(context.boundary_state),
                quadratic_weight: BigUint::from(1u8),
                factor_current: context
                    .factor_current
                    .iter()
                    .map(|coordinate| (coordinate.factor, coordinate.incidence.clone()))
                    .collect(),
            })
            .collect::<Vec<_>>();
        let apparatus = self
            .resident
            .conduct_situated_current_front(&contexts, participant_aperture, deed_wire)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        let affine = self.rest.body().body().body();
        if apparatus.cell_population != affine.relational_potential().cells.len()
            || apparatus.selected.len() != affine.affine_cells().len()
            || apparatus.selected_population == 0
            || apparatus.scalar_score_present
            || apparatus.authored_output_extent_present
            || apparatus.invariant_transport_reuploaded
            || apparatus.cpu_semantic_replay_after_device
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the resident situated current did not return a complete native cell front"
                    .to_owned(),
            ));
        }
        let selected_indices = apparatus
            .selected
            .iter()
            .enumerate()
            .filter_map(|(at, selected)| (*selected != 0).then_some(at))
            .collect::<Vec<_>>();
        let selected_cell_addresses = selected_indices
            .iter()
            .map(|at| affine.relational_potential().cells[*at].address.clone())
            .collect::<Vec<_>>();
        let selected_affine_sections = selected_indices
            .iter()
            .map(|at| affine.affine_cells()[*at].clone())
            .collect::<Vec<_>>();
        let selected_set = selected_indices
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        let hidden_cell_reconstruction_fibre = affine
            .relational_potential()
            .cells
            .iter()
            .enumerate()
            .filter(|(at, _)| !selected_set.contains(at))
            .map(|(_, cell)| cell.address.clone())
            .collect::<Vec<_>>();
        let surface = match perspective_surface.as_deref() {
            Some(surface) => render_returned_participant_cells(
                affine.relational_potential(),
                affine.relational_codec(),
                &selected_cell_addresses,
                surface,
            )?,
            None => render_returned_cells(
                affine.relational_potential(),
                affine.relational_codec(),
                &selected_cell_addresses,
            )?,
        };
        let surface_sha256 = render_digest(surface.as_bytes());
        let identity_sha256 = render_digest(
            &serde_json::to_vec(&(
                "soma-life.product-situated-current-emanation.v1",
                self.rest.identity(),
                &current.identity_sha256,
                participant_aperture,
                deed,
                &perspective_surface,
                &selected_cell_addresses,
                &selected_affine_sections,
                &apparatus.overlap_identity_sha256,
                &surface_sha256,
            ))
            .map_err(|error| LaboratoryCultivationError::Correspondence(error.to_string()))?,
        );
        Ok(ProductSituatedCurrentEmanation {
            schema: "soma-life.product-situated-current-emanation.v1".to_owned(),
            rest_identity_sha256: self.rest.identity().to_owned(),
            exterior_occurrence: current.exterior_occurrence.clone(),
            exterior_current_identity_sha256: current.identity_sha256.clone(),
            participant_aperture,
            deed,
            perspective_surface,
            selected_cell_addresses,
            selected_affine_sections,
            hidden_cell_reconstruction_fibre,
            surface,
            surface_sha256,
            identity_sha256,
            apparatus,
        })
    }

    /// Return the exact shared-incidence section of one fine-grained technical recurrence and one
    /// resident participant/history return while retaining every admitted organ in this owner.
    pub fn join_technical_history(
        &self,
        technical: &GranularExteriorProjectiveCurrent,
        history: &LaboratoryParticipantEmanation,
    ) -> Result<ProductTechnicalHistoryEmanation, LaboratoryCultivationError> {
        ProductTechnicalHistoryEmanation::found(&self.rest, technical, history)
    }

    /// Conduct a native material section while every admitted organ remains in the owned rest.
    pub fn conduct_material(
        &mut self,
        factorization: &mut MaterialNativeFactorization,
    ) -> Result<SituatedCultivatedConductReturn, LaboratoryCultivationError> {
        let identity = self.rest.identity();
        if factorization.predecessor_rest_identity_sha256 != identity {
            return Err(LaboratoryCultivationError::Correspondence(
                "the material section addresses another Athena product body".to_owned(),
            ));
        }
        let transport = factorization
            .cultivated_affine_transport
            .as_mut()
            .ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "the product material section has no affine transport field".to_owned(),
                )
            })?;
        if transport.standing_rest_identity_sha256 != identity
            || transport.resident_apparatus.is_some()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the product affine testimony is stale or already conducted".to_owned(),
            ));
        }
        let integrated = self
            .resident
            .conduct(
                &vec![true; self.factors.len()],
                &transport.entering_section,
                0,
            )
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        if !integrated.one_underlying_context
            || integrated.launches != 3
            || integrated.synchronizations != 1
            || integrated.intermediate_host_egress_octets != 0
            || integrated.coupled.synchronizations != 0
            || integrated.affine.synchronizations != 0
            || integrated.participant.synchronizations != 0
            || integrated.invariant_transport_reuploaded
            || integrated.cpu_semantic_replay_after_device
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the Athena product fronts did not return as one card-owned word".to_owned(),
            ));
        }
        let integrated_receipt = MaterialIntegratedResidentApparatusReceipt {
            schema: "soma-life.material-integrated-resident-apparatus.v1".to_owned(),
            device: integrated.coupled.device.clone(),
            context_identity: integrated.context_identity,
            one_underlying_context: integrated.one_underlying_context,
            launches: integrated.launches,
            synchronizations: integrated.synchronizations,
            successor_host_ingress_octets: integrated.successor_host_ingress_octets,
            successor_host_egress_octets: integrated.successor_host_egress_octets,
            intermediate_host_egress_octets: integrated.intermediate_host_egress_octets,
            resident_invariant_octets: integrated.resident_invariant_octets,
            invariant_transport_reuploaded: integrated.invariant_transport_reuploaded,
            cpu_semantic_replay_after_device: integrated.cpu_semantic_replay_after_device,
        };
        let affine = integrated.affine;
        if affine.addressed_cell_population != transport.addressed_cell_population
            || affine.local_fibre_term_population != transport.local_fibre_term_population
            || affine.exact_reconstruction_cell_population != transport.addressed_cell_population
            || affine.invariant_transport_reuploaded
            || affine.cpu_semantic_replay_after_device
            || affine.cell_selected_or_ranked
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the Athena product affine field diverged from its exact cold reconstruction"
                    .to_owned(),
            ));
        }
        transport.resident_apparatus = Some(affine);
        transport.integrated_resident_apparatus = Some(integrated_receipt);
        if integrated.coupled.sections != self.expected
            || integrated.coupled.sections.len() != self.factors.len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the integrated product word diverged from the one Athena body".to_owned(),
            ));
        }
        let factors = self
            .factors
            .iter()
            .zip(&integrated.coupled.sections)
            .map(|((address, incident_threads), current)| {
                super::SituatedCultivatedConductedFactor {
                    address: address.clone(),
                    incident_threads: incident_threads.clone(),
                    current: current.clone(),
                }
            })
            .collect();
        Ok(SituatedCultivatedConductReturn {
            rest_identity_sha256: identity.to_owned(),
            factors,
            apparatus: integrated.coupled,
        })
    }

    pub fn into_rest(self) -> OpticalProductRest {
        self.rest
    }
}
