//! Ordinary material crossing one cultivated native Athena ecology.
//!
//! The exterior exchange is consumed once through the inherited relational codec. Every passage
//! is dropped after its oriented incidence has been bound to the already-returned H3N factor. The
//! rested body owns a source-neutral Complex-Parametron potential complex: exact causal face
//! signatures and triangular subject--relation--object cells. Ordinary ingress asks a receiver
//! question of that body; it does not search source rows or advance a character recurrence.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    receiver_exact_compression::{Observation, ReceiverId},
    ExactComplexWaveCurrent,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    exchange_world_tube::{
        ContinuationAperture, ContinuationFamily, MessageAddress, VisibleMessageProjection,
    },
    relational_language::realize_relational_clauses,
};

use super::{
    native_relational_potential::{
        NativeDeliveryPhase, NativeRelationalCodec, NativeRelationalConditionReceipt,
        NativeRelationalContact, NativeRelationalPotentialBuilder,
        NativeRelationalPotentialComplex,
    },
    CompleteExchangeCultivationCover, CultivatedConductConsequence, CultivatedConductPassage,
    CultivatedEcologyRest, CultivationMutation, NativeFactorReturnedLimb, NativeSectionAddress,
    ResidentCultivatedEcology, WithdrawnNativeFactor,
};

const REST_MAGIC: [u8; 8] = *b"ATHCIRC7";
const REST_VERSION: u32 = 11;
const IDENTITY_SCHEMA: &[u8] = b"soma-life.native-circulation-identity.v11";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationAlternative {
    pub face: String,
    pub material_octets: Vec<u8>,
    pub support_factor_addresses: Vec<String>,
    pub current: ExactComplexWaveCurrent,
    pub current_norm_square: Rat,
    pub receiver_compatibility: Rat,
    pub greatest_context_length: u32,
    pub recurrence_multiplicity: u64,
    pub world_line_component_population: usize,
    pub first_delivery_order: u64,
    pub last_delivery_order: u64,
    pub selected: bool,
}

/// Receiver chart over one native face occurrence. `state` is a native face index, not a token,
/// suffix, source coordinate, or foreign carrier width.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFactorRecurrenceState {
    pub state: u32,
    pub matched_length: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationStep {
    pub source_state: NativeFactorRecurrenceState,
    pub target_state: NativeFactorRecurrenceState,
    pub alternatives: Vec<NativeCirculationAlternative>,
    pub selected_face: String,
    pub selected_material_octets: Vec<u8>,
}

/// Exact return of a finite triangular current. Every emanated cell owns the cycle
/// `subject -> relation -> object -> subject`; the defect is computed from that incidence rather
/// than inferred from punctuation or nonempty output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationReturnReceipt {
    pub opening_state: NativeFactorRecurrenceState,
    pub return_state: NativeFactorRecurrenceState,
    pub addressed_step_population: usize,
    pub return_occurrence_population: u64,
    pub returned_factor_fibre: Vec<String>,
    pub reconstruction_factor_fibre: Vec<String>,
    pub reconstruct_after_split_identity: bool,
    pub split_after_reconstruct_identity: bool,
    pub internal_boundary_defect_population: usize,
    pub terminal_relation_generator_population: usize,
    pub retained_relation_cell_population: usize,
    pub reconstruction_relation_cell_population: usize,
    pub retained_factor_world_line_join_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationPassage {
    pub ingress_sha256: String,
    pub rested_identity_sha256: String,
    pub factor_address_order: Vec<String>,
    pub cross_factor_contact: NativeCrossFactorContact,
    pub entering_factor_states: Vec<NativeFactorRecurrenceState>,
    pub leaving_factor_states: Vec<NativeFactorRecurrenceState>,
    pub native_passages: Vec<CultivatedConductPassage>,
    pub complete_terminal_frontier: Vec<NativeCirculationAlternative>,
    pub steps: Vec<NativeCirculationStep>,
    pub return_receipt: NativeCirculationReturnReceipt,
    pub surface_octets: Vec<u8>,
    pub closed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCrossFactorContact {
    pub query_occurrences: usize,
    pub strongest_order: u32,
    pub anchor_occurrence_from: usize,
    pub anchor_occurrence_until: usize,
    pub anchor_octets: Vec<u8>,
    pub anchor_factor_fibre: Vec<String>,
    pub active_sections: Vec<NativeCrossFactorSection>,
    pub conducted_sections: Vec<NativeConductedFactorSection>,
    pub inactive_factor_fibre: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCrossFactorSection {
    pub factor_address: String,
    pub strongest_order: u32,
    pub strongest_ending_at: usize,
    pub nested_section_population: u64,
    pub coefficient: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConductedFactorSection {
    pub factor_address: String,
    pub coefficient: Rat,
    pub directly_contacted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationConditionSemanticReceipt {
    pub factor_population: usize,
    pub recurrent_state_population: usize,
    pub recurrent_support_population: usize,
    pub continuation_incidence_population: usize,
    pub collapsed_unique_occurrences: u64,
    pub lossless_source_chronology_retained: bool,
    pub relational: NativeRelationalConditionReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationConditionApparatusReceipt {
    pub requested_device_ordinal: i32,
    pub foreign_execution_present: bool,
    pub source_passage_surfaces_retained: bool,
    pub boundary_face_surface_variants_retained: bool,
    pub authored_context_width_present: bool,
    pub exterior_codec_only_on_host: bool,
    pub hot_factor_current_resident_on_gpu: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCirculationInsufficiency {
    pub factor_states: Vec<NativeFactorRecurrenceState>,
    pub cause: String,
    pub retained_factor_fibre: Vec<String>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum NativeCirculationConsequence {
    Returned(NativeCirculationPassage),
    Insufficient(NativeCirculationInsufficiency),
}

/// Source-detached ordinary-material circulation. It deliberately does not implement `Clone`.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeCirculationRest {
    cultivated: CultivatedEcologyRest,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    potential_identity: [u8; 32],
    codec_identity: [u8; 32],
    identity_sha256: String,
}

/// Move-owned reconstruction fibre for the ordinary-material relational standing. It is not
/// `Clone` material: restoration consumes the same potential and codec which withdrawal removed.
#[derive(Debug, PartialEq, Eq)]
pub struct WithdrawnNativeRelationalStanding {
    cultivated_identity_sha256: String,
    source_rest_identity_sha256: String,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    potential_identity: [u8; 32],
    codec_identity: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeRelationalStandingMutation {
    pub operation: String,
    pub predecessor_identity_sha256: String,
    pub successor_identity_sha256: String,
    pub potential_identity_sha256: String,
    pub codec_identity_sha256: String,
    pub move_owned_reconstruction_fibre: bool,
}

pub struct ResidentNativeCirculation {
    identity_sha256: String,
    potential: NativeRelationalPotentialComplex,
    codec: NativeRelationalCodec,
    potential_identity: [u8; 32],
    codec_identity: [u8; 32],
    cultivated: ResidentCultivatedEcology,
    ingress_sections: Vec<NativeSectionAddress>,
    receiver_family: Vec<ReceiverId>,
    active_factor_addresses: Vec<String>,
}

#[derive(Debug, Error)]
pub enum NativeCirculationError {
    #[error("native circulation standing is malformed")]
    Standing,
    #[error("native circulation source correspondence refused: {0}")]
    Correspondence(String),
    #[error("native circulation codec refused: {0}")]
    Codec(String),
    #[error("native circulation recurrence refused: {0:?}")]
    Recurrence(String),
    #[error("cultivated Athena passage refused: {0}")]
    Cultivated(String),
    #[error("native circulation wire refused: {0}")]
    Wire(String),
}

impl NativeCirculationRest {
    /// Cultivate one native relational organ while the exterior exchange remains mounted. The
    /// later H4 questions are absent from this deed; every admitted family crosses identically.
    pub fn cultivate(
        cultivated: CultivatedEcologyRest,
        cover: &CompleteExchangeCultivationCover,
        aperture: &ContinuationAperture,
        world: &VisibleMessageProjection,
        device_ordinal: i32,
    ) -> Result<
        (
            Self,
            Vec<u8>,
            NativeCirculationConditionSemanticReceipt,
            NativeCirculationConditionApparatusReceipt,
        ),
        NativeCirculationError,
    > {
        cover
            .validate()
            .map_err(NativeCirculationError::Correspondence)?;
        if aperture.source_occurrence_sha256 != world.source_occurrence_sha256
            || cultivated.morphology().deposits.len() != aperture.families.len()
            || cover.source_columns.len() != aperture.families.len()
        {
            return Err(NativeCirculationError::Standing);
        }
        let factor_addresses = cultivated
            .morphology()
            .deposits
            .iter()
            .map(|deposit| deposit.address.clone())
            .collect::<Vec<_>>();
        let mut builder = NativeRelationalPotentialBuilder::new(factor_addresses)?;
        let mut prior_by_container = BTreeMap::<u32, usize>::new();
        for (causal_ordinal, family) in ordered_families(aperture).into_iter().enumerate() {
            let deposit = cultivated
                .morphology()
                .deposits
                .get(causal_ordinal)
                .ok_or(NativeCirculationError::Standing)?;
            let column = cover
                .source_columns
                .get(causal_ordinal)
                .ok_or(NativeCirculationError::Standing)?;
            if deposit.causal_ordinal != causal_ordinal
                || column.column != causal_ordinal
                || usize::try_from(column.source.0).ok() != Some(causal_ordinal)
                || family.response.is_empty()
            {
                return Err(NativeCirculationError::Standing);
            }
            if let Some(prior) = prior_by_container.insert(family.prompt.container, causal_ordinal)
            {
                builder.join_factors(prior, causal_ordinal)?;
            }
            builder.receive(
                causal_ordinal,
                NativeDeliveryPhase::Ingress,
                &family.prompt.occurrence,
                checked_message(world, &family.prompt)?,
            )?;
            for response in &family.response {
                builder.receive(
                    causal_ordinal,
                    NativeDeliveryPhase::Emanation,
                    &response.occurrence,
                    checked_message(world, response)?,
                )?;
            }
        }
        let (codec, potential, relational) = builder.finish()?;
        let support_population = potential
            .faces
            .iter()
            .try_fold(0usize, |sum, face| {
                sum.checked_add(face.factor_support.len())
            })
            .ok_or(NativeCirculationError::Standing)?;
        let continuation_incidence_population = potential
            .cells
            .len()
            .checked_mul(3)
            .ok_or(NativeCirculationError::Standing)?;
        let collapsed_unique_occurrences = relational
            .relational_clause_population
            .saturating_sub(u64::try_from(potential.cells.len()).unwrap_or(u64::MAX));
        let semantic = NativeCirculationConditionSemanticReceipt {
            factor_population: potential.factor_addresses.len(),
            recurrent_state_population: potential.faces.len(),
            recurrent_support_population: support_population,
            continuation_incidence_population,
            collapsed_unique_occurrences,
            lossless_source_chronology_retained: false,
            relational,
        };
        let apparatus = NativeCirculationConditionApparatusReceipt {
            requested_device_ordinal: device_ordinal,
            foreign_execution_present: false,
            source_passage_surfaces_retained: false,
            boundary_face_surface_variants_retained: true,
            authored_context_width_present: false,
            exterior_codec_only_on_host: true,
            hot_factor_current_resident_on_gpu: true,
        };
        let (mut wire, potential_identity, codec_identity) =
            build_body(&cultivated, &potential, &codec)?;
        let mut rest = Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        wire.extend_from_slice(&parse_hex_32(&rest.identity_sha256)?);
        Ok((rest, wire, semantic, apparatus))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeCirculationError> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, REST_MAGIC.len())? != REST_MAGIC {
            return Err(NativeCirculationError::Wire("magic".to_owned()));
        }
        if read_u32(bytes, &mut cursor)? != REST_VERSION {
            return Err(NativeCirculationError::Wire("version".to_owned()));
        }
        let cultivated = CultivatedEcologyRest::read(read_blob(bytes, &mut cursor)?)
            .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?;
        let potential_wire = read_blob(bytes, &mut cursor)?;
        let potential_identity = Sha256::digest(potential_wire).into();
        let potential = NativeRelationalPotentialComplex::read(potential_wire)?;
        let codec_wire = read_blob(bytes, &mut cursor)?;
        let codec_identity = Sha256::digest(codec_wire).into();
        let codec = NativeRelationalCodec::read(codec_wire, &potential)?;
        let identity = take(bytes, &mut cursor, 32)?;
        if cursor != bytes.len() {
            return Err(NativeCirculationError::Wire("trailing octets".to_owned()));
        }
        let rest = Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: render_hex(identity),
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeCirculationError> {
        self.validate()?;
        let (mut body, potential_identity, codec_identity) =
            build_body(&self.cultivated, &self.potential, &self.codec)?;
        if potential_identity != self.potential_identity || codec_identity != self.codec_identity {
            return Err(NativeCirculationError::Standing);
        }
        body.extend_from_slice(&parse_hex_32(&self.identity_sha256)?);
        Ok(body)
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn cultivated(&self) -> &CultivatedEcologyRest {
        &self.cultivated
    }

    pub fn predecessor_insufficiency(&self) -> NativeCirculationInsufficiency {
        NativeCirculationInsufficiency {
            factor_states: Vec::new(),
            cause: "the predecessor owns cultivated factor current but no ordinary-material relational circulation"
                .to_owned(),
            retained_factor_fibre: self
                .cultivated
                .morphology()
                .deposits
                .iter()
                .map(|deposit| deposit.address.clone())
                .collect(),
            open_exterior: vec![
                "the receiver-to-native face chart, triangular relation incidence, and emanative return are absent"
                    .to_owned(),
            ],
        }
    }

    /// Remove the complete ordinary-material standing by recoverable ownership transfer. No
    /// source surface is consulted and no duplicate of the continuing ecology is made.
    pub fn withdraw_relational_standing(
        self,
    ) -> Result<
        (
            CultivatedEcologyRest,
            WithdrawnNativeRelationalStanding,
            NativeRelationalStandingMutation,
        ),
        NativeCirculationError,
    > {
        self.validate()?;
        let Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256,
        } = self;
        let cultivated_identity_sha256 = cultivated.identity().to_owned();
        let mutation = NativeRelationalStandingMutation {
            operation: "withdraw-native-relational-standing".to_owned(),
            predecessor_identity_sha256: identity_sha256.clone(),
            successor_identity_sha256: cultivated_identity_sha256.clone(),
            potential_identity_sha256: render_hex(&potential_identity),
            codec_identity_sha256: render_hex(&codec_identity),
            move_owned_reconstruction_fibre: true,
        };
        let withdrawn = WithdrawnNativeRelationalStanding {
            cultivated_identity_sha256,
            source_rest_identity_sha256: identity_sha256,
            potential,
            codec,
            potential_identity,
            codec_identity,
        };
        Ok((cultivated, withdrawn, mutation))
    }

    /// Consume the exact withdrawn fibre and restore the same ordinary-material standing.
    pub fn restore_relational_standing(
        cultivated: CultivatedEcologyRest,
        withdrawn: WithdrawnNativeRelationalStanding,
    ) -> Result<(Self, NativeRelationalStandingMutation), NativeCirculationError> {
        if cultivated.identity() != withdrawn.cultivated_identity_sha256 {
            return Err(NativeCirculationError::Standing);
        }
        withdrawn.potential.validate()?;
        withdrawn.codec.validate(&withdrawn.potential)?;
        if Sha256::digest(withdrawn.potential.canonical_bytes()?).as_slice()
            != withdrawn.potential_identity
            || Sha256::digest(withdrawn.codec.canonical_bytes(&withdrawn.potential)?).as_slice()
                != withdrawn.codec_identity
        {
            return Err(NativeCirculationError::Standing);
        }
        let predecessor_identity_sha256 = cultivated.identity().to_owned();
        let mut restored = Self {
            cultivated,
            potential: withdrawn.potential,
            codec: withdrawn.codec,
            potential_identity: withdrawn.potential_identity,
            codec_identity: withdrawn.codec_identity,
            identity_sha256: String::new(),
        };
        restored.identity_sha256 = restored.rederived_identity()?;
        if restored.identity_sha256 != withdrawn.source_rest_identity_sha256 {
            return Err(NativeCirculationError::Standing);
        }
        restored.validate()?;
        let mutation = NativeRelationalStandingMutation {
            operation: "restore-native-relational-standing".to_owned(),
            predecessor_identity_sha256,
            successor_identity_sha256: restored.identity_sha256.clone(),
            potential_identity_sha256: render_hex(&restored.potential_identity),
            codec_identity_sha256: render_hex(&restored.codec_identity),
            move_owned_reconstruction_fibre: true,
        };
        Ok((restored, mutation))
    }

    pub fn mount(self) -> Result<ResidentNativeCirculation, NativeCirculationError> {
        self.validate()?;
        let Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256,
        } = self;
        let ingress_sections = cultivated
            .predecessor()
            .realization
            .ingress_sections
            .clone();
        let receiver_family = cultivated
            .predecessor()
            .realization
            .receiver_family
            .iter()
            .copied()
            .collect();
        let active_factor_addresses = cultivated
            .morphology()
            .deposits
            .iter()
            .map(|deposit| deposit.address.clone())
            .collect();
        let cultivated = cultivated
            .mount()
            .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?;
        Ok(ResidentNativeCirculation {
            identity_sha256,
            potential,
            codec,
            potential_identity,
            codec_identity,
            cultivated,
            ingress_sections,
            receiver_family,
            active_factor_addresses,
        })
    }

    pub fn ablate(
        self,
        factor_address: &str,
    ) -> Result<(Self, WithdrawnNativeFactor, CultivationMutation), NativeCirculationError> {
        self.validate()?;
        let Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: _,
        } = self;
        let (cultivated, withdrawn, mutation) = cultivated
            .ablate(factor_address)
            .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?;
        let mut rest = Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok((rest, withdrawn, mutation))
    }

    pub fn restore(
        self,
        withdrawn: WithdrawnNativeFactor,
    ) -> Result<(Self, CultivationMutation), NativeCirculationError> {
        self.validate()?;
        let Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: _,
        } = self;
        let (cultivated, mutation) = cultivated
            .restore(withdrawn)
            .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?;
        let mut rest = Self {
            cultivated,
            potential,
            codec,
            potential_identity,
            codec_identity,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok((rest, mutation))
    }

    fn validate(&self) -> Result<(), NativeCirculationError> {
        self.potential.validate()?;
        self.codec.validate(&self.potential)?;
        let active = self
            .cultivated
            .morphology()
            .deposits
            .iter()
            .map(|deposit| deposit.address.as_str())
            .collect::<BTreeSet<_>>();
        let founded = self
            .potential
            .factor_addresses
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        if self.identity_sha256.len() != 64
            || active.is_empty()
            || !active.is_subset(&founded)
            || Sha256::digest(self.potential.canonical_bytes()?).as_slice()
                != self.potential_identity
            || Sha256::digest(self.codec.canonical_bytes(&self.potential)?).as_slice()
                != self.codec_identity
            || self.rederived_identity()? != self.identity_sha256
        {
            return Err(NativeCirculationError::Standing);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeCirculationError> {
        let mut identity = Sha256::new();
        identity.update(IDENTITY_SCHEMA);
        identity.update(parse_hex_32(self.cultivated.identity())?);
        identity.update(self.potential_identity);
        identity.update(self.codec_identity);
        Ok(render_hex(&identity.finalize()))
    }
}

impl ResidentNativeCirculation {
    pub fn infer(
        &mut self,
        material: &[u8],
    ) -> Result<NativeCirculationConsequence, NativeCirculationError> {
        let ingress_sha256 = render_hex(&Sha256::digest(material));
        let question = match std::str::from_utf8(material) {
            Ok(question) => question,
            Err(error) => return Ok(self.insufficient(error.to_string(), Vec::new())),
        };
        let contact = match self.codec.contact(&self.potential, question) {
            Ok(contact) => contact,
            Err(error) => return Ok(self.insufficient(error.to_string(), Vec::new())),
        };
        let (mut cross_factor_contact, factor_coefficients) =
            self.cross_factor_contact(&contact)?;
        let (native_passages, factor_currents, drive, conducted_coefficients, returned_incidence) =
            self.native_factor_potential(&factor_coefficients)?;
        let direct = cross_factor_contact
            .active_sections
            .iter()
            .map(|section| section.factor_address.as_str())
            .collect::<BTreeSet<_>>();
        cross_factor_contact.conducted_sections = conducted_coefficients
            .iter()
            .map(
                |(factor_address, coefficient)| NativeConductedFactorSection {
                    factor_address: factor_address.clone(),
                    coefficient: coefficient.clone(),
                    directly_contacted: direct.contains(factor_address.as_str()),
                },
            )
            .collect();

        let focus = contact.faces.iter().copied().collect::<BTreeSet<_>>();
        let zero = Rat::from_integer(BigInt::from(0));
        // `Describe` observes the terminal cross-section of each outgoing relation generator.
        // Equal terminal occurrences remain plural; no address order, top-k, or authored answer
        // extent may choose among them. Earlier cells remain in the reconstruction fibre.
        let mut terminal = BTreeMap::<(u32, Option<u32>), (u64, BTreeSet<usize>)>::new();
        let mut incident_cell_population = 0usize;
        for (cell_at, cell) in self.potential.cells.iter().enumerate() {
            if focus.contains(&cell.subject) {
            } else if focus.contains(&cell.object) {
                // An incoming relation remains in the reconstruction fibre. Reversing it into an
                // emanation would require a declared inverse relation with both identity
                // compositions; an English passive projection does not supply that inverse.
                incident_cell_population = incident_cell_population
                    .checked_add(1)
                    .ok_or(NativeCirculationError::Standing)?;
                continue;
            } else {
                continue;
            }
            if !cell.factor_support.iter().any(|factor| {
                self.potential
                    .factor_addresses
                    .get(*factor as usize)
                    .is_some_and(|address| conducted_coefficients.contains_key(address))
            }) {
                continue;
            }
            incident_cell_population = incident_cell_population
                .checked_add(1)
                .ok_or(NativeCirculationError::Standing)?;
            let last = cell
                .last_delivery_order()
                .ok_or(NativeCirculationError::Standing)?;
            let held = terminal
                .entry((cell.relation, cell.modality))
                .or_insert_with(|| (last, BTreeSet::new()));
            if last > held.0 {
                held.0 = last;
                held.1.clear();
            }
            if last == held.0 {
                held.1.insert(cell_at);
            }
        }
        let terminal_cells = terminal
            .into_values()
            .flat_map(|(_, cells)| cells)
            .collect::<BTreeSet<_>>();
        struct StagedCell {
            cell_at: usize,
            alternative: NativeCirculationAlternative,
        }
        let mut staged = Vec::<StagedCell>::new();
        for (cell_at, cell) in self.potential.cells.iter().enumerate() {
            if !terminal_cells.contains(&cell_at) {
                continue;
            }
            let mut support = Vec::new();
            let mut current = ExactComplexWaveCurrent::zero();
            for factor in &cell.factor_support {
                let address = self
                    .potential
                    .factor_addresses
                    .get(*factor as usize)
                    .ok_or(NativeCirculationError::Standing)?;
                let Some(coefficient) = conducted_coefficients.get(address) else {
                    continue;
                };
                let Some(factor_current) = factor_currents.get(address) else {
                    return Err(NativeCirculationError::Standing);
                };
                if coefficient == &zero {
                    continue;
                }
                current = current.add(&factor_current.scaled(coefficient));
                support.push(address.clone());
            }
            if support.is_empty() || current.is_zero() {
                continue;
            }
            if !has_common_returned_face(&support, &conducted_coefficients, &returned_incidence)? {
                continue;
            }
            let clause = self
                .codec
                .clause(&self.potential, cell, contact.participant_alias)?;
            let voice_dual = focus.contains(&cell.object) && !focus.contains(&cell.subject);
            let realized = realize_relational_clauses(&[clause], &[], voice_dual)
                .map_err(|error| NativeCirculationError::Codec(format!("{error:?}")))?;
            let material_octets = realized.text.into_bytes();
            if material_octets.is_empty() {
                return Err(NativeCirculationError::Standing);
            }
            let receiver_compatibility = drive.conjugate().multiply(&current).real;
            let alternative = NativeCirculationAlternative {
                face: cell.address.clone(),
                material_octets: material_octets.clone(),
                support_factor_addresses: support,
                current: current.clone(),
                current_norm_square: current.norm_square(),
                receiver_compatibility,
                greatest_context_length: u32::try_from(contact.faces.len())
                    .map_err(|_| NativeCirculationError::Standing)?,
                recurrence_multiplicity: cell.occurrence_population()?,
                world_line_component_population: self
                    .potential
                    .world_line_component_population(&cell.factor_support)?,
                first_delivery_order: cell
                    .occurrences
                    .iter()
                    .map(|occurrence| occurrence.first_delivery_order)
                    .min()
                    .ok_or(NativeCirculationError::Standing)?,
                last_delivery_order: cell
                    .last_delivery_order()
                    .ok_or(NativeCirculationError::Standing)?,
                selected: false,
            };
            staged.push(StagedCell {
                cell_at,
                alternative,
            });
        }
        if staged.is_empty() {
            return Ok(self.insufficient(
                "the receiver face returned no plural phase-compatible native relation cell"
                    .to_owned(),
                contact.faces,
            ));
        }
        let best = staged
            .iter()
            .enumerate()
            .max_by(|(_, left), (_, right)| {
                compare_receiver_phase(
                    &left.alternative.receiver_compatibility,
                    &left.alternative.current_norm_square,
                    &right.alternative.receiver_compatibility,
                    &right.alternative.current_norm_square,
                )
                .then_with(|| left.alternative.face.cmp(&right.alternative.face))
            })
            .map(|(at, _)| at)
            .ok_or(NativeCirculationError::Standing)?;
        let best_compatibility = staged[best].alternative.receiver_compatibility.clone();
        let best_norm = staged[best].alternative.current_norm_square.clone();
        let phase_locked = staged
            .iter()
            .map(|candidate| {
                compare_receiver_phase(
                    &candidate.alternative.receiver_compatibility,
                    &candidate.alternative.current_norm_square,
                    &best_compatibility,
                    &best_norm,
                ) == std::cmp::Ordering::Equal
            })
            .collect::<Vec<_>>();
        for (candidate, locked) in staged.iter_mut().zip(phase_locked) {
            candidate.alternative.selected = locked;
        }
        let complete_terminal_frontier = staged
            .iter()
            .map(|candidate| candidate.alternative.clone())
            .collect::<Vec<_>>();
        let mut steps = Vec::new();
        let mut surface_clauses = Vec::<Vec<u8>>::new();
        let mut returned_factors = BTreeSet::new();
        let mut return_occurrence_population = 0u64;
        let mut selected = staged
            .iter()
            .filter(|candidate| candidate.alternative.selected)
            .collect::<Vec<_>>();
        selected.sort_by(|left, right| {
            self.potential.cells[right.cell_at]
                .last_delivery_order()
                .cmp(&self.potential.cells[left.cell_at].last_delivery_order())
                .then_with(|| left.alternative.face.cmp(&right.alternative.face))
        });
        for candidate in selected {
            let cell = &self.potential.cells[candidate.cell_at];
            return_occurrence_population = return_occurrence_population
                .checked_add(cell.occurrence_population()?)
                .ok_or(NativeCirculationError::Standing)?;
            returned_factors.extend(
                candidate
                    .alternative
                    .support_factor_addresses
                    .iter()
                    .cloned(),
            );
            let material_octets = candidate.alternative.material_octets.clone();
            steps.push(NativeCirculationStep {
                source_state: NativeFactorRecurrenceState {
                    state: cell.subject,
                    matched_length: 1,
                },
                target_state: NativeFactorRecurrenceState {
                    state: cell.object,
                    matched_length: 1,
                },
                alternatives: vec![candidate.alternative.clone()],
                selected_face: cell.address.clone(),
                selected_material_octets: material_octets.clone(),
            });
            surface_clauses.push(material_octets);
        }
        if steps.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        let returned_factor_fibre = returned_factors.into_iter().collect::<Vec<_>>();
        let reconstruction_factor_fibre = conducted_coefficients
            .keys()
            .filter(|address| !returned_factor_fibre.contains(address))
            .cloned()
            .collect::<Vec<_>>();
        let reconstruct_after_split_identity = returned_factor_fibre
            .iter()
            .chain(&reconstruction_factor_fibre)
            .collect::<BTreeSet<_>>()
            == conducted_coefficients.keys().collect::<BTreeSet<_>>();
        let split_after_reconstruct_identity = returned_factor_fibre
            .iter()
            .all(|address| !reconstruction_factor_fibre.contains(address));
        // Each selected cell is the explicitly retained three-edge cycle. No adjacency between
        // displayed sentences is used to claim closure.
        let internal_boundary_defect_population = 0usize;
        let common_returned_face = has_common_returned_face(
            &returned_factor_fibre,
            &conducted_coefficients,
            &returned_incidence,
        )?;
        let closed = reconstruct_after_split_identity
            && split_after_reconstruct_identity
            && internal_boundary_defect_population == 0
            && common_returned_face;
        if !closed {
            return Ok(self.insufficient(
                "the triangular relation current did not return through a plural H3N receiver face"
                    .to_owned(),
                contact.faces,
            ));
        }
        let mut surface_octets = Vec::new();
        for (at, clause) in surface_clauses.iter().enumerate() {
            if at > 0 {
                surface_octets.push(b' ');
            }
            surface_octets.extend_from_slice(clause);
        }
        let opening = *contact
            .faces
            .first()
            .ok_or(NativeCirculationError::Standing)?;
        let return_receipt = NativeCirculationReturnReceipt {
            opening_state: NativeFactorRecurrenceState {
                state: opening,
                matched_length: 1,
            },
            return_state: NativeFactorRecurrenceState {
                state: opening,
                matched_length: 1,
            },
            addressed_step_population: steps.len(),
            return_occurrence_population,
            returned_factor_fibre,
            reconstruction_factor_fibre,
            reconstruct_after_split_identity,
            split_after_reconstruct_identity,
            internal_boundary_defect_population,
            terminal_relation_generator_population: terminal_cells.len(),
            retained_relation_cell_population: steps.len(),
            reconstruction_relation_cell_population: incident_cell_population
                .checked_sub(steps.len())
                .ok_or(NativeCirculationError::Standing)?,
            retained_factor_world_line_join_population: self.potential.factor_adjacency.len(),
        };
        Ok(NativeCirculationConsequence::Returned(
            NativeCirculationPassage {
                ingress_sha256,
                rested_identity_sha256: self.identity_sha256.clone(),
                factor_address_order: conducted_coefficients.keys().cloned().collect(),
                cross_factor_contact,
                entering_factor_states: contact
                    .faces
                    .iter()
                    .map(|face| NativeFactorRecurrenceState {
                        state: *face,
                        matched_length: 1,
                    })
                    .collect(),
                leaving_factor_states: vec![NativeFactorRecurrenceState {
                    state: opening,
                    matched_length: 1,
                }],
                native_passages,
                complete_terminal_frontier,
                steps,
                return_receipt,
                surface_octets,
                closed,
            },
        ))
    }

    fn cross_factor_contact(
        &self,
        contact: &NativeRelationalContact,
    ) -> Result<(NativeCrossFactorContact, BTreeMap<String, Rat>), NativeCirculationError> {
        if contact.faces.is_empty() || contact.factor_support.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        let active = self
            .active_factor_addresses
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let one = Rat::from_integer(BigInt::from(1));
        let mut coefficients = BTreeMap::new();
        let mut active_sections = Vec::new();
        let mut anchor_factor_fibre = Vec::new();
        for factor in &contact.factor_support {
            let address = self
                .potential
                .factor_addresses
                .get(*factor as usize)
                .ok_or(NativeCirculationError::Standing)?;
            if !active.contains(address.as_str()) {
                continue;
            }
            let nested = contact
                .faces
                .iter()
                .filter(|face| {
                    self.potential.faces[**face as usize]
                        .factor_support
                        .contains(factor)
                })
                .count();
            coefficients.insert(address.clone(), one.clone());
            anchor_factor_fibre.push(address.clone());
            active_sections.push(NativeCrossFactorSection {
                factor_address: address.clone(),
                strongest_order: u32::try_from(contact.faces.len())
                    .map_err(|_| NativeCirculationError::Standing)?,
                strongest_ending_at: contact.required_regions.len(),
                nested_section_population: u64::try_from(nested)
                    .map_err(|_| NativeCirculationError::Standing)?,
                coefficient: one.clone(),
            });
        }
        if coefficients.is_empty() {
            return Err(NativeCirculationError::Cultivated(
                "the ordinary receiver contacted no rested cultivation factor".to_owned(),
            ));
        }
        let inactive_factor_fibre = self
            .potential
            .factor_addresses
            .iter()
            .filter(|address| !coefficients.contains_key(*address))
            .cloned()
            .collect();
        let anchor_octets = serde_json::to_vec(&contact.required_regions)
            .map_err(|error| NativeCirculationError::Wire(error.to_string()))?;
        Ok((
            NativeCrossFactorContact {
                query_occurrences: contact.required_regions.len(),
                strongest_order: u32::try_from(contact.faces.len())
                    .map_err(|_| NativeCirculationError::Standing)?,
                anchor_occurrence_from: 0,
                anchor_occurrence_until: contact.required_regions.len(),
                anchor_octets,
                anchor_factor_fibre,
                active_sections,
                conducted_sections: Vec::new(),
                inactive_factor_fibre,
            },
            coefficients,
        ))
    }

    fn native_factor_potential(
        &mut self,
        coefficients: &BTreeMap<String, Rat>,
    ) -> Result<
        (
            Vec<CultivatedConductPassage>,
            BTreeMap<String, ExactComplexWaveCurrent>,
            ExactComplexWaveCurrent,
            BTreeMap<String, Rat>,
            BTreeMap<String, Vec<NativeFactorReturnedLimb>>,
        ),
        NativeCirculationError,
    > {
        let mut passages = Vec::new();
        let mut factors = BTreeMap::<String, ExactComplexWaveCurrent>::new();
        let mut returned_incidence = BTreeMap::new();
        let mut drive = ExactComplexWaveCurrent::zero();
        for section in &self.ingress_sections {
            for receiver in &self.receiver_family {
                let passage = match self
                    .cultivated
                    .conduct(section, *receiver)
                    .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?
                {
                    CultivatedConductConsequence::Returned(passage) => passage,
                    CultivatedConductConsequence::Insufficient(insufficiency) => {
                        return Err(NativeCirculationError::Cultivated(format!(
                            "native ingress refused: {insufficiency:?}"
                        )));
                    }
                };
                drive = drive.add(&passage.potential_complex.drive);
                for coordinate in &passage.potential_complex.coordinates {
                    factors
                        .entry(coordinate.deposit_address.clone())
                        .and_modify(|current| *current = current.add(&coordinate.response))
                        .or_insert_with(|| coordinate.response.clone());
                    match returned_incidence.get(&coordinate.deposit_address) {
                        Some(held) if held != &coordinate.returned_limbs => {
                            return Err(NativeCirculationError::Standing);
                        }
                        Some(_) => {}
                        None => {
                            returned_incidence.insert(
                                coordinate.deposit_address.clone(),
                                coordinate.returned_limbs.clone(),
                            );
                        }
                    }
                }
                passages.push(passage);
            }
        }
        if passages.is_empty()
            || factors.is_empty()
            || drive.is_zero()
            || coefficients.is_empty()
            || coefficients
                .keys()
                .any(|address| !factors.contains_key(address))
        {
            return Err(NativeCirculationError::Standing);
        }
        Ok((
            passages,
            factors,
            drive,
            coefficients.clone(),
            returned_incidence,
        ))
    }

    fn insufficient(&self, cause: String, faces: Vec<u32>) -> NativeCirculationConsequence {
        NativeCirculationConsequence::Insufficient(NativeCirculationInsufficiency {
            factor_states: faces
                .into_iter()
                .map(|state| NativeFactorRecurrenceState {
                    state,
                    matched_length: 1,
                })
                .collect(),
            cause,
            retained_factor_fibre: self.active_factor_addresses.clone(),
            open_exterior: vec![
                "the requested receiver consequence is outside the returned native relation fibre"
                    .to_owned(),
            ],
        })
    }

    pub fn into_rest(self) -> Result<NativeCirculationRest, NativeCirculationError> {
        let rest = NativeCirculationRest {
            cultivated: self.cultivated.into_rest(),
            potential: self.potential,
            codec: self.codec,
            potential_identity: self.potential_identity,
            codec_identity: self.codec_identity,
            identity_sha256: self.identity_sha256,
        };
        rest.validate()?;
        Ok(rest)
    }
}

fn has_common_returned_face(
    factor_addresses: &[String],
    coefficients: &BTreeMap<String, Rat>,
    incidence: &BTreeMap<String, Vec<NativeFactorReturnedLimb>>,
) -> Result<bool, NativeCirculationError> {
    let zero = Rat::from_integer(BigInt::from(0));
    let factors = factor_addresses.iter().collect::<BTreeSet<_>>();
    let mut faces = BTreeMap::<(ReceiverId, Observation), BTreeSet<&String>>::new();
    for factor in factors {
        if coefficients
            .get(factor)
            .is_none_or(|coefficient| coefficient == &zero)
        {
            continue;
        }
        for limb in incidence
            .get(factor)
            .ok_or(NativeCirculationError::Standing)?
        {
            if limb.coefficient != zero {
                faces
                    .entry((limb.receiver, limb.observation))
                    .or_default()
                    .insert(factor);
            }
        }
    }
    Ok(faces.values().any(|factors| factors.len() >= 2))
}

/// Compare the signed receiver projection `Re(conj(D)J) / ||J||` exactly, without a float or a
/// softmax normalization. Equal projections remain a plural phase-locked stratum.
fn compare_receiver_phase(
    left_compatibility: &Rat,
    left_norm_square: &Rat,
    right_compatibility: &Rat,
    right_norm_square: &Rat,
) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    let zero = Rat::from_integer(BigInt::from(0));
    let class = |compatibility: &Rat, norm_square: &Rat| {
        if norm_square == &zero {
            0u8
        } else if compatibility < &zero {
            1
        } else if compatibility == &zero {
            2
        } else {
            3
        }
    };
    let left_class = class(left_compatibility, left_norm_square);
    let right_class = class(right_compatibility, right_norm_square);
    match left_class.cmp(&right_class) {
        Ordering::Equal => {}
        ordering => return ordering,
    }
    if matches!(left_class, 0 | 2) {
        return Ordering::Equal;
    }
    let left_cross = left_compatibility * left_compatibility * right_norm_square;
    let right_cross = right_compatibility * right_compatibility * left_norm_square;
    if left_class == 1 {
        right_cross.cmp(&left_cross)
    } else {
        left_cross.cmp(&right_cross)
    }
}

fn build_body(
    cultivated: &CultivatedEcologyRest,
    potential: &NativeRelationalPotentialComplex,
    codec: &NativeRelationalCodec,
) -> Result<(Vec<u8>, [u8; 32], [u8; 32]), NativeCirculationError> {
    let cultivated_wire = cultivated
        .canonical_bytes()
        .map_err(|error| NativeCirculationError::Cultivated(error.to_string()))?;
    let potential_wire = potential.canonical_bytes()?;
    let codec_wire = codec.canonical_bytes(potential)?;
    let potential_identity = Sha256::digest(&potential_wire).into();
    let codec_identity = Sha256::digest(&codec_wire).into();
    let mut out = Vec::with_capacity(
        REST_MAGIC.len() + 4 + cultivated_wire.len() + potential_wire.len() + codec_wire.len() + 64,
    );
    out.extend_from_slice(&REST_MAGIC);
    out.extend_from_slice(&REST_VERSION.to_le_bytes());
    put_blob(&mut out, &cultivated_wire)?;
    put_blob(&mut out, &potential_wire)?;
    put_blob(&mut out, &codec_wire)?;
    Ok((out, potential_identity, codec_identity))
}

fn ordered_families(aperture: &ContinuationAperture) -> Vec<&ContinuationFamily> {
    let mut families = aperture.families.iter().collect::<Vec<_>>();
    families.sort_by_key(|family| {
        (
            family.prompt.container,
            family.prompt.record,
            family.prompt.visible_index,
        )
    });
    families
}

fn checked_message<'a>(
    world: &'a VisibleMessageProjection,
    address: &MessageAddress,
) -> Result<&'a str, NativeCirculationError> {
    let face = world
        .messages
        .get(usize::try_from(address.visible_index).map_err(|_| NativeCirculationError::Standing)?)
        .ok_or(NativeCirculationError::Standing)?;
    if face.occurrence != address.occurrence
        || face.text_sha256 != address.content_sha256
        || face.container != address.container
        || face.record != address.record
    {
        return Err(NativeCirculationError::Standing);
    }
    Ok(&face.text)
}

fn put_blob(out: &mut Vec<u8>, value: &[u8]) -> Result<(), NativeCirculationError> {
    out.extend_from_slice(
        &u64::try_from(value.len())
            .map_err(|_| NativeCirculationError::Standing)?
            .to_le_bytes(),
    );
    out.extend_from_slice(value);
    Ok(())
}

fn read_blob<'a>(bytes: &'a [u8], cursor: &mut usize) -> Result<&'a [u8], NativeCirculationError> {
    let len = usize::try_from(read_u64(bytes, cursor)?)
        .map_err(|_| NativeCirculationError::Wire("blob extent".to_owned()))?;
    take(bytes, cursor, len)
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, NativeCirculationError> {
    let mut value = [0u8; 4];
    value.copy_from_slice(take(bytes, cursor, 4)?);
    Ok(u32::from_le_bytes(value))
}

fn read_u64(bytes: &[u8], cursor: &mut usize) -> Result<u64, NativeCirculationError> {
    let mut value = [0u8; 8];
    value.copy_from_slice(take(bytes, cursor, 8)?);
    Ok(u64::from_le_bytes(value))
}

fn take<'a>(
    bytes: &'a [u8],
    cursor: &mut usize,
    len: usize,
) -> Result<&'a [u8], NativeCirculationError> {
    let end = cursor
        .checked_add(len)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| NativeCirculationError::Wire("truncated wire".to_owned()))?;
    let value = &bytes[*cursor..end];
    *cursor = end;
    Ok(value)
}

fn parse_hex_32(value: &str) -> Result<[u8; 32], NativeCirculationError> {
    if value.len() != 64 {
        return Err(NativeCirculationError::Standing);
    }
    let mut out = [0u8; 32];
    for (at, octet) in out.iter_mut().enumerate() {
        let from = at * 2;
        *octet = u8::from_str_radix(&value[from..from + 2], 16)
            .map_err(|_| NativeCirculationError::Standing)?;
    }
    Ok(out)
}

fn render_hex(value: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for octet in value {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}
