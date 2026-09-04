//! Perspective-sensitive emanation from one situated Athena body.
//!
//! The incoming surface remains exterior testimony.  L3's complete native factorization and the
//! actual primary/mixed current returned by the L2 resident body found a temporary addressed
//! potential complex.  A declared receiver deed and perspective then project that successor
//! through the standing relational surface codec.  A later world return carries no desired text:
//! it changes addressed morphology, and that sparse difference returns through the metric causal
//! adjoint before another emanation can occur.

use std::collections::BTreeSet;

use holonic_engine::{is_sha256_digest as is_sha256, ExactComplexWaveCurrent, ExactRatMatrix};
use serde::Serialize;
use thiserror::Error;

use super::{
    CausalAdjointStepInput, CausalAdjointWord, CausalOperationInvariant,
    MaterialFactorizationStanding, MaterialNativeFactorization, NativeConductedSection,
    SituatedCultivatedConductReturn, SituatedCultivatedEcologyRest,
};

mod exterior;
mod morphology;
mod potential;

use self::exterior::{exterior_clauses, realize_surface};
use self::morphology::{
    digest_json, exact_morphology_metric, hex_sha256, morphology_atoms, participant_identities,
    population_surface, rat, sparse_difference, unique_copy, unique_nonempty,
};
use self::potential::{condensation, native_potential};

pub const NATIVE_PROSE_POTENTIAL_SCHEMA: &str = "soma-life.native-prose-potential-complex.v1";
pub const SITUATED_EMANATION_DIFFERENCE_SCHEMA: &str = "soma-life.situated-emanation-difference.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EmanationDeed {
    Describe,
    Identify,
    Infer,
    Explain,
    Rewrite,
    Derive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EmanationVoice {
    Active,
    Passive,
    Copular,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EmanationParticipantRole {
    Speaker,
    Addressee,
    Referent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EmanationParticipant {
    pub occurrence: String,
    pub identity: String,
    /// Exterior proper-name face. It never enters a native potential address or identity.
    pub proper_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EmanationParticipantFace {
    pub participant_identity: String,
    pub role: EmanationParticipantRole,
    pub exterior_surface: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerspectiveChart {
    pub occurrence: String,
    pub speaker: Option<String>,
    pub addressee: Option<String>,
}

impl PerspectiveChart {
    pub fn found(
        occurrence: impl Into<String>,
        speaker: Option<String>,
        addressee: Option<String>,
    ) -> Result<Self, EmanationError> {
        let chart = Self {
            occurrence: occurrence.into(),
            speaker,
            addressee,
        };
        chart.validate()?;
        Ok(chart)
    }

    fn validate(&self) -> Result<(), EmanationError> {
        if self.occurrence.is_empty()
            || self.speaker.as_ref().is_some_and(String::is_empty)
            || self.addressee.as_ref().is_some_and(String::is_empty)
            || (self.speaker.is_some() && self.speaker == self.addressee)
        {
            return Err(EmanationError::Perspective);
        }
        Ok(())
    }

    fn face(&self, participant: &EmanationParticipant) -> EmanationParticipantFace {
        let (role, exterior_surface) = if self.speaker.as_deref() == Some(&participant.identity) {
            (EmanationParticipantRole::Speaker, "I".to_owned())
        } else if self.addressee.as_deref() == Some(&participant.identity) {
            (EmanationParticipantRole::Addressee, "you".to_owned())
        } else {
            (
                EmanationParticipantRole::Referent,
                participant.proper_name.clone(),
            )
        };
        EmanationParticipantFace {
            participant_identity: participant.identity.clone(),
            role,
            exterior_surface,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedEmanationIngress {
    pub occurrence: String,
    pub material_occurrence: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub predecessor_occurrence: Option<String>,
    pub subject_participant: String,
    pub participants: Vec<EmanationParticipant>,
    pub deed: EmanationDeed,
    pub modifiers: Vec<String>,
    pub perspective: PerspectiveChart,
    pub chronology: Vec<String>,
    pub open_ambiguity: Vec<String>,
    pub open_exterior: Vec<String>,
}

impl AddressedEmanationIngress {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        occurrence: impl Into<String>,
        material_occurrence: impl Into<String>,
        payload: &[u8],
        predecessor_occurrence: Option<String>,
        subject_participant: impl Into<String>,
        participants: Vec<EmanationParticipant>,
        deed: EmanationDeed,
        modifiers: Vec<String>,
        perspective: PerspectiveChart,
        chronology: Vec<String>,
        open_ambiguity: Vec<String>,
        open_exterior: Vec<String>,
    ) -> Result<Self, EmanationError> {
        let ingress = Self {
            occurrence: occurrence.into(),
            material_occurrence: material_occurrence.into(),
            payload_sha256: hex_sha256(payload),
            payload_octets: u64::try_from(payload.len()).map_err(|_| EmanationError::Extent)?,
            predecessor_occurrence,
            subject_participant: subject_participant.into(),
            participants,
            deed,
            modifiers,
            perspective,
            chronology,
            open_ambiguity,
            open_exterior,
        };
        ingress.validate()?;
        Ok(ingress)
    }

    fn validate(&self) -> Result<(), EmanationError> {
        self.perspective.validate()?;
        let identities = self
            .participants
            .iter()
            .map(|participant| participant.identity.as_str())
            .collect::<BTreeSet<_>>();
        let occurrences = self
            .participants
            .iter()
            .map(|participant| participant.occurrence.as_str())
            .collect::<BTreeSet<_>>();
        if self.occurrence.is_empty()
            || self.material_occurrence.is_empty()
            || !is_sha256(&self.payload_sha256)
            || self.payload_octets == 0
            || self.participants.is_empty()
            || identities.len() != self.participants.len()
            || occurrences.len() != self.participants.len()
            || !identities.contains(self.subject_participant.as_str())
            || self
                .perspective
                .speaker
                .as_deref()
                .is_some_and(|identity| !identities.contains(identity))
            || self
                .perspective
                .addressee
                .as_deref()
                .is_some_and(|identity| !identities.contains(identity))
            || self.participants.iter().any(|participant| {
                participant.occurrence.is_empty()
                    || participant.identity.is_empty()
                    || participant.proper_name.is_empty()
            })
            || self.chronology.is_empty()
            || !unique_nonempty(self.chronology.iter().map(String::as_str))
            || self.modifiers.iter().any(String::is_empty)
            || self.open_ambiguity.iter().any(String::is_empty)
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(EmanationError::Ingress);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativePotentialCellKind {
    Operation,
    Constraint,
    Geometry,
    ExactConsequence,
    SituatedFactor,
    SymmetricInteraction,
    CultivatedAffineTransport,
    Participant,
    Modifier,
    Chronology,
    OpenAmbiguity,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum NativePotentialCellBody {
    Operation {
        invariant: CausalOperationInvariant,
        entered_section: Vec<i64>,
        returned_section: Vec<i64>,
        exact_difference: Vec<i64>,
    },
    Constraint {
        orientation: Vec<i8>,
        exact_residual: i64,
        held: bool,
    },
    Geometry {
        vertices: Vec<(u32, i64, i64)>,
        constraint_incidence: Vec<i8>,
        transport_incidence: Vec<i8>,
    },
    ExactConsequence {
        returned_section: Vec<i64>,
        exact_residual: i64,
        fixed_section: bool,
    },
    SituatedFactor {
        coordinate: u32,
        coefficient: i64,
        current: ExactComplexWaveCurrent,
        incident_symmetric_population: usize,
    },
    SymmetricInteraction {
        current: ExactComplexWaveCurrent,
    },
    CultivatedAffineTransport {
        transport_identity_sha256: String,
        entering_section: Vec<i64>,
        addressed_landmark_population: usize,
        addressed_cell_population: usize,
        local_fibre_term_population: usize,
        every_cell_augments_to_entering_section: bool,
    },
    Participant {
        participant_identity: String,
    },
    Modifier {
        addressed_disturbance: String,
    },
    Chronology {
        predecessor: Option<String>,
        successor: String,
    },
    OpenAmbiguity {
        retained_fibre: String,
    },
}

impl NativePotentialCellBody {
    pub fn kind(&self) -> NativePotentialCellKind {
        match self {
            Self::Operation { .. } => NativePotentialCellKind::Operation,
            Self::Constraint { .. } => NativePotentialCellKind::Constraint,
            Self::Geometry { .. } => NativePotentialCellKind::Geometry,
            Self::ExactConsequence { .. } => NativePotentialCellKind::ExactConsequence,
            Self::SituatedFactor { .. } => NativePotentialCellKind::SituatedFactor,
            Self::SymmetricInteraction { .. } => NativePotentialCellKind::SymmetricInteraction,
            Self::CultivatedAffineTransport { .. } => {
                NativePotentialCellKind::CultivatedAffineTransport
            }
            Self::Participant { .. } => NativePotentialCellKind::Participant,
            Self::Modifier { .. } => NativePotentialCellKind::Modifier,
            Self::Chronology { .. } => NativePotentialCellKind::Chronology,
            Self::OpenAmbiguity { .. } => NativePotentialCellKind::OpenAmbiguity,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativePotentialCell {
    pub address: String,
    pub body: NativePotentialCellBody,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativePotentialContactKind {
    Constrains,
    Realizes,
    Supports,
    Couples,
    Presents,
    Precedes,
    LeavesOpen,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativePotentialContact {
    pub from: String,
    pub to: String,
    pub kind: NativePotentialContactKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeProsePotentialComplex {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_identity_sha256: String,
    pub material_occurrence: String,
    pub native_operation_identity_sha256: String,
    pub cells: Vec<NativePotentialCell>,
    pub contacts: Vec<NativePotentialContact>,
    pub native_sections: Vec<NativeConductedSection>,
    pub complete_reconstruction_fibre: Vec<String>,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EmanationCondensationReceipt {
    pub requested_future_receiver_family: BTreeSet<NativePotentialCellKind>,
    pub dependency_closed_family: BTreeSet<NativePotentialCellKind>,
    pub visible_cells: BTreeSet<String>,
    pub retained_hidden_fibre: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
struct EmanationMorphology {
    perspective: PerspectiveChart,
    voice: EmanationVoice,
    kind_order: Vec<NativePotentialCellKind>,
    condensation: EmanationCondensationReceipt,
    continuation_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EmanationSurface {
    pub occurrence: String,
    pub predecessor_body_identity_sha256: String,
    pub native_successor_identity_sha256: String,
    pub deed: EmanationDeed,
    pub participant_faces: Vec<EmanationParticipantFace>,
    pub native_clause_addresses: Vec<String>,
    pub text: String,
    pub text_sha256: String,
    pub text_octets: u64,
    pub hidden_reconstruction_fibre: BTreeSet<String>,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AddressedEmanationWorldReturn {
    pub occurrence: String,
    pub predecessor_emission_occurrence: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub deed: Option<EmanationDeed>,
    pub perspective: Option<PerspectiveChart>,
    pub voice: Option<EmanationVoice>,
    pub kind_order: Option<Vec<NativePotentialCellKind>>,
    pub future_receiver_family: Option<BTreeSet<NativePotentialCellKind>>,
    pub corrected_factorization: Option<MaterialNativeFactorization>,
    pub continuation_occurrence: Option<String>,
    pub open_exterior: Vec<String>,
}

impl AddressedEmanationWorldReturn {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        occurrence: impl Into<String>,
        predecessor_emission_occurrence: impl Into<String>,
        payload: &[u8],
        deed: Option<EmanationDeed>,
        perspective: Option<PerspectiveChart>,
        voice: Option<EmanationVoice>,
        kind_order: Option<Vec<NativePotentialCellKind>>,
        future_receiver_family: Option<BTreeSet<NativePotentialCellKind>>,
        corrected_factorization: Option<MaterialNativeFactorization>,
        continuation_occurrence: Option<String>,
        open_exterior: Vec<String>,
    ) -> Result<Self, EmanationError> {
        let returned = Self {
            occurrence: occurrence.into(),
            predecessor_emission_occurrence: predecessor_emission_occurrence.into(),
            payload_sha256: hex_sha256(payload),
            payload_octets: u64::try_from(payload.len()).map_err(|_| EmanationError::Extent)?,
            deed,
            perspective,
            voice,
            kind_order,
            future_receiver_family,
            corrected_factorization,
            continuation_occurrence,
            open_exterior,
        };
        returned.validate()?;
        Ok(returned)
    }

    fn validate(&self) -> Result<(), EmanationError> {
        if let Some(chart) = &self.perspective {
            chart.validate()?;
        }
        if self.occurrence.is_empty()
            || self.predecessor_emission_occurrence.is_empty()
            || !is_sha256(&self.payload_sha256)
            || self.payload_octets == 0
            || self
                .kind_order
                .as_ref()
                .is_some_and(|order| !unique_copy(order))
            || self
                .future_receiver_family
                .as_ref()
                .is_some_and(BTreeSet::is_empty)
            || self
                .continuation_occurrence
                .as_ref()
                .is_some_and(String::is_empty)
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(EmanationError::WorldReturn);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedEmanationDifference {
    pub schema: String,
    pub world_return_occurrence: String,
    pub predecessor_body_identity_sha256: String,
    pub successor_body_identity_sha256: String,
    pub candidate_potential_identity_sha256: String,
    pub returned_potential_identity_sha256: String,
    pub candidate_condensation: EmanationCondensationReceipt,
    pub returned_condensation: EmanationCondensationReceipt,
    pub addressed_basis: Vec<String>,
    pub candidate_coordinates: Vec<i64>,
    pub returned_coordinates: Vec<i64>,
    pub oriented_difference: Vec<i64>,
    pub changed_atoms: BTreeSet<String>,
    pub zero_difference_reconstruction_fibre: BTreeSet<String>,
    pub causal_adjoint: CausalAdjointWord,
    pub causal_content_preserved: bool,
    pub participant_lineage_preserved: bool,
    pub hidden_reconstruction_fibre: BTreeSet<String>,
    pub open_exterior: Vec<String>,
}

/// One live passage. The L2 rest is moved into this owner and cannot be used concurrently.
pub struct SituatedEmanationPassage<Standing = SituatedCultivatedEcologyRest> {
    rest: Standing,
    factorization: MaterialNativeFactorization,
    resident_return: SituatedCultivatedConductReturn,
    ingress: AddressedEmanationIngress,
    potential: NativeProsePotentialComplex,
    morphology: EmanationMorphology,
    open_emission: Option<(String, String)>,
    body_identity_sha256: String,
}

impl<Standing: MaterialFactorizationStanding> SituatedEmanationPassage<Standing> {
    pub fn found(
        rest: Standing,
        factorization: MaterialNativeFactorization,
        resident_return: SituatedCultivatedConductReturn,
        ingress: AddressedEmanationIngress,
    ) -> Result<Self, EmanationError> {
        rest.validate_material_standing()
            .map_err(EmanationError::Rest)?;
        ingress.validate()?;
        if factorization.predecessor_rest_identity_sha256 != rest.material_standing_identity()
            || resident_return.rest_identity_sha256 != rest.material_standing_identity()
            || factorization.material_occurrence != ingress.material_occurrence
            || factorization
                .cultivated_affine_transport
                .as_ref()
                .is_some_and(|transport| transport.resident_apparatus.is_none())
        {
            return Err(EmanationError::Lineage);
        }
        let potential = native_potential(&rest, &factorization, &resident_return, &ingress)?;
        let kinds = potential
            .cells
            .iter()
            .map(|cell| cell.body.kind())
            .collect::<BTreeSet<_>>();
        let morphology = EmanationMorphology {
            perspective: ingress.perspective.clone(),
            voice: EmanationVoice::Active,
            kind_order: kinds.iter().copied().collect(),
            condensation: condensation(&potential, kinds)?,
            continuation_occurrences: Vec::new(),
        };
        let mut passage = Self {
            rest,
            factorization,
            resident_return,
            ingress,
            potential,
            morphology,
            open_emission: None,
            body_identity_sha256: String::new(),
        };
        passage.body_identity_sha256 = passage.rederived_identity()?;
        passage.validate()?;
        Ok(passage)
    }

    pub fn body_identity(&self) -> &str {
        &self.body_identity_sha256
    }

    pub fn potential(&self) -> &NativeProsePotentialComplex {
        &self.potential
    }

    pub fn factorization(&self) -> &MaterialNativeFactorization {
        &self.factorization
    }

    pub fn ingress(&self) -> &AddressedEmanationIngress {
        &self.ingress
    }

    pub fn condensation_receipt(&self) -> &EmanationCondensationReceipt {
        &self.morphology.condensation
    }

    pub fn emanate(&mut self) -> Result<EmanationSurface, EmanationError> {
        self.validate()?;
        if self.open_emission.is_some() {
            return Err(EmanationError::OpenEmission);
        }
        let native_successor_identity_sha256 = digest_json(&(
            &self.potential.identity_sha256,
            self.ingress.deed,
            &self.morphology,
        ))?;
        let clauses = exterior_clauses(
            &self.potential,
            &self.factorization.invariant,
            &self.ingress,
            &self.morphology,
        )?;
        let realized = realize_surface(&clauses, self.morphology.voice)?;
        let text = realized.text;
        if text.trim().is_empty() {
            return Err(EmanationError::Surface(
                "the exterior codec returned no surface".to_owned(),
            ));
        }
        let occurrence = format!(
            "situated-emanation/{}/{}",
            self.ingress.occurrence,
            digest_json(&(&native_successor_identity_sha256, &text))?
        );
        let participant_faces = self
            .ingress
            .participants
            .iter()
            .map(|participant| self.morphology.perspective.face(participant))
            .collect::<Vec<_>>();
        let surface = EmanationSurface {
            occurrence: occurrence.clone(),
            predecessor_body_identity_sha256: self.body_identity_sha256.clone(),
            native_successor_identity_sha256: native_successor_identity_sha256.clone(),
            deed: self.ingress.deed,
            participant_faces,
            native_clause_addresses: clauses
                .iter()
                .map(|clause| clause.identity.clone())
                .collect(),
            text_sha256: hex_sha256(text.as_bytes()),
            text_octets: u64::try_from(text.len()).map_err(|_| EmanationError::Extent)?,
            text,
            hidden_reconstruction_fibre: self.morphology.condensation.retained_hidden_fibre.clone(),
            open_exterior: self.potential.open_exterior.clone(),
        };
        self.open_emission = Some((occurrence, native_successor_identity_sha256));
        Ok(surface)
    }

    pub fn receive_world_return(
        &mut self,
        returned: AddressedEmanationWorldReturn,
    ) -> Result<SituatedEmanationDifference, EmanationError> {
        returned.validate()?;
        let Some((emission_occurrence, _)) = self.open_emission.take() else {
            return Err(EmanationError::NoOpenEmission);
        };
        if returned.predecessor_emission_occurrence != emission_occurrence {
            self.open_emission = Some((emission_occurrence, String::new()));
            return Err(EmanationError::Lineage);
        }
        let predecessor_body_identity_sha256 = self.body_identity_sha256.clone();
        let candidate_potential_identity_sha256 = self.potential.identity_sha256.clone();
        let candidate_condensation = self.morphology.condensation.clone();
        let candidate_atoms =
            morphology_atoms(&self.potential, &self.morphology, self.ingress.deed);
        let prior_operation = self.factorization.native_operation_identity_sha256.clone();
        let prior_participants = participant_identities(&self.ingress);

        if let Some(deed) = returned.deed {
            self.ingress.deed = deed;
        }
        if let Some(factorization) = returned.corrected_factorization {
            if factorization.predecessor_rest_identity_sha256
                != self.rest.material_standing_identity()
            {
                return Err(EmanationError::Lineage);
            }
            self.potential = native_potential(
                &self.rest,
                &factorization,
                &self.resident_return,
                &self.ingress,
            )?;
            self.factorization = factorization;
        }
        if let Some(perspective) = returned.perspective {
            perspective.validate()?;
            self.morphology.perspective = perspective;
        }
        if let Some(voice) = returned.voice {
            self.morphology.voice = voice;
        }
        if let Some(order) = returned.kind_order {
            let present = self
                .potential
                .cells
                .iter()
                .map(|cell| cell.body.kind())
                .collect::<BTreeSet<_>>();
            if order.iter().copied().collect::<BTreeSet<_>>() != present {
                return Err(EmanationError::Ordering);
            }
            self.morphology.kind_order = order;
        } else {
            let present = self
                .potential
                .cells
                .iter()
                .map(|cell| cell.body.kind())
                .collect::<BTreeSet<_>>();
            self.morphology
                .kind_order
                .retain(|kind| present.contains(kind));
            let missing = present
                .into_iter()
                .filter(|kind| !self.morphology.kind_order.contains(kind))
                .collect::<Vec<_>>();
            self.morphology.kind_order.extend(missing);
        }
        if let Some(family) = returned.future_receiver_family {
            self.morphology.condensation = condensation(&self.potential, family)?;
        } else if !self
            .morphology
            .condensation
            .visible_cells
            .iter()
            .all(|address| {
                self.potential
                    .cells
                    .iter()
                    .any(|cell| &cell.address == address)
            })
        {
            let family = self
                .morphology
                .condensation
                .requested_future_receiver_family
                .clone();
            self.morphology.condensation = condensation(&self.potential, family)?;
        }
        if let Some(continuation) = returned.continuation_occurrence {
            if self
                .morphology
                .continuation_occurrences
                .contains(&continuation)
            {
                return Err(EmanationError::WorldReturn);
            }
            self.morphology.continuation_occurrences.push(continuation);
        }

        let returned_atoms = morphology_atoms(&self.potential, &self.morphology, self.ingress.deed);
        let (
            addressed_basis,
            candidate_coordinates,
            returned_coordinates,
            oriented_difference,
            zero_difference_reconstruction_fibre,
        ) = sparse_difference(&candidate_atoms, &returned_atoms)?;
        if oriented_difference
            .iter()
            .all(|coefficient| *coefficient == 0)
        {
            return Err(EmanationError::ZeroDifference);
        }
        let rank = addressed_basis.len();
        let metric = exact_morphology_metric(&candidate_coordinates, &returned_coordinates)?;
        let causal_adjoint = CausalAdjointWord::found(
            vec![CausalAdjointStepInput {
                name: format!("receiver-world-return/{}", returned.occurrence),
                forward: ExactRatMatrix::identity(rank)
                    .map_err(|error| EmanationError::Difference(error.to_string()))?,
                domain_metric: metric.clone(),
                codomain_metric: metric,
            }],
            oriented_difference.iter().copied().map(rat).collect(),
        )
        .map_err(|error| EmanationError::Difference(error.to_string()))?;
        let changed_atoms = addressed_basis
            .iter()
            .zip(&oriented_difference)
            .filter_map(|(address, difference)| (*difference != 0).then_some(address.clone()))
            .collect::<BTreeSet<_>>();
        let causal_content_preserved =
            prior_operation == self.factorization.native_operation_identity_sha256;
        let participant_lineage_preserved =
            prior_participants == participant_identities(&self.ingress);
        let mut open_exterior = self.potential.open_exterior.clone();
        open_exterior.extend(returned.open_exterior);
        open_exterior.sort();
        open_exterior.dedup();
        self.body_identity_sha256 = self.rederived_identity()?;
        let difference = SituatedEmanationDifference {
            schema: SITUATED_EMANATION_DIFFERENCE_SCHEMA.to_owned(),
            world_return_occurrence: returned.occurrence,
            predecessor_body_identity_sha256,
            successor_body_identity_sha256: self.body_identity_sha256.clone(),
            candidate_potential_identity_sha256,
            returned_potential_identity_sha256: self.potential.identity_sha256.clone(),
            candidate_condensation,
            returned_condensation: self.morphology.condensation.clone(),
            addressed_basis,
            candidate_coordinates,
            returned_coordinates,
            oriented_difference,
            changed_atoms,
            zero_difference_reconstruction_fibre,
            causal_adjoint,
            causal_content_preserved,
            participant_lineage_preserved,
            hidden_reconstruction_fibre: self.morphology.condensation.retained_hidden_fibre.clone(),
            open_exterior,
        };
        self.validate()?;
        Ok(difference)
    }

    pub fn into_rest(self) -> Result<Standing, EmanationError> {
        if self.open_emission.is_some() {
            return Err(EmanationError::OpenEmission);
        }
        if !self.morphology.continuation_occurrences.is_empty() {
            return Err(EmanationError::UncommittedReturn);
        }
        Ok(self.rest)
    }

    fn validate(&self) -> Result<(), EmanationError> {
        self.rest
            .validate_material_standing()
            .map_err(EmanationError::Rest)?;
        self.ingress.validate()?;
        if self.factorization.predecessor_rest_identity_sha256
            != self.rest.material_standing_identity()
            || self.factorization.material_occurrence != self.ingress.material_occurrence
            || self.resident_return.rest_identity_sha256 != self.rest.material_standing_identity()
            || self
                .factorization
                .cultivated_affine_transport
                .as_ref()
                .is_some_and(|transport| transport.resident_apparatus.is_none())
            || self.potential.predecessor_rest_identity_sha256
                != self.rest.material_standing_identity()
            || self.body_identity_sha256 != self.rederived_identity()?
        {
            return Err(EmanationError::Lineage);
        }
        let addresses = self
            .potential
            .cells
            .iter()
            .map(|cell| cell.address.as_str())
            .collect::<BTreeSet<_>>();
        if addresses.len() != self.potential.cells.len()
            || self.potential.contacts.iter().any(|contact| {
                !addresses.contains(contact.from.as_str())
                    || !addresses.contains(contact.to.as_str())
            })
            || self
                .morphology
                .condensation
                .visible_cells
                .iter()
                .any(|cell| !addresses.contains(cell.as_str()))
            || self
                .morphology
                .condensation
                .retained_hidden_fibre
                .iter()
                .any(|cell| !addresses.contains(cell.as_str()))
        {
            return Err(EmanationError::Potential);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, EmanationError> {
        digest_json(&(
            self.rest.material_standing_identity(),
            &self.factorization.native_operation_identity_sha256,
            &self.potential.identity_sha256,
            &self.ingress.occurrence,
            self.ingress.deed,
            &self.morphology,
        ))
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum EmanationError {
    #[error("the situated rest refused emanation: {0}")]
    Rest(String),
    #[error("the complete addressed ingress is malformed")]
    Ingress,
    #[error("the perspective chart is malformed")]
    Perspective,
    #[error("the factorization, ingress, resident return, and rest do not share lineage")]
    Lineage,
    #[error("the resident current is incomplete: {0}")]
    Resident(String),
    #[error("the transient native potential is malformed")]
    Potential,
    #[error("the native addressed section is unavailable: {0}")]
    NativeSection(String),
    #[error("the boundary condensation does not factor the requested receiver family")]
    Condensation,
    #[error("the returned ordering is not the complete potential-kind population")]
    Ordering,
    #[error("the exterior surface codec refused: {0}")]
    Surface(String),
    #[error("an emanation remains open and must receive a return")]
    OpenEmission,
    #[error("no emanation is open for this world return")]
    NoOpenEmission,
    #[error("the addressed world return is malformed")]
    WorldReturn,
    #[error("the returned morphology did not change")]
    ZeroDifference,
    #[error("an admitted world return must cultivate the continuing rest before release")]
    UncommittedReturn,
    #[error("the complete situated difference refused: {0}")]
    Difference(String),
    #[error("an extent exceeded the exterior apparatus chart")]
    Extent,
    #[error("the emanation wire refused: {0}")]
    Wire(String),
}

#[cfg(test)]
mod tests;
