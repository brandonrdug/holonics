//! Durable return through the singular Athena membrane.
//!
//! The membrane's resident radiation is re-entered as a genuinely later exterior occurrence,
//! pulled back through the addressed native passage, and retained as one complete situated
//! difference.  Staging owns the sole predecessor and the exact source fibre.  Commit consumes
//! both into a source-detached successor; decline returns them unchanged.

use std::collections::BTreeSet;

use holonic_engine::{
    cuda_refine::ResidentMembraneInteriorReturn,
    native_spool::{
        NativeCollapsedFibre, NativeConstitutiveResponse, NativeIncidenceTerm,
        NativePullbackOccurrence, NativeThreadHand,
    },
    ExactRatMatrix, OccurrencePort,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{
    AdmittedAthenaMembraneStanding, AffineLaboratoryCultivatedAthenaRest, AthenaCausalMembrane,
    AthenaMembraneReturn, AthenaMembraneStanding, CausalAdjointStepInput,
    RecurrentReturnedAffineLaboratoryAthenaRest, ReturnedAffineLaboratoryAthenaRest,
    SituatedDifferenceInput, SituatedDifferenceSection,
};

pub const MEMBRANE_CULTIVATION_SCHEMA: &str = "soma-life.athena-membrane-cultivation.v1";
pub const DETACHED_MEMBRANE_CULTIVATION_SCHEMA: &str =
    "soma-life.detached-athena-membrane-cultivation.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MembraneCultivationReceipt {
    pub schema: String,
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub situated_difference_identity_sha256: String,
    pub exterior_world_return_occurrence: String,
    pub exterior_world_return_event: holonic_engine::EventId,
    pub carrying_occurrence: NativePullbackOccurrence,
    pub actual_native_word: Vec<holonic_engine::receiver_exact_compression::InputId>,
    pub winding_rank: usize,
    pub winding_section: Vec<Rat>,
    pub returned_source_covector: Vec<Rat>,
    pub exact_source_fibre_departed_before_rest: bool,
    pub source_access_after_commit: bool,
    pub query_selected_developmental_population: bool,
    pub expected_surface_entered_the_law: bool,
    pub fixed_behavioral_extent_supplied: bool,
    pub open_exterior: Vec<String>,
}

/// The uncommitted boundary passage.  It is a type-state owner, not a rollback copy: there is one
/// predecessor inside `membrane`, and one move-owned later occurrence inside `world_return`.
pub struct StagedMembraneCultivation<Standing = AffineLaboratoryCultivatedAthenaRest> {
    membrane: AthenaCausalMembrane<Standing>,
    world_return: AthenaMembraneReturn,
    resident_return: ResidentMembraneInteriorReturn,
    difference: SituatedDifferenceSection,
}

/// Source-detached, restable continuation between an admitted membrane return and its durable
/// morphology deposit. This is an apparatus rebase of one staged passage, not a second learner or
/// a history store. Its predecessor identity and complete difference must both match at commit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DetachedMembraneCultivation {
    schema: String,
    predecessor_rest_identity_sha256: String,
    exterior_world_return_occurrence: String,
    exterior_world_return_event: holonic_engine::EventId,
    actual_native_word: Vec<holonic_engine::receiver_exact_compression::InputId>,
    difference: SituatedDifferenceSection,
    open_exterior: Vec<String>,
}

impl DetachedMembraneCultivation {
    pub fn read(bytes: &[u8]) -> Result<Self, MembraneCultivationError> {
        let detached: Self = serde_json::from_slice(bytes)
            .map_err(|error| MembraneCultivationError::Lineage(error.to_string()))?;
        detached.validate()?;
        Ok(detached)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, MembraneCultivationError> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| MembraneCultivationError::Lineage(error.to_string()))
    }

    pub fn predecessor_identity(&self) -> &str {
        &self.predecessor_rest_identity_sha256
    }

    pub fn difference(&self) -> &SituatedDifferenceSection {
        &self.difference
    }

    fn validate(&self) -> Result<(), MembraneCultivationError> {
        self.difference
            .validate()
            .map_err(|error| MembraneCultivationError::Difference(error.to_string()))?;
        if self.schema != DETACHED_MEMBRANE_CULTIVATION_SCHEMA
            || self.predecessor_rest_identity_sha256.len() != 64
            || !self
                .predecessor_rest_identity_sha256
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
            || self.exterior_world_return_occurrence.is_empty()
            || self.actual_native_word.is_empty()
            || self.actual_native_word != self.difference.candidate.ordered_word
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(MembraneCultivationError::Lineage(
                "the detached membrane passage lost its exact return lineage".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn commit<Standing: MembraneDifferenceStanding>(
        self,
        predecessor: Standing,
    ) -> Result<(Standing::Successor, MembraneCultivationReceipt), MembraneCultivationError> {
        self.validate()?;
        if predecessor.membrane_identity() != self.predecessor_rest_identity_sha256 {
            return Err(MembraneCultivationError::Lineage(
                "the detached return was offered to another rested Athena body".to_owned(),
            ));
        }
        let carrying_occurrence = self.difference.carrying_occurrence;
        let difference_identity = self.difference.identity_sha256.clone();
        let winding_section = self.difference.chart.returned_coordinates.clone();
        let returned_source_covector = self
            .difference
            .causal_adjoint
            .returned_source_covector
            .clone();
        let winding_rank = winding_section.len();
        let successor = predecessor
            .deposit_membrane_difference(self.difference)
            .map_err(MembraneCultivationError::Cultivation)?;
        let receipt = MembraneCultivationReceipt {
            schema: MEMBRANE_CULTIVATION_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: self.predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: successor.membrane_identity().to_owned(),
            situated_difference_identity_sha256: difference_identity,
            exterior_world_return_occurrence: self.exterior_world_return_occurrence,
            exterior_world_return_event: self.exterior_world_return_event,
            carrying_occurrence,
            actual_native_word: self.actual_native_word,
            winding_rank,
            winding_section,
            returned_source_covector,
            exact_source_fibre_departed_before_rest: true,
            source_access_after_commit: false,
            query_selected_developmental_population: false,
            expected_surface_entered_the_law: false,
            fixed_behavioral_extent_supplied: false,
            open_exterior: self.open_exterior,
        };
        Ok((successor, receipt))
    }

    /// Commit and serialize the successor immediately after its complete transition validation.
    /// This avoids replaying the same cold validation merely to cross an apparatus storage cut;
    /// `read` still revalidates the complete wire at remount.
    pub fn commit_restable<Standing: MembraneDifferenceStanding>(
        self,
        predecessor: Standing,
    ) -> Result<(Standing::Successor, MembraneCultivationReceipt, Vec<u8>), MembraneCultivationError>
    where
        Standing::Successor: Serialize,
    {
        let (successor, receipt) = self.commit(predecessor)?;
        let wire = serde_json::to_vec(&successor)
            .map_err(|error| MembraneCultivationError::Cultivation(error.to_string()))?;
        Ok((successor, receipt, wire))
    }
}

impl<Standing: AthenaMembraneStanding> StagedMembraneCultivation<Standing> {
    pub fn found(
        membrane: AthenaCausalMembrane<Standing>,
        world_return: AthenaMembraneReturn,
        resident_return: ResidentMembraneInteriorReturn,
    ) -> Result<Self, MembraneCultivationError> {
        let trace = holonic_engine::cuda_refine::trace_configuration().holonics_phase_trace;
        let began = std::time::Instant::now();
        let rest = membrane.rested_body();
        let interior = membrane
            .interior()
            .ok_or(MembraneCultivationError::InteriorAbsent)?;
        if world_return.receipt.rested_identity_sha256 != rest.membrane_identity()
            || world_return.occurrence.rested_identity_sha256 != rest.membrane_identity()
            || world_return
                .occurrence
                .exterior
                .address()
                .predecessor
                .is_none()
            || world_return.occurrence.chart.transported_current
                != resident_return.returned_radiation
            || resident_return.native_radiation.is_zero()
            || resident_return.returned_radiation.is_zero()
            || !resident_return.boundary_injection_depended_on_native_radiation
            || resident_return.invariant_transport_reuploaded
            || resident_return.cpu_semantic_replay_after_device
            || resident_return.cell_selected_or_ranked
        {
            return Err(MembraneCultivationError::Lineage(
                "the later occurrence is not the exact re-entry of this membrane radiation"
                    .to_owned(),
            ));
        }

        let candidate = world_return.occurrence.native.clone();
        let returned_event = world_return.occurrence.exterior.address().event_projection;
        let returned_coefficient = candidate
            .incidence
            .coefficient
            .checked_neg()
            .ok_or(MembraneCultivationError::Extent)?;
        let returned_section = candidate
            .entering_section
            .add(&resident_return.native_radiation);
        let returned_current = candidate
            .entering_current
            .add(&resident_return.returned_radiation);
        let fibre = BTreeSet::from([candidate.address.occurrence, returned_event]);
        let returned = super::NativeConductedSection {
            address: super::NativeSectionAddress {
                spool: candidate.address.spool.clone(),
                thread: format!(
                    "native-membrane-return/{}",
                    world_return
                        .occurrence
                        .exterior
                        .address()
                        .incidence_identity_sha256
                ),
                occurrence: returned_event,
            },
            predecessor: Some(candidate.address.occurrence),
            entering_boundary: candidate.emitting_boundary,
            emitting_boundary: candidate.entering_boundary,
            entering_port: OccurrencePort::input(returned_event, 0),
            emitting_port: OccurrencePort::output(returned_event, 0),
            entering_native: candidate.emitting_native,
            emitting_native: candidate.entering_native,
            incidence: NativeIncidenceTerm {
                occurrence: returned_event,
                from: candidate.emitting_native,
                to: candidate.entering_native,
                coefficient: returned_coefficient,
            },
            entering_section: candidate.emitting_section.clone(),
            entering_current: candidate.emitting_current.clone(),
            emitting_section: returned_section.clone(),
            emitting_current: returned_current.clone(),
            relative_phase: candidate.relative_phase.clone(),
            hand: match candidate.hand {
                NativeThreadHand::Along => NativeThreadHand::Against,
                NativeThreadHand::Against => NativeThreadHand::Along,
            },
            constitutive_response: NativeConstitutiveResponse {
                native: candidate.entering_native,
                receiver: candidate.receiver,
                presented: returned_section,
                stored: returned_current,
            },
            mutual_constitutive_responses: Vec::new(),
            ordered_word: candidate.ordered_word.clone(),
            receiver: candidate.receiver,
            observation: candidate.observation,
            reconstruction_fibre: fibre.clone(),
            successor_sections: Vec::new(),
            open_exterior: vec![
                "receiver histories outside the admitted membrane return remain open".to_owned(),
            ],
        };

        let winding = interior
            .returned_winding_section(rest, &resident_return.family_overlaps)
            .map_err(|error| MembraneCultivationError::Interior(error.to_string()))?;
        if trace {
            eprintln!("sens6-cultivation winding-returned {:?}", began.elapsed());
        }
        let metric = interior
            .winding_metric(rest)
            .map_err(|error| MembraneCultivationError::Interior(error.to_string()))?;
        if trace {
            eprintln!("sens6-cultivation winding-metric {:?}", began.elapsed());
        }
        let rank = interior.winding_rank();
        let identity = ExactRatMatrix::identity(rank)
            .map_err(|error| MembraneCultivationError::Linear(error.to_string()))?;
        let candidate_incidence = scalar_identity(rank, candidate.incidence.coefficient)?;
        let returned_incidence = scalar_identity(rank, returned_coefficient)?;
        let mut adjoint_steps = Vec::with_capacity(candidate.ordered_word.len() + 3);
        adjoint_steps.push(CausalAdjointStepInput {
            name: format!("candidate-incidence/{}", candidate.address.occurrence.0),
            forward: candidate_incidence,
            domain_metric: metric.clone(),
            codomain_metric: metric.clone(),
        });
        for generator in &candidate.ordered_word {
            adjoint_steps.push(CausalAdjointStepInput {
                name: format!("native-ordered-generator/{}", generator.0),
                forward: identity.clone(),
                domain_metric: metric.clone(),
                codomain_metric: metric.clone(),
            });
        }
        adjoint_steps.push(CausalAdjointStepInput {
            name: format!(
                "resident-membrane-return/{}/{}",
                resident_return.left_cell, resident_return.right_cell
            ),
            forward: identity.clone(),
            domain_metric: metric.clone(),
            codomain_metric: metric.clone(),
        });
        adjoint_steps.push(CausalAdjointStepInput {
            name: format!("returned-incidence/{}", returned_event.0),
            forward: returned_incidence,
            domain_metric: metric.clone(),
            codomain_metric: metric,
        });
        let carrying_occurrence = NativePullbackOccurrence {
            left: candidate.address.occurrence,
            right: returned_event,
            joining_native: candidate.emitting_native,
        };
        let mut open_exterior = world_return.receipt.open_exterior.clone();
        open_exterior.push(
            "the complete exterior source fibre departs before the successor becomes rest"
                .to_owned(),
        );
        open_exterior.sort();
        open_exterior.dedup();
        let difference = SituatedDifferenceSection::found(SituatedDifferenceInput {
            candidate,
            returned,
            carrying_occurrence,
            occurrence_fibres: vec![NativeCollapsedFibre {
                native: carrying_occurrence.joining_native,
                occurrences: fibre,
            }],
            source_transport: identity.clone(),
            rebased_transport: identity.clone(),
            source_chart: identity.clone(),
            target_chart: identity,
            candidate_coordinates: vec![rat(0); rank],
            returned_coordinates: winding.clone(),
            adjoint_steps,
            terminal_covector: winding,
            native_obstructions: Vec::new(),
            open_deposition_boundary: format!("athena-membrane-deposition/{}", returned_event.0),
            open_exterior,
        })
        .map_err(|error| MembraneCultivationError::Difference(error.to_string()))?;
        if trace {
            eprintln!("sens6-cultivation difference-founded {:?}", began.elapsed());
        }
        Ok(Self {
            membrane,
            world_return,
            resident_return,
            difference,
        })
    }

    pub fn difference(&self) -> &SituatedDifferenceSection {
        &self.difference
    }

    /// Decline before mutation and recover the exact predecessor, source fibre, resident return,
    /// and staged difference testimony.
    pub fn decline(
        self,
    ) -> (
        AthenaCausalMembrane<Standing>,
        AthenaMembraneReturn,
        ResidentMembraneInteriorReturn,
        SituatedDifferenceSection,
    ) {
        (
            self.membrane,
            self.world_return,
            self.resident_return,
            self.difference,
        )
    }

    /// Close the source-bearing stage at an apparatus boundary. The complete exterior fibre and
    /// resident device return depart here; only the exact predecessor and returned difference may
    /// be rested and later recomposed.
    pub fn detach(
        self,
    ) -> Result<(Standing, DetachedMembraneCultivation), MembraneCultivationError> {
        let predecessor_rest_identity_sha256 =
            self.membrane.rested_body().membrane_identity().to_owned();
        let exterior_world_return_occurrence = self
            .world_return
            .occurrence
            .exterior
            .address()
            .occurrence
            .clone();
        let exterior_world_return_event = self
            .world_return
            .occurrence
            .exterior
            .address()
            .event_projection;
        let actual_native_word = self.world_return.receipt.native_ordered_word.clone();
        let mut open_exterior = self.difference.open_exterior.clone();
        open_exterior.extend(self.world_return.receipt.open_exterior.iter().cloned());
        open_exterior.sort();
        open_exterior.dedup();
        drop(self.world_return);
        drop(self.resident_return);
        let predecessor = self.membrane.into_rest();
        let detached = DetachedMembraneCultivation {
            schema: DETACHED_MEMBRANE_CULTIVATION_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256,
            exterior_world_return_occurrence,
            exterior_world_return_event,
            actual_native_word,
            difference: self.difference,
            open_exterior,
        };
        detached.validate()?;
        Ok((predecessor, detached))
    }
}

/// One standing which can consume a complete situated difference into a causally later native
/// rest. The associated successor keeps the type-state transition exact without requiring one
/// authored training subsystem for every exterior material family.
pub trait MembraneDifferenceStanding: AthenaMembraneStanding + Sized {
    type Successor: AthenaMembraneStanding;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String>;
}

impl MembraneDifferenceStanding for AffineLaboratoryCultivatedAthenaRest {
    type Successor = ReturnedAffineLaboratoryAthenaRest;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        self.deposit_returned_difference(difference)
            .map_err(|error| error.to_string())
    }
}

impl<Standing: MembraneDifferenceStanding> MembraneDifferenceStanding
    for AdmittedAthenaMembraneStanding<Standing>
{
    type Successor = Standing::Successor;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        self.into_inner().deposit_membrane_difference(difference)
    }
}

impl MembraneDifferenceStanding for ReturnedAffineLaboratoryAthenaRest {
    type Successor = RecurrentReturnedAffineLaboratoryAthenaRest;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        self.deposit_additional_returned_difference(difference)
            .map_err(|error| error.to_string())
    }
}

impl MembraneDifferenceStanding for RecurrentReturnedAffineLaboratoryAthenaRest {
    type Successor = Self;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        self.deposit_additional_returned_difference(difference)
            .map_err(|error| error.to_string())
    }
}

impl<Standing: MembraneDifferenceStanding> StagedMembraneCultivation<Standing> {
    /// Commit consumes the predecessor and the complete exterior fibre. Only cold address
    /// testimony enters the receipt; the successor type has no source-fibre field or access path.
    pub fn commit(
        self,
    ) -> Result<(Standing::Successor, MembraneCultivationReceipt), MembraneCultivationError> {
        let (predecessor, detached) = self.detach()?;
        detached.commit(predecessor)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MembraneCultivationError {
    #[error("the morphology-derived membrane interior is absent")]
    InteriorAbsent,
    #[error("the returned membrane lineage is malformed: {0}")]
    Lineage(String),
    #[error("the membrane interior refused the returned action: {0}")]
    Interior(String),
    #[error("the exact winding carrier refused: {0}")]
    Linear(String),
    #[error("the situated difference refused: {0}")]
    Difference(String),
    #[error("the durable cultivation passage refused: {0}")]
    Cultivation(String),
    #[error("the returned incidence escaped its exact integer carrier")]
    Extent,
}

fn scalar_identity(
    rank: usize,
    coefficient: i64,
) -> Result<ExactRatMatrix, MembraneCultivationError> {
    ExactRatMatrix::from_diagonal(vec![rat(coefficient); rank])
        .map_err(|error| MembraneCultivationError::Linear(error.to_string()))
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}
