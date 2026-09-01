//! Source-neutral addressed threads and reusable native spool complexes.
//!
//! This module owns only the native side of a realization boundary.  It has no source-model
//! identity, tensor coordinate, executor, ancestry witness, or callable reconstruction edge.  A
//! thread retains the full occurrence span rather than reducing a passage to its endpoints; a
//! spool retains the exact serial pullbacks, native generator action, receiver factors, complete
//! occurrence fibres, and any lawful interchange through which that passage can be reused.

use super::helpers::{validate_interchange, validate_pullback};
use super::refusal::NativeSpoolRefusal;

use std::collections::{BTreeMap, BTreeSet};

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::{
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort, PortHand,
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
};

pub const NATIVE_THREAD_SCHEMA: &str = "holonic-engine.native-thread.v1";
pub const NATIVE_SPOOL_SCHEMA: &str = "holonic-engine.native-spool.v2";
pub const NATIVE_SPOOL_BUNDLE_SCHEMA: &str = "holonic-engine.native-spool-bundle.v2";
pub const NATIVE_THREAD_DEPOSIT_SCHEMA: &str = "holonic-engine.native-thread-deposit.v1";
pub const NATIVE_THREAD_DEPOSIT_RECEIPT_SCHEMA: &str =
    "holonic-engine.native-thread-deposit-receipt.v1";
pub const NATIVE_THREAD_DEPOSIT_BATCH_RECEIPT_SCHEMA: &str =
    "holonic-engine.native-thread-deposit-batch-receipt.v1";
pub const NATIVE_SITUATED_SPOOL_BUNDLE_SCHEMA: &str =
    "holonic-engine.native-situated-spool-bundle.v1";
pub const RECEIVER_INSUFFICIENCY_SCHEMA: &str = "holonic-engine.receiver-insufficiency.v1";

/// One carrying occurrence in the population `W_f` of an addressed span.
///
/// `entering_native` and `emitting_native` are the two boundary maps.  They are retained per
/// occurrence even when several occurrences have equal endpoint states.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadOccurrence {
    pub occurrence: EventId,
    pub predecessor: Option<EventId>,
    pub entering_port: OccurrencePort,
    pub emitting_port: OccurrencePort,
    pub entering_native: NativeStateId,
    pub emitting_native: NativeStateId,
}

/// One oriented native incidence term carried by an occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeIncidenceTerm {
    pub occurrence: EventId,
    pub from: NativeStateId,
    pub to: NativeStateId,
    pub coefficient: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeThreadHand {
    Along,
    Against,
}

/// The local Complex-Parametron section and current at one native cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeParametronCell {
    pub native: NativeStateId,
    pub section: ExactComplexWaveCurrent,
    pub current: ExactComplexWaveCurrent,
    pub relative_phase: ExactUnitConicPhase,
    pub hand: NativeThreadHand,
}

/// One receiver-indexed constitutive response.  The relation is retained as an exact presented
/// current and exact stored response rather than a scalar score.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConstitutiveResponse {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub presented: ExactComplexWaveCurrent,
    pub stored: ExactComplexWaveCurrent,
}

/// One exact off-diagonal storage term of the receiver constitutive form. It is caused contact
/// between two addressed occurrences, not an inference from co-presence or equal output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMutualConstitutiveResponse {
    pub left_occurrence: EventId,
    pub right_occurrence: EventId,
    pub left_native: NativeStateId,
    pub right_native: NativeStateId,
    pub receiver: ReceiverId,
    pub storage: Rat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeReceiverConsequence {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
}

/// An obstruction returned by the native passage itself.  It contains only native states and
/// receiver addresses; any ancestry needed to revisit the boundary remains exterior.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadObstruction {
    pub boundary: BoundaryId,
    pub receiver: Option<ReceiverId>,
    pub reason: String,
    pub retained_native_fibre: BTreeSet<NativeStateId>,
}

/// One complete source-neutral addressed passage `X <- W_f -> Y`.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThread {
    pub schema: String,
    pub address: String,
    pub entering_boundary: BoundaryId,
    pub emitting_boundary: BoundaryId,
    pub entering_carrier: String,
    pub emitting_carrier: String,
    pub occurrences: Vec<NativeThreadOccurrence>,
    pub native_support: BTreeSet<NativeStateId>,
    pub incidence: Vec<NativeIncidenceTerm>,
    pub parametrons: Vec<NativeParametronCell>,
    pub constitutive_responses: Vec<NativeConstitutiveResponse>,
    pub chronology: Vec<InputId>,
    pub receiver_consequences: Vec<NativeReceiverConsequence>,
    pub obstruction: Option<NativeThreadObstruction>,
    pub open_exterior: Vec<String>,
    pub reconstruction_fibre: BTreeSet<EventId>,
}

impl NativeThread {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_THREAD_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.address.is_empty()
            || self.entering_carrier.is_empty()
            || self.emitting_carrier.is_empty()
            || self.occurrences.is_empty()
            || self.native_support.is_empty()
            || self.incidence.is_empty()
            || self.parametrons.is_empty()
            || self.constitutive_responses.is_empty()
            || self.chronology.is_empty()
            || self.receiver_consequences.is_empty()
        {
            return Err(NativeSpoolRefusal::MalformedThread(self.address.clone()));
        }

        let mut occurrence_by_id = BTreeMap::new();
        for occurrence in &self.occurrences {
            if occurrence_by_id
                .insert(occurrence.occurrence, occurrence)
                .is_some()
                || occurrence.predecessor == Some(occurrence.occurrence)
                || occurrence.entering_port.event != occurrence.occurrence
                || occurrence.entering_port.hand != PortHand::Input
                || occurrence.emitting_port.event != occurrence.occurrence
                || occurrence.emitting_port.hand != PortHand::Output
                || !self.native_support.contains(&occurrence.entering_native)
                || !self.native_support.contains(&occurrence.emitting_native)
            {
                return Err(NativeSpoolRefusal::Occurrence(self.address.clone()));
            }
        }
        let occurrence_ids = occurrence_by_id.keys().copied().collect::<BTreeSet<_>>();
        if occurrence_ids != self.reconstruction_fibre {
            return Err(NativeSpoolRefusal::ReconstructionFibre(
                self.address.clone(),
            ));
        }

        let mut incidence_occurrences = BTreeSet::new();
        for incidence in &self.incidence {
            let Some(occurrence) = occurrence_by_id.get(&incidence.occurrence).copied() else {
                return Err(NativeSpoolRefusal::Incidence(self.address.clone()));
            };
            if incidence.coefficient == 0
                || incidence.from != occurrence.entering_native
                || incidence.to != occurrence.emitting_native
            {
                return Err(NativeSpoolRefusal::Incidence(self.address.clone()));
            }
            incidence_occurrences.insert(incidence.occurrence);
        }
        if incidence_occurrences != occurrence_ids {
            return Err(NativeSpoolRefusal::Incidence(self.address.clone()));
        }

        let mut parametron_states = BTreeSet::new();
        let mut productive = false;
        for cell in &self.parametrons {
            if !self.native_support.contains(&cell.native)
                || !parametron_states.insert(cell.native)
                || !cell.relative_phase.is_unit()
            {
                return Err(NativeSpoolRefusal::Parametron(self.address.clone()));
            }
            productive |= !cell.section.is_zero() || !cell.current.is_zero();
        }
        if parametron_states != self.native_support || (!productive && self.obstruction.is_none()) {
            return Err(NativeSpoolRefusal::Parametron(self.address.clone()));
        }

        let mut consequences = BTreeMap::new();
        for consequence in &self.receiver_consequences {
            if !self.native_support.contains(&consequence.native)
                || consequences
                    .insert(
                        (consequence.native, consequence.receiver),
                        consequence.observation,
                    )
                    .is_some()
            {
                return Err(NativeSpoolRefusal::ReceiverConsequence(
                    self.address.clone(),
                ));
            }
        }
        let mut constitutive = BTreeSet::new();
        for response in &self.constitutive_responses {
            let key = (response.native, response.receiver);
            let cell = self
                .parametrons
                .iter()
                .find(|cell| cell.native == response.native);
            if !consequences.contains_key(&key)
                || !constitutive.insert(key)
                || cell.is_none_or(|cell| {
                    response.presented != cell.section || response.stored != cell.current
                })
            {
                return Err(NativeSpoolRefusal::ConstitutiveResponse(
                    self.address.clone(),
                ));
            }
        }
        if constitutive != consequences.keys().copied().collect() {
            return Err(NativeSpoolRefusal::ConstitutiveResponse(
                self.address.clone(),
            ));
        }

        if let Some(obstruction) = &self.obstruction {
            if obstruction.reason.is_empty()
                || obstruction.retained_native_fibre.is_empty()
                || !obstruction
                    .retained_native_fibre
                    .is_subset(&self.native_support)
            {
                return Err(NativeSpoolRefusal::Obstruction(self.address.clone()));
            }
        }
        if self.open_exterior.iter().any(String::is_empty) {
            return Err(NativeSpoolRefusal::OpenExterior(self.address.clone()));
        }
        Ok(())
    }
}

/// One member of the pullback occurrence population `W_f ×_Y W_g`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativePullbackOccurrence {
    pub left: EventId,
    pub right: EventId,
    pub joining_native: NativeStateId,
}

/// Exact serial composition of two thread spans.  Validation recomputes the complete joining
/// population; a count or equal endpoint boundary is not sufficient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSerialPullback {
    pub left_thread: String,
    pub right_thread: String,
    pub joining_boundary: BoundaryId,
    pub occurrences: BTreeSet<NativePullbackOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGeneratorStep {
    pub from: NativeStateId,
    pub to: NativeStateId,
    pub thread: String,
}

/// The descended native generator `U_g`.  The exterior realization witness owns the corresponding
/// source-side `q T_g = U_g q` square; this object retains only the total native action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGeneratorDescent {
    pub generator: InputId,
    pub steps: Vec<NativeGeneratorStep>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCollapsedFibre {
    pub native: NativeStateId,
    pub occurrences: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeShortestSeparator {
    pub left: EventId,
    pub right: EventId,
    pub word: Vec<InputId>,
    pub receiver: ReceiverId,
    pub left_observation: Observation,
    pub right_observation: Observation,
}

/// The complete consequence of one ordering used by an interchange receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOrderedConsequence {
    pub order: Vec<String>,
    pub successor: NativeStateId,
    pub obstructions: BTreeSet<NativeThreadObstruction>,
    pub lineage_occurrences: BTreeSet<EventId>,
    pub logical_resources: BTreeMap<String, i64>,
}

/// Exact independence testimony.  The two orders remain explicit while every consequence other
/// than their enumeration must agree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeInterchangeReceipt {
    pub left_thread: String,
    pub right_thread: String,
    pub left_then_right: NativeOrderedConsequence,
    pub right_then_left: NativeOrderedConsequence,
}

/// A reusable source-neutral generator family of native threads.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSpool {
    pub schema: String,
    pub address: String,
    pub native_population: BTreeSet<NativeStateId>,
    pub receiver_family: BTreeSet<ReceiverId>,
    pub generator_family: BTreeSet<InputId>,
    pub threads: Vec<NativeThread>,
    pub serial_pullbacks: Vec<NativeSerialPullback>,
    pub generator_descents: Vec<NativeGeneratorDescent>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub mutual_constitutive_responses: Vec<NativeMutualConstitutiveResponse>,
    pub reconstruction_fibres: Vec<NativeCollapsedFibre>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub interchanges: Vec<NativeInterchangeReceipt>,
    pub open_exterior: Vec<String>,
}

impl NativeSpool {
    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_SPOOL_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.address.is_empty()
            || self.native_population.is_empty()
            || self.receiver_family.is_empty()
            || self.generator_family.is_empty()
            || self.threads.is_empty()
        {
            return Err(NativeSpoolRefusal::MalformedSpool(self.address.clone()));
        }
        let mut threads = BTreeMap::new();
        let mut occurrence_to_emitting = BTreeMap::new();
        let mut occurrence_to_entering = BTreeMap::new();
        let mut derived_population = BTreeSet::new();
        for thread in &self.threads {
            thread.validate()?;
            if threads.insert(thread.address.as_str(), thread).is_some() {
                return Err(NativeSpoolRefusal::DuplicateThread(thread.address.clone()));
            }
            derived_population.extend(thread.native_support.iter().copied());
            for occurrence in &thread.occurrences {
                if occurrence_to_emitting
                    .insert(occurrence.occurrence, occurrence.emitting_native)
                    .is_some()
                {
                    return Err(NativeSpoolRefusal::DuplicateOccurrence(
                        occurrence.occurrence,
                    ));
                }
                occurrence_to_entering.insert(occurrence.occurrence, occurrence.entering_native);
            }
        }
        if derived_population != self.native_population {
            return Err(NativeSpoolRefusal::NativePopulation(self.address.clone()));
        }

        let mut pullback_pairs = BTreeSet::new();
        for pullback in &self.serial_pullbacks {
            let key = (
                pullback.left_thread.as_str(),
                pullback.right_thread.as_str(),
            );
            if !pullback_pairs.insert(key) {
                return Err(NativeSpoolRefusal::DuplicatePullback(
                    pullback.left_thread.clone(),
                    pullback.right_thread.clone(),
                ));
            }
            validate_pullback(pullback, &threads)?;
        }

        let mut descent_generators = BTreeSet::new();
        for descent in &self.generator_descents {
            if !self.generator_family.contains(&descent.generator)
                || !descent_generators.insert(descent.generator)
            {
                return Err(NativeSpoolRefusal::GeneratorDescent(descent.generator));
            }
            let mut domain = BTreeSet::new();
            for step in &descent.steps {
                let Some(thread) = threads.get(step.thread.as_str()) else {
                    return Err(NativeSpoolRefusal::GeneratorDescent(descent.generator));
                };
                if !domain.insert(step.from)
                    || !self.native_population.contains(&step.from)
                    || !self.native_population.contains(&step.to)
                    || !thread.occurrences.iter().any(|occurrence| {
                        occurrence.entering_native == step.from
                            && occurrence.emitting_native == step.to
                    })
                {
                    return Err(NativeSpoolRefusal::GeneratorDescent(descent.generator));
                }
            }
            if domain != self.native_population {
                return Err(NativeSpoolRefusal::GeneratorDescent(descent.generator));
            }
        }
        if descent_generators != self.generator_family {
            return Err(NativeSpoolRefusal::GeneratorFamily(self.address.clone()));
        }

        let mut factor_keys = BTreeSet::new();
        for factor in &self.receiver_factors {
            if !self.native_population.contains(&factor.native)
                || !self.receiver_family.contains(&factor.receiver)
                || !factor_keys.insert((factor.native, factor.receiver))
            {
                return Err(NativeSpoolRefusal::ReceiverFactor(self.address.clone()));
            }
        }
        let expected_factor_keys = self
            .native_population
            .iter()
            .flat_map(|native| {
                self.receiver_family
                    .iter()
                    .map(move |receiver| (*native, *receiver))
            })
            .collect::<BTreeSet<_>>();
        if factor_keys != expected_factor_keys {
            return Err(NativeSpoolRefusal::ReceiverFactor(self.address.clone()));
        }

        let zero = Rat::from_integer(0.into());
        let mut mutual_pairs = BTreeSet::new();
        for response in &self.mutual_constitutive_responses {
            let pair = (response.left_occurrence, response.right_occurrence);
            let ordered = response.left_occurrence < response.right_occurrence;
            let nonzero = response.storage != zero;
            let receiver_admitted = self.receiver_family.contains(&response.receiver);
            let left_matches = occurrence_to_entering.get(&response.left_occurrence)
                == Some(&response.left_native);
            let right_matches = occurrence_to_entering.get(&response.right_occurrence)
                == Some(&response.right_native);
            let fresh = mutual_pairs.insert(pair);
            if !ordered
                || !nonzero
                || !receiver_admitted
                || !left_matches
                || !right_matches
                || !fresh
            {
                return Err(NativeSpoolRefusal::MutualConstitutiveResponse(format!(
                    "{} at {:?}<->{:?}: ordered={ordered}, nonzero={nonzero}, receiver={receiver_admitted}, left={left_matches}, right={right_matches}, fresh={fresh}",
                    self.address, response.left_occurrence, response.right_occurrence
                )));
            }
        }

        let mut fibre_occurrences = BTreeSet::new();
        let mut fibre_by_occurrence = BTreeMap::new();
        for fibre in &self.reconstruction_fibres {
            if fibre.occurrences.is_empty() || !self.native_population.contains(&fibre.native) {
                return Err(NativeSpoolRefusal::SpoolFibre(self.address.clone()));
            }
            for occurrence in &fibre.occurrences {
                if occurrence_to_emitting.get(occurrence) != Some(&fibre.native)
                    || !fibre_occurrences.insert(*occurrence)
                {
                    return Err(NativeSpoolRefusal::SpoolFibre(self.address.clone()));
                }
                fibre_by_occurrence.insert(*occurrence, fibre.native);
            }
        }
        if fibre_occurrences != occurrence_to_emitting.keys().copied().collect() {
            return Err(NativeSpoolRefusal::SpoolFibre(self.address.clone()));
        }

        for separator in &self.shortest_separators {
            if separator.left == separator.right
                || separator.word.is_empty()
                || separator.left_observation == separator.right_observation
                || fibre_by_occurrence.get(&separator.left)
                    != fibre_by_occurrence.get(&separator.right)
                || separator
                    .word
                    .iter()
                    .any(|generator| !self.generator_family.contains(generator))
            {
                return Err(NativeSpoolRefusal::Separator(self.address.clone()));
            }
        }

        let mut interchange_pairs = BTreeSet::new();
        for interchange in &self.interchanges {
            let pair = (
                interchange.left_thread.as_str(),
                interchange.right_thread.as_str(),
            );
            if pair.0 == pair.1
                || !interchange_pairs.insert(pair)
                || !threads.contains_key(pair.0)
                || !threads.contains_key(pair.1)
            {
                return Err(NativeSpoolRefusal::Interchange(self.address.clone()));
            }
            validate_interchange(interchange, &threads)?;
        }
        if self.open_exterior.iter().any(String::is_empty) {
            return Err(NativeSpoolRefusal::OpenExterior(self.address.clone()));
        }
        Ok(())
    }
}
