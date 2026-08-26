//! Source-neutral addressed threads and reusable native spool complexes.
//!
//! This module owns only the native side of a realization boundary.  It has no source-model
//! identity, tensor coordinate, executor, ancestry witness, or callable reconstruction edge.  A
//! thread retains the full occurrence span rather than reducing a passage to its endpoints; a
//! spool retains the exact serial pullbacks, native generator action, receiver factors, complete
//! occurrence fibres, and any lawful interchange through which that passage can be reused.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort, PortHand,
    cuda_refine::{
        CudaRefineExecutor, ResidentComplexIncidence, ResidentComplexIncidenceReturn,
        ResidentNativeWord, ResidentNativeWordReturn,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
};

pub const NATIVE_THREAD_SCHEMA: &str = "holonic-engine.native-thread.v1";
pub const NATIVE_SPOOL_SCHEMA: &str = "holonic-engine.native-spool.v2";
pub const NATIVE_SPOOL_BUNDLE_SCHEMA: &str = "holonic-engine.native-spool-bundle.v2";
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

        let mut occurrence_ids = BTreeSet::new();
        for occurrence in &self.occurrences {
            if !occurrence_ids.insert(occurrence.occurrence)
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
        if occurrence_ids != self.reconstruction_fibre {
            return Err(NativeSpoolRefusal::ReconstructionFibre(
                self.address.clone(),
            ));
        }

        let mut incidence_occurrences = BTreeSet::new();
        for incidence in &self.incidence {
            let Some(occurrence) = self
                .occurrences
                .iter()
                .find(|candidate| candidate.occurrence == incidence.occurrence)
            else {
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

/// One exact serial composition joining threads owned by two different spools.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSpoolComposition {
    pub left_spool: String,
    pub right_spool: String,
    pub pullback: NativeSerialPullback,
}

/// A compatible source-neutral complex of reusable native spools.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSpoolBundle {
    pub schema: String,
    pub address: String,
    pub spools: Vec<NativeSpool>,
    pub compositions: Vec<NativeSpoolComposition>,
    pub open_exterior: Vec<String>,
}

/// A non-owning, source-neutral view of one occurrence and its exact native carrying section.
///
/// The view can only be founded through [`NativeSpoolBundle::addressed_section`].  Its incidence,
/// Parametron cells, ordered generator word, and reconstruction fibre remain owned by the one
/// mounted bundle; this type does not copy them into a second topology.
#[derive(Debug)]
pub struct NativeAddressedSection<'a> {
    bundle: &'a NativeSpoolBundle,
    spool: &'a NativeSpool,
    thread: &'a NativeThread,
    occurrence: &'a NativeThreadOccurrence,
    incidence: &'a NativeIncidenceTerm,
    entering_parametron: &'a NativeParametronCell,
    emitting_parametron: &'a NativeParametronCell,
    reconstruction_fibre: &'a NativeCollapsedFibre,
}

impl<'a> NativeAddressedSection<'a> {
    pub fn bundle_address(&self) -> &str {
        &self.bundle.address
    }

    pub fn spool(&self) -> &'a NativeSpool {
        self.spool
    }

    pub fn thread(&self) -> &'a NativeThread {
        self.thread
    }

    pub fn occurrence(&self) -> &'a NativeThreadOccurrence {
        self.occurrence
    }

    pub fn incidence(&self) -> &'a NativeIncidenceTerm {
        self.incidence
    }

    pub fn entering_parametron(&self) -> &'a NativeParametronCell {
        self.entering_parametron
    }

    pub fn emitting_parametron(&self) -> &'a NativeParametronCell {
        self.emitting_parametron
    }

    pub fn reconstruction_fibre(&self) -> &'a NativeCollapsedFibre {
        self.reconstruction_fibre
    }

    pub fn ordered_generator_word(&self) -> &'a [InputId] {
        &self.thread.chronology
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        self.bundle.validate()?;
        let valid = self
            .bundle
            .spools
            .iter()
            .any(|candidate| std::ptr::eq(candidate, self.spool))
            && self
                .spool
                .threads
                .iter()
                .any(|candidate| std::ptr::eq(candidate, self.thread))
            && self
                .thread
                .occurrences
                .iter()
                .any(|candidate| std::ptr::eq(candidate, self.occurrence))
            && self.thread.incidence.iter().any(|candidate| {
                std::ptr::eq(candidate, self.incidence)
                    && candidate.occurrence == self.occurrence.occurrence
                    && candidate.from == self.occurrence.entering_native
                    && candidate.to == self.occurrence.emitting_native
            })
            && self.thread.parametrons.iter().any(|candidate| {
                std::ptr::eq(candidate, self.entering_parametron)
                    && candidate.native == self.occurrence.entering_native
            })
            && self.thread.parametrons.iter().any(|candidate| {
                std::ptr::eq(candidate, self.emitting_parametron)
                    && candidate.native == self.occurrence.emitting_native
            })
            && self.spool.reconstruction_fibres.iter().any(|candidate| {
                std::ptr::eq(candidate, self.reconstruction_fibre)
                    && candidate.native == self.occurrence.emitting_native
                    && candidate.occurrences.contains(&self.occurrence.occurrence)
            });
        if !valid {
            return Err(NativeSpoolRefusal::AddressedSection(
                self.occurrence.occurrence,
            ));
        }
        Ok(())
    }
}

impl NativeSpoolBundle {
    pub fn read(bytes: &[u8]) -> Result<Self, NativeSpoolRefusal> {
        let bundle: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
        bundle.validate()?;
        Ok(bundle)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeSpoolRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_SPOOL_BUNDLE_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.address.is_empty() || self.spools.is_empty() {
            return Err(NativeSpoolRefusal::MalformedBundle(self.address.clone()));
        }
        let mut spools = BTreeMap::new();
        let mut thread_owner = BTreeMap::new();
        for spool in &self.spools {
            spool.validate()?;
            if spools.insert(spool.address.as_str(), spool).is_some() {
                return Err(NativeSpoolRefusal::DuplicateSpool(spool.address.clone()));
            }
            for thread in &spool.threads {
                if thread_owner
                    .insert(thread.address.as_str(), spool.address.as_str())
                    .is_some()
                {
                    return Err(NativeSpoolRefusal::DuplicateThread(thread.address.clone()));
                }
            }
        }

        let mut graph = BTreeMap::<&str, BTreeSet<&str>>::new();
        for spool in spools.keys() {
            graph.entry(*spool).or_default();
        }
        let mut composition_pairs = BTreeSet::new();
        for composition in &self.compositions {
            let Some(left) = spools.get(composition.left_spool.as_str()) else {
                return Err(NativeSpoolRefusal::BundleComposition);
            };
            let Some(right) = spools.get(composition.right_spool.as_str()) else {
                return Err(NativeSpoolRefusal::BundleComposition);
            };
            if composition.left_spool == composition.right_spool
                || !composition_pairs.insert((
                    composition.left_spool.as_str(),
                    composition.right_spool.as_str(),
                    composition.pullback.left_thread.as_str(),
                    composition.pullback.right_thread.as_str(),
                ))
                || thread_owner.get(composition.pullback.left_thread.as_str())
                    != Some(&left.address.as_str())
                || thread_owner.get(composition.pullback.right_thread.as_str())
                    != Some(&right.address.as_str())
            {
                return Err(NativeSpoolRefusal::BundleComposition);
            }
            let pair = BTreeMap::from([
                (
                    composition.pullback.left_thread.as_str(),
                    left.threads
                        .iter()
                        .find(|thread| thread.address == composition.pullback.left_thread)
                        .ok_or(NativeSpoolRefusal::BundleComposition)?,
                ),
                (
                    composition.pullback.right_thread.as_str(),
                    right
                        .threads
                        .iter()
                        .find(|thread| thread.address == composition.pullback.right_thread)
                        .ok_or(NativeSpoolRefusal::BundleComposition)?,
                ),
            ]);
            validate_pullback(&composition.pullback, &pair)?;
            graph
                .entry(composition.left_spool.as_str())
                .or_default()
                .insert(composition.right_spool.as_str());
            graph
                .entry(composition.right_spool.as_str())
                .or_default()
                .insert(composition.left_spool.as_str());
        }
        if !connected(&graph) {
            return Err(NativeSpoolRefusal::DisconnectedBundle);
        }
        if self.open_exterior.iter().any(String::is_empty) {
            return Err(NativeSpoolRefusal::OpenExterior(self.address.clone()));
        }
        Ok(())
    }

    /// Borrow one admitted occurrence as a complete native section view.  Spool, thread, and
    /// occurrence addresses are all required so equal exterior endpoints can never select a
    /// carrying occurrence by projection.
    pub fn addressed_section(
        &self,
        spool_address: &str,
        thread_address: &str,
        occurrence: EventId,
    ) -> Result<NativeAddressedSection<'_>, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread = spool
            .threads
            .iter()
            .find(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownThread(thread_address.to_owned()))?;
        let occurrence = thread
            .occurrences
            .iter()
            .find(|candidate| candidate.occurrence == occurrence)
            .ok_or(NativeSpoolRefusal::UnknownOccurrence(occurrence))?;
        let incidence = thread
            .incidence
            .iter()
            .find(|term| term.occurrence == occurrence.occurrence)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let entering_parametron = thread
            .parametrons
            .iter()
            .find(|cell| cell.native == occurrence.entering_native)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let emitting_parametron = thread
            .parametrons
            .iter()
            .find(|cell| cell.native == occurrence.emitting_native)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let reconstruction_fibre = spool
            .reconstruction_fibres
            .iter()
            .find(|fibre| {
                fibre.native == occurrence.emitting_native
                    && fibre.occurrences.contains(&occurrence.occurrence)
            })
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let section = NativeAddressedSection {
            bundle: self,
            spool,
            thread,
            occurrence,
            incidence,
            entering_parametron,
            emitting_parametron,
            reconstruction_fibre,
        };
        section.validate()?;
        Ok(section)
    }

    /// Mount one declared spool word as continuing resident native transport. The exterior
    /// realization and its witness are neither accepted nor reachable by this owner.
    pub fn mount_word(
        &self,
        spool_address: &str,
        word: &[InputId],
    ) -> Result<ResidentNativeSpoolWord, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        if word.is_empty() {
            return Err(NativeSpoolRefusal::UnknownGenerator(InputId(0)));
        }
        let states = spool.native_population.iter().copied().collect::<Vec<_>>();
        let state_index = states
            .iter()
            .enumerate()
            .map(|(at, native)| (*native, at as u32))
            .collect::<BTreeMap<_, _>>();
        let generators = spool.generator_family.iter().copied().collect::<Vec<_>>();
        let generator_index = generators
            .iter()
            .enumerate()
            .map(|(at, generator)| (*generator, at as u32))
            .collect::<BTreeMap<_, _>>();
        let resident_word = word
            .iter()
            .map(|generator| {
                generator_index
                    .get(generator)
                    .copied()
                    .ok_or(NativeSpoolRefusal::UnknownGenerator(*generator))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let descents = spool
            .generator_descents
            .iter()
            .map(|descent| (descent.generator, descent))
            .collect::<BTreeMap<_, _>>();
        let mut generator_table = Vec::with_capacity(states.len() * generators.len());
        for generator in &generators {
            let descent = descents
                .get(generator)
                .ok_or(NativeSpoolRefusal::UnknownGenerator(*generator))?;
            let steps = descent
                .steps
                .iter()
                .map(|step| (step.from, step.to))
                .collect::<BTreeMap<_, _>>();
            for state in &states {
                let returned = steps
                    .get(state)
                    .ok_or(NativeSpoolRefusal::UnknownNative(*state))?;
                generator_table.push(
                    *state_index
                        .get(returned)
                        .ok_or(NativeSpoolRefusal::UnknownNative(*returned))?,
                );
            }
        }
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let device = card.device_name().to_owned();
        let block_threads = card.block_threads();
        let resident = ResidentNativeWord::mount(
            card,
            states.len(),
            generators.len(),
            &generator_table,
            &resident_word,
        )
        .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let receiver_factors = spool
            .receiver_factors
            .iter()
            .map(|factor| ((factor.native, factor.receiver), factor.observation))
            .collect();
        Ok(ResidentNativeSpoolWord {
            spool_address: spool.address.clone(),
            states,
            state_index,
            receiver_factors,
            device,
            block_threads,
            resident,
        })
    }

    /// Mount one thread's exact incidence/current face on the card. The incidence rows and current
    /// population are derived from the addressed thread itself; no caller width or source chart is
    /// accepted.
    pub fn mount_thread_current(
        &self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<ResidentNativeThreadCurrent, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread = spool
            .threads
            .iter()
            .find(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownThread(thread_address.to_owned()))?;
        let states = thread.native_support.iter().copied().collect::<Vec<_>>();
        let state_index = states
            .iter()
            .enumerate()
            .map(|(at, native)| (*native, at))
            .collect::<BTreeMap<_, _>>();
        let incidence_by_occurrence = thread
            .incidence
            .iter()
            .map(|term| (term.occurrence, term))
            .collect::<BTreeMap<_, _>>();
        let mut incidence = vec![0i64; thread.occurrences.len() * states.len()];
        for (row, occurrence) in thread.occurrences.iter().enumerate() {
            let term = incidence_by_occurrence[&occurrence.occurrence];
            let from = state_index[&term.from];
            let to = state_index[&term.to];
            incidence[row * states.len() + from] -= term.coefficient;
            incidence[row * states.len() + to] += term.coefficient;
        }
        let cells = thread
            .parametrons
            .iter()
            .map(|cell| (cell.native, cell))
            .collect::<BTreeMap<_, _>>();
        let front = states
            .iter()
            .map(|state| cells[state].current.clone())
            .collect::<Vec<_>>();
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let resident = ResidentComplexIncidence::mount(
            card,
            thread.address.clone(),
            0,
            thread.occurrences.len(),
            states.len(),
            &incidence,
        )
        .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        Ok(ResidentNativeThreadCurrent { front, resident })
    }

    /// Derive the receiver insufficiency exposed by a staged thread withdrawal. Both implicated
    /// occurrences remain in the continuing body plus its reversible delta; the separator is an
    /// actual distinct Complex-Parametron response under the withdrawn generator word.
    pub fn insufficiency_after_withdrawal(
        &self,
        withdrawal: &NativeThreadWithdrawal,
    ) -> Result<ReceiverInsufficiency, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == withdrawal.spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(withdrawal.spool_address.clone()))?;
        let generator = withdrawal
            .generator_descents
            .iter()
            .find(|(_, descent)| {
                descent
                    .steps
                    .iter()
                    .any(|step| step.thread == withdrawal.thread.address)
            })
            .map(|(_, descent)| descent.generator)
            .ok_or(NativeSpoolRefusal::Insufficiency)?;
        let removed_cells = withdrawal
            .thread
            .parametrons
            .iter()
            .map(|cell| (cell.native, cell))
            .collect::<BTreeMap<_, _>>();
        let removed_responses = withdrawal
            .thread
            .constitutive_responses
            .iter()
            .map(|response| ((response.native, response.receiver), response))
            .collect::<BTreeMap<_, _>>();
        for removed in &withdrawal.thread.occurrences {
            for retained_thread in &spool.threads {
                let Some(retained) = retained_thread
                    .occurrences
                    .iter()
                    .find(|candidate| candidate.entering_native == removed.entering_native)
                else {
                    continue;
                };
                let Some(retained_cell) = retained_thread
                    .parametrons
                    .iter()
                    .find(|cell| cell.native == retained.entering_native)
                else {
                    continue;
                };
                let removed_cell = removed_cells[&removed.entering_native];
                for ((native, receiver), removed_response) in &removed_responses {
                    if *native != removed.entering_native {
                        continue;
                    }
                    let Some(retained_response) = retained_thread
                        .constitutive_responses
                        .iter()
                        .find(|response| {
                            response.native == retained.entering_native
                                && response.receiver == *receiver
                        })
                    else {
                        continue;
                    };
                    if removed_cell.current == retained_cell.current
                        && removed_response.stored == retained_response.stored
                    {
                        continue;
                    }
                    let separator = NativeShortestSeparator {
                        left: removed.occurrence,
                        right: retained.occurrence,
                        word: vec![generator],
                        receiver: *receiver,
                        left_observation: current_observation(
                            &removed_cell.current,
                            &removed_response.stored,
                        ),
                        right_observation: current_observation(
                            &retained_cell.current,
                            &retained_response.stored,
                        ),
                    };
                    if separator.left_observation == separator.right_observation {
                        continue;
                    }
                    let insufficiency = ReceiverInsufficiency {
                        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
                        at_occurrence: removed.occurrence,
                        native: removed.entering_native,
                        retained_fibre: BTreeSet::from([removed.occurrence, retained.occurrence]),
                        cause: ReceiverInsufficiencyCause::ReconstructionFibreReopened {
                            separator,
                        },
                        open_exterior: vec![
                            "thread withdrawal separates an admitted Complex-Parametron response"
                                .to_owned(),
                        ],
                    };
                    insufficiency.validate()?;
                    return Ok(insufficiency);
                }
            }
        }
        Err(NativeSpoolRefusal::Insufficiency)
    }

    /// Withdraw one addressed native thread and every dependent receipt as a staged local delta.
    /// The continuing bundle is consumed, never cloned. Restoration consumes the delta and proves
    /// the original canonical identity.
    pub fn withdraw_thread(
        mut self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, NativeThreadWithdrawal), NativeSpoolRefusal> {
        self.validate()?;
        let original_identity_sha256 = native_bundle_identity(&self)?;
        let spool = self
            .spools
            .iter_mut()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread_position = spool
            .threads
            .iter()
            .position(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::DuplicateThread(thread_address.to_owned()))?;
        let thread = spool.threads.remove(thread_position);
        let removed_events = thread
            .occurrences
            .iter()
            .map(|occurrence| occurrence.occurrence)
            .collect::<BTreeSet<_>>();

        let generator_descents = extract_indexed(&mut spool.generator_descents, |descent| {
            descent
                .steps
                .iter()
                .any(|step| step.thread == thread_address)
        });
        for (_, descent) in &generator_descents {
            spool.generator_family.remove(&descent.generator);
        }
        let serial_pullbacks = extract_indexed(&mut spool.serial_pullbacks, |pullback| {
            pullback.left_thread == thread_address || pullback.right_thread == thread_address
        });
        let interchanges = extract_indexed(&mut spool.interchanges, |interchange| {
            interchange.left_thread == thread_address || interchange.right_thread == thread_address
        });
        let shortest_separators = extract_indexed(&mut spool.shortest_separators, |separator| {
            removed_events.contains(&separator.left) || removed_events.contains(&separator.right)
        });
        let mutual_constitutive_responses =
            extract_indexed(&mut spool.mutual_constitutive_responses, |response| {
                removed_events.contains(&response.left_occurrence)
                    || removed_events.contains(&response.right_occurrence)
            });

        let mut fibre_deltas = Vec::new();
        let mut retained_fibres = Vec::new();
        for (position, mut fibre) in spool.reconstruction_fibres.drain(..).enumerate() {
            let withdrawn = fibre
                .occurrences
                .intersection(&removed_events)
                .copied()
                .collect::<BTreeSet<_>>();
            fibre.occurrences = fibre
                .occurrences
                .difference(&removed_events)
                .copied()
                .collect();
            if !withdrawn.is_empty() {
                fibre_deltas.push(NativeWithdrawalFibreDelta {
                    position,
                    native: fibre.native,
                    occurrences: withdrawn,
                    fibre_departed: fibre.occurrences.is_empty(),
                });
            }
            if !fibre.occurrences.is_empty() {
                retained_fibres.push(fibre);
            }
        }
        spool.reconstruction_fibres = retained_fibres;
        spool.native_population = spool
            .threads
            .iter()
            .flat_map(|thread| thread.native_support.iter().copied())
            .collect();
        let retained_native_population = spool.native_population.clone();
        let receiver_factors = extract_indexed(&mut spool.receiver_factors, |factor| {
            !retained_native_population.contains(&factor.native)
        });
        spool.validate()?;
        self.validate()?;
        Ok((
            self,
            NativeThreadWithdrawal {
                original_identity_sha256,
                spool_address: spool_address.to_owned(),
                thread_position,
                thread,
                serial_pullbacks,
                generator_descents,
                receiver_factors,
                mutual_constitutive_responses,
                shortest_separators,
                interchanges,
                fibre_deltas,
            },
        ))
    }

    pub fn restore_thread(
        mut self,
        withdrawal: NativeThreadWithdrawal,
    ) -> Result<Self, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter_mut()
            .find(|spool| spool.address == withdrawal.spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(withdrawal.spool_address.clone()))?;
        if spool
            .threads
            .iter()
            .any(|thread| thread.address == withdrawal.thread.address)
            || withdrawal.thread_position > spool.threads.len()
        {
            return Err(NativeSpoolRefusal::Restoration);
        }
        spool
            .threads
            .insert(withdrawal.thread_position, withdrawal.thread);
        restore_indexed(&mut spool.serial_pullbacks, withdrawal.serial_pullbacks)?;
        for (_, descent) in &withdrawal.generator_descents {
            spool.generator_family.insert(descent.generator);
        }
        restore_indexed(&mut spool.generator_descents, withdrawal.generator_descents)?;
        restore_indexed(&mut spool.receiver_factors, withdrawal.receiver_factors)?;
        restore_indexed(
            &mut spool.mutual_constitutive_responses,
            withdrawal.mutual_constitutive_responses,
        )?;
        restore_indexed(
            &mut spool.shortest_separators,
            withdrawal.shortest_separators,
        )?;
        restore_indexed(&mut spool.interchanges, withdrawal.interchanges)?;
        for delta in withdrawal.fibre_deltas {
            if delta.fibre_departed {
                if delta.position > spool.reconstruction_fibres.len() {
                    return Err(NativeSpoolRefusal::Restoration);
                }
                spool.reconstruction_fibres.insert(
                    delta.position,
                    NativeCollapsedFibre {
                        native: delta.native,
                        occurrences: delta.occurrences,
                    },
                );
            } else {
                let fibre = spool
                    .reconstruction_fibres
                    .iter_mut()
                    .find(|fibre| fibre.native == delta.native)
                    .ok_or(NativeSpoolRefusal::Restoration)?;
                fibre.occurrences.extend(delta.occurrences);
            }
        }
        spool.native_population = spool
            .threads
            .iter()
            .flat_map(|thread| thread.native_support.iter().copied())
            .collect();
        self.validate()?;
        if native_bundle_identity(&self)? != withdrawal.original_identity_sha256 {
            return Err(NativeSpoolRefusal::Restoration);
        }
        Ok(self)
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeWithdrawalFibreDelta {
    pub position: usize,
    pub native: NativeStateId,
    pub occurrences: BTreeSet<EventId>,
    pub fibre_departed: bool,
}

/// The exact local difference needed to reverse one thread withdrawal.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeThreadWithdrawal {
    pub original_identity_sha256: String,
    pub spool_address: String,
    pub thread_position: usize,
    pub thread: NativeThread,
    pub serial_pullbacks: Vec<(usize, NativeSerialPullback)>,
    pub generator_descents: Vec<(usize, NativeGeneratorDescent)>,
    pub receiver_factors: Vec<(usize, ReceiverFactor)>,
    pub mutual_constitutive_responses: Vec<(usize, NativeMutualConstitutiveResponse)>,
    pub shortest_separators: Vec<(usize, NativeShortestSeparator)>,
    pub interchanges: Vec<(usize, NativeInterchangeReceipt)>,
    pub fibre_deltas: Vec<NativeWithdrawalFibreDelta>,
}

/// One later return from a resident native spool word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSpoolConductReturn {
    pub spool_address: String,
    pub native_start: Vec<NativeStateId>,
    pub native_end: Vec<NativeStateId>,
    pub receiver: ReceiverId,
    pub observations: Vec<Observation>,
    pub device: String,
    pub block_threads: u32,
    pub apparatus: ResidentNativeWordReturn,
}

/// The singular resident owner of one declared native word.
pub struct ResidentNativeSpoolWord {
    spool_address: String,
    states: Vec<NativeStateId>,
    state_index: BTreeMap<NativeStateId, u32>,
    receiver_factors: BTreeMap<(NativeStateId, ReceiverId), Observation>,
    device: String,
    block_threads: u32,
    resident: ResidentNativeWord,
}

/// One resident native Complex-Parametron thread. It owns its exact current front and card
/// incidence; neither source coordinates nor an exterior reconstruction edge are reachable.
pub struct ResidentNativeThreadCurrent {
    front: Vec<ExactComplexWaveCurrent>,
    resident: ResidentComplexIncidence,
}

impl ResidentNativeThreadCurrent {
    pub fn conduct(&mut self) -> Result<ResidentComplexIncidenceReturn, NativeSpoolRefusal> {
        self.resident
            .conduct(std::slice::from_ref(&self.front))
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))
    }
}

impl ResidentNativeSpoolWord {
    pub fn conduct(
        &mut self,
        native_start: &[NativeStateId],
        receiver: ReceiverId,
    ) -> Result<NativeSpoolConductReturn, NativeSpoolRefusal> {
        let start = native_start
            .iter()
            .map(|native| {
                self.state_index
                    .get(native)
                    .copied()
                    .ok_or(NativeSpoolRefusal::UnknownNative(*native))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let apparatus = self
            .resident
            .conduct(&start)
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let native_end = apparatus
            .native_end
            .iter()
            .map(|at| {
                self.states
                    .get(*at as usize)
                    .copied()
                    .ok_or(NativeSpoolRefusal::Apparatus(
                        "the resident word returned a state outside its mounted population"
                            .to_owned(),
                    ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let observations = native_end
            .iter()
            .map(|native| {
                self.receiver_factors
                    .get(&(*native, receiver))
                    .copied()
                    .ok_or(NativeSpoolRefusal::UnknownReceiver {
                        native: *native,
                        receiver,
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(NativeSpoolConductReturn {
            spool_address: self.spool_address.clone(),
            native_start: native_start.to_vec(),
            native_end,
            receiver,
            observations,
            device: self.device.clone(),
            block_threads: self.block_threads,
            apparatus,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "cause", rename_all = "kebab-case")]
pub enum ReceiverInsufficiencyCause {
    ReceiverOutsideFamily {
        requested: ReceiverId,
        admitted: BTreeSet<ReceiverId>,
    },
    SuccessorOutsideFamily {
        requested_word: Vec<InputId>,
        admitted_generators: BTreeSet<InputId>,
    },
    SectionOutsideFamily {
        requested: EventId,
        admitted: BTreeSet<EventId>,
    },
    ReconstructionFibreReopened {
        separator: NativeShortestSeparator,
    },
}

/// Exact native obstruction returned instead of consulting any exterior realization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverInsufficiency {
    pub schema: String,
    pub at_occurrence: EventId,
    pub native: NativeStateId,
    pub retained_fibre: BTreeSet<EventId>,
    pub cause: ReceiverInsufficiencyCause,
    pub open_exterior: Vec<String>,
}

impl ReceiverInsufficiency {
    /// Return the exact retained occurrence fibre when a receiver is not admitted by this
    /// section's spool.  The admitted family and fibre are derived from the borrowed native owner.
    pub fn receiver_outside_family(
        section: &NativeAddressedSection<'_>,
        requested: ReceiverId,
        open_exterior: Vec<String>,
    ) -> Result<Self, NativeSpoolRefusal> {
        section.validate()?;
        Self::from_section(
            section,
            ReceiverInsufficiencyCause::ReceiverOutsideFamily {
                requested,
                admitted: section.spool.receiver_family.clone(),
            },
            open_exterior,
        )
    }

    /// Return the exact retained occurrence fibre when an ordered successor word contains a
    /// generator not admitted by this section's spool.
    pub fn successor_word_outside_family(
        section: &NativeAddressedSection<'_>,
        requested_word: Vec<InputId>,
        open_exterior: Vec<String>,
    ) -> Result<Self, NativeSpoolRefusal> {
        section.validate()?;
        Self::from_section(
            section,
            ReceiverInsufficiencyCause::SuccessorOutsideFamily {
                requested_word,
                admitted_generators: section.spool.generator_family.clone(),
            },
            open_exterior,
        )
    }

    /// Return the current exact fibre when a requested occurrence is not in this spool's admitted
    /// section population.  The absent occurrence is testimony only; no native state is invented
    /// for it.
    pub fn section_outside_family(
        section: &NativeAddressedSection<'_>,
        requested: EventId,
        open_exterior: Vec<String>,
    ) -> Result<Self, NativeSpoolRefusal> {
        section.validate()?;
        let admitted = section
            .spool
            .threads
            .iter()
            .flat_map(|thread| thread.occurrences.iter())
            .map(|occurrence| occurrence.occurrence)
            .collect();
        Self::from_section(
            section,
            ReceiverInsufficiencyCause::SectionOutsideFamily {
                requested,
                admitted,
            },
            open_exterior,
        )
    }

    fn from_section(
        section: &NativeAddressedSection<'_>,
        cause: ReceiverInsufficiencyCause,
        open_exterior: Vec<String>,
    ) -> Result<Self, NativeSpoolRefusal> {
        let insufficiency = Self {
            schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
            at_occurrence: section.occurrence.occurrence,
            native: section.occurrence.emitting_native,
            retained_fibre: section.reconstruction_fibre.occurrences.clone(),
            cause,
            open_exterior,
        };
        insufficiency.validate()?;
        Ok(insufficiency)
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != RECEIVER_INSUFFICIENCY_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.retained_fibre.is_empty() || self.open_exterior.iter().any(String::is_empty) {
            return Err(NativeSpoolRefusal::Insufficiency);
        }
        match &self.cause {
            ReceiverInsufficiencyCause::ReceiverOutsideFamily {
                requested,
                admitted,
            } => {
                if admitted.is_empty() || admitted.contains(requested) {
                    return Err(NativeSpoolRefusal::Insufficiency);
                }
            }
            ReceiverInsufficiencyCause::SuccessorOutsideFamily {
                requested_word,
                admitted_generators,
            } => {
                if requested_word.is_empty()
                    || admitted_generators.is_empty()
                    || requested_word
                        .iter()
                        .all(|generator| admitted_generators.contains(generator))
                {
                    return Err(NativeSpoolRefusal::Insufficiency);
                }
            }
            ReceiverInsufficiencyCause::SectionOutsideFamily {
                requested,
                admitted,
            } => {
                if admitted.is_empty()
                    || admitted.contains(requested)
                    || !admitted.is_superset(&self.retained_fibre)
                    || !self.retained_fibre.contains(&self.at_occurrence)
                {
                    return Err(NativeSpoolRefusal::Insufficiency);
                }
            }
            ReceiverInsufficiencyCause::ReconstructionFibreReopened { separator } => {
                if separator.left == separator.right
                    || separator.word.is_empty()
                    || separator.left_observation == separator.right_observation
                    || !self.retained_fibre.contains(&separator.left)
                    || !self.retained_fibre.contains(&separator.right)
                {
                    return Err(NativeSpoolRefusal::Insufficiency);
                }
            }
        }
        Ok(())
    }
}

fn validate_pullback(
    pullback: &NativeSerialPullback,
    threads: &BTreeMap<&str, &NativeThread>,
) -> Result<(), NativeSpoolRefusal> {
    let Some(left) = threads.get(pullback.left_thread.as_str()) else {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    };
    let Some(right) = threads.get(pullback.right_thread.as_str()) else {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    };
    if left.emitting_boundary != pullback.joining_boundary
        || right.entering_boundary != pullback.joining_boundary
    {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    }
    let expected =
        left.occurrences
            .iter()
            .flat_map(|left_occurrence| {
                right
                    .occurrences
                    .iter()
                    .filter_map(move |right_occurrence| {
                        (left_occurrence.emitting_native == right_occurrence.entering_native)
                            .then_some(NativePullbackOccurrence {
                                left: left_occurrence.occurrence,
                                right: right_occurrence.occurrence,
                                joining_native: left_occurrence.emitting_native,
                            })
                    })
            })
            .collect::<BTreeSet<_>>();
    if expected.is_empty() || expected != pullback.occurrences {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    }
    Ok(())
}

fn validate_interchange(
    receipt: &NativeInterchangeReceipt,
    threads: &BTreeMap<&str, &NativeThread>,
) -> Result<(), NativeSpoolRefusal> {
    if receipt.left_then_right.order
        != vec![receipt.left_thread.clone(), receipt.right_thread.clone()]
        || receipt.right_then_left.order
            != vec![receipt.right_thread.clone(), receipt.left_thread.clone()]
    {
        return Err(NativeSpoolRefusal::Interchange(receipt.left_thread.clone()));
    }
    let expected_lineage = threads[receipt.left_thread.as_str()]
        .occurrences
        .iter()
        .chain(threads[receipt.right_thread.as_str()].occurrences.iter())
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    if receipt.left_then_right.successor != receipt.right_then_left.successor
        || receipt.left_then_right.obstructions != receipt.right_then_left.obstructions
        || receipt.left_then_right.lineage_occurrences != expected_lineage
        || receipt.right_then_left.lineage_occurrences != expected_lineage
        || receipt.left_then_right.logical_resources != receipt.right_then_left.logical_resources
    {
        return Err(NativeSpoolRefusal::Interchange(receipt.left_thread.clone()));
    }
    Ok(())
}

fn connected(graph: &BTreeMap<&str, BTreeSet<&str>>) -> bool {
    let Some(start) = graph.keys().next().copied() else {
        return false;
    };
    let mut reached = BTreeSet::from([start]);
    let mut queue = VecDeque::from([start]);
    while let Some(at) = queue.pop_front() {
        for next in &graph[at] {
            if reached.insert(*next) {
                queue.push_back(*next);
            }
        }
    }
    reached.len() == graph.len()
}

fn extract_indexed<T>(
    values: &mut Vec<T>,
    mut withdraw: impl FnMut(&T) -> bool,
) -> Vec<(usize, T)> {
    let mut retained = Vec::with_capacity(values.len());
    let mut removed = Vec::new();
    for (position, value) in values.drain(..).enumerate() {
        if withdraw(&value) {
            removed.push((position, value));
        } else {
            retained.push(value);
        }
    }
    *values = retained;
    removed
}

fn restore_indexed<T>(
    values: &mut Vec<T>,
    mut restored: Vec<(usize, T)>,
) -> Result<(), NativeSpoolRefusal> {
    restored.sort_by_key(|(position, _)| *position);
    for (position, value) in restored {
        if position > values.len() {
            return Err(NativeSpoolRefusal::Restoration);
        }
        values.insert(position, value);
    }
    Ok(())
}

fn native_bundle_identity(bundle: &NativeSpoolBundle) -> Result<String, NativeSpoolRefusal> {
    let bytes = bundle.canonical_bytes()?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn current_observation(
    current: &ExactComplexWaveCurrent,
    stored: &ExactComplexWaveCurrent,
) -> Observation {
    let mut digest = Sha256::new();
    for coordinate in [
        current.real.to_string(),
        current.imaginary.to_string(),
        stored.real.to_string(),
        stored.imaginary.to_string(),
    ] {
        digest.update((coordinate.len() as u64).to_le_bytes());
        digest.update(coordinate.as_bytes());
    }
    Observation(u64::from_le_bytes(
        digest.finalize()[..8]
            .try_into()
            .expect("eight observation octets"),
    ))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeSpoolRefusal {
    #[error("native spool wire refused: {0}")]
    Wire(String),
    #[error("unknown native spool schema {0}")]
    Schema(String),
    #[error("native thread {0} is empty or incomplete")]
    MalformedThread(String),
    #[error("native thread {0} has malformed occurrence lineage or ports")]
    Occurrence(String),
    #[error("native thread {0} does not retain its complete occurrence fibre")]
    ReconstructionFibre(String),
    #[error("native thread {0} has malformed or incomplete incidence")]
    Incidence(String),
    #[error("native thread {0} has malformed, incomplete, or empty Parametron current")]
    Parametron(String),
    #[error("native thread {0} has a malformed receiver consequence")]
    ReceiverConsequence(String),
    #[error("native thread {0} has a malformed constitutive response")]
    ConstitutiveResponse(String),
    #[error("native thread {0} has a malformed obstruction")]
    Obstruction(String),
    #[error("native object {0} has an empty open-exterior address")]
    OpenExterior(String),
    #[error("native spool {0} is empty or incomplete")]
    MalformedSpool(String),
    #[error("native thread address {0} is repeated")]
    DuplicateThread(String),
    #[error("native occurrence {0:?} is owned by more than one thread")]
    DuplicateOccurrence(EventId),
    #[error("native spool {0} has an inconsistent native population")]
    NativePopulation(String),
    #[error("serial pullback {0} -> {1} is incomplete or malformed")]
    Pullback(String, String),
    #[error("serial pullback {0} -> {1} is repeated")]
    DuplicatePullback(String, String),
    #[error("native generator {0:?} has a partial or unrealized descent")]
    GeneratorDescent(InputId),
    #[error("native spool {0} does not carry exactly its declared generator family")]
    GeneratorFamily(String),
    #[error("native spool {0} does not carry the complete receiver factor family")]
    ReceiverFactor(String),
    #[error("native spool {0} has a malformed mutual constitutive response")]
    MutualConstitutiveResponse(String),
    #[error("native spool {0} does not retain an exact occurrence-fibre partition")]
    SpoolFibre(String),
    #[error("native spool {0} has a malformed shortest separator")]
    Separator(String),
    #[error("native spool {0} has a malformed interchange receipt")]
    Interchange(String),
    #[error("native spool bundle {0} is empty or incomplete")]
    MalformedBundle(String),
    #[error("native spool address {0} is repeated")]
    DuplicateSpool(String),
    #[error("native spool composition is missing, repeated, or names the wrong owner")]
    BundleComposition,
    #[error("native spool bundle has more than one disconnected component")]
    DisconnectedBundle,
    #[error("receiver insufficiency is malformed or does not exhibit its retained fibre")]
    Insufficiency,
    #[error("native spool {0} is absent from this bundle")]
    UnknownSpool(String),
    #[error("native thread {0} is absent from this bundle")]
    UnknownThread(String),
    #[error("native occurrence {0:?} is absent from the addressed thread")]
    UnknownOccurrence(EventId),
    #[error("native addressed section at occurrence {0:?} is inconsistent with its owner")]
    AddressedSection(EventId),
    #[error("native generator {0:?} is absent from the mounted spool")]
    UnknownGenerator(InputId),
    #[error("native state {0:?} is absent from the mounted spool")]
    UnknownNative(NativeStateId),
    #[error("receiver {receiver:?} has no factor at native state {native:?}")]
    UnknownReceiver {
        native: NativeStateId,
        receiver: ReceiverId,
    },
    #[error("resident native spool apparatus refused: {0}")]
    Apparatus(String),
    #[error("the native thread withdrawal cannot restore its exact predecessor")]
    Restoration,
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use relational_geometry::Rat;

    fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(real)),
            Rat::from_integer(BigInt::from(imaginary)),
        )
    }

    fn thread(
        address: &str,
        event: u64,
        entering_boundary: u64,
        emitting_boundary: u64,
        from: u64,
        to: u64,
        generator: u64,
    ) -> NativeThread {
        let occurrence = EventId(event);
        let from = NativeStateId(from);
        let to = NativeStateId(to);
        let receiver = ReceiverId(9);
        NativeThread {
            schema: NATIVE_THREAD_SCHEMA.to_owned(),
            address: address.to_owned(),
            entering_boundary: BoundaryId(entering_boundary),
            emitting_boundary: BoundaryId(emitting_boundary),
            entering_carrier: "native-complex-section".to_owned(),
            emitting_carrier: "native-complex-section".to_owned(),
            occurrences: vec![NativeThreadOccurrence {
                occurrence,
                predecessor: None,
                entering_port: OccurrencePort::input(occurrence, 0),
                emitting_port: OccurrencePort::output(occurrence, 0),
                entering_native: from,
                emitting_native: to,
            }],
            native_support: BTreeSet::from([from, to]),
            incidence: vec![NativeIncidenceTerm {
                occurrence,
                from,
                to,
                coefficient: 1,
            }],
            parametrons: vec![
                NativeParametronCell {
                    native: from,
                    section: current(1, 0),
                    current: current(0, 1),
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                },
                NativeParametronCell {
                    native: to,
                    section: current(0, 1),
                    current: current(-1, 0),
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                },
            ],
            constitutive_responses: vec![
                NativeConstitutiveResponse {
                    native: from,
                    receiver,
                    presented: current(1, 0),
                    stored: current(0, 1),
                },
                NativeConstitutiveResponse {
                    native: to,
                    receiver,
                    presented: current(0, 1),
                    stored: current(-1, 0),
                },
            ],
            chronology: vec![InputId(generator)],
            receiver_consequences: vec![
                NativeReceiverConsequence {
                    native: from,
                    receiver,
                    observation: Observation(from.0 + 100),
                },
                NativeReceiverConsequence {
                    native: to,
                    receiver,
                    observation: Observation(to.0 + 100),
                },
            ],
            obstruction: None,
            open_exterior: vec!["receiver/history outside the admitted family".to_owned()],
            reconstruction_fibre: BTreeSet::from([occurrence]),
        }
    }

    fn spool() -> NativeSpool {
        let left = thread("thread/turn-out", 1, 10, 11, 0, 1, 7);
        let right = thread("thread/turn-back", 2, 11, 10, 1, 0, 7);
        NativeSpool {
            schema: NATIVE_SPOOL_SCHEMA.to_owned(),
            address: "spool/native-turn".to_owned(),
            native_population: BTreeSet::from([NativeStateId(0), NativeStateId(1)]),
            receiver_family: BTreeSet::from([ReceiverId(9)]),
            generator_family: BTreeSet::from([InputId(7)]),
            threads: vec![left, right],
            serial_pullbacks: vec![
                NativeSerialPullback {
                    left_thread: "thread/turn-out".to_owned(),
                    right_thread: "thread/turn-back".to_owned(),
                    joining_boundary: BoundaryId(11),
                    occurrences: BTreeSet::from([NativePullbackOccurrence {
                        left: EventId(1),
                        right: EventId(2),
                        joining_native: NativeStateId(1),
                    }]),
                },
                NativeSerialPullback {
                    left_thread: "thread/turn-back".to_owned(),
                    right_thread: "thread/turn-out".to_owned(),
                    joining_boundary: BoundaryId(10),
                    occurrences: BTreeSet::from([NativePullbackOccurrence {
                        left: EventId(2),
                        right: EventId(1),
                        joining_native: NativeStateId(0),
                    }]),
                },
            ],
            generator_descents: vec![NativeGeneratorDescent {
                generator: InputId(7),
                steps: vec![
                    NativeGeneratorStep {
                        from: NativeStateId(0),
                        to: NativeStateId(1),
                        thread: "thread/turn-out".to_owned(),
                    },
                    NativeGeneratorStep {
                        from: NativeStateId(1),
                        to: NativeStateId(0),
                        thread: "thread/turn-back".to_owned(),
                    },
                ],
            }],
            receiver_factors: vec![
                ReceiverFactor {
                    native: NativeStateId(0),
                    receiver: ReceiverId(9),
                    observation: Observation(100),
                },
                ReceiverFactor {
                    native: NativeStateId(1),
                    receiver: ReceiverId(9),
                    observation: Observation(101),
                },
            ],
            mutual_constitutive_responses: Vec::new(),
            reconstruction_fibres: vec![
                NativeCollapsedFibre {
                    native: NativeStateId(0),
                    occurrences: BTreeSet::from([EventId(2)]),
                },
                NativeCollapsedFibre {
                    native: NativeStateId(1),
                    occurrences: BTreeSet::from([EventId(1)]),
                },
            ],
            shortest_separators: Vec::new(),
            interchanges: Vec::new(),
            open_exterior: vec!["larger receiver family".to_owned()],
        }
    }

    fn bundle() -> NativeSpoolBundle {
        NativeSpoolBundle {
            schema: NATIVE_SPOOL_BUNDLE_SCHEMA.to_owned(),
            address: "bundle/native-turn".to_owned(),
            spools: vec![spool()],
            compositions: Vec::new(),
            open_exterior: vec!["another compatible spool".to_owned()],
        }
    }

    #[test]
    fn native_bundle_round_trips_without_ancestry_fields() {
        let bundle = bundle();
        let bytes = bundle.canonical_bytes().expect("valid bundle");
        let remounted = NativeSpoolBundle::read(&bytes).expect("remount");
        assert_eq!(remounted, bundle);
        let text = String::from_utf8(bytes).expect("json").to_ascii_lowercase();
        for forbidden in [
            "soulkiller",
            "phoenix",
            "foreign",
            "model_name",
            "tensor",
            "token_id",
            "source_executor",
            "q_proj",
            "k_proj",
            "v_proj",
        ] {
            assert!(
                !text.contains(forbidden),
                "native wire contains {forbidden}"
            );
        }
    }

    #[test]
    fn native_addressed_section_borrows_the_exact_occurrence_carrier() {
        let bundle = bundle();
        let section = bundle
            .addressed_section("spool/native-turn", "thread/turn-out", EventId(1))
            .expect("addressed section");

        section.validate().expect("validated borrowed view");
        assert_eq!(section.bundle_address(), "bundle/native-turn");
        assert_eq!(section.spool().address, "spool/native-turn");
        assert_eq!(section.thread().address, "thread/turn-out");
        assert_eq!(section.occurrence().occurrence, EventId(1));
        assert_eq!(section.incidence().coefficient, 1);
        assert_eq!(section.entering_parametron().native, NativeStateId(0));
        assert_eq!(section.emitting_parametron().native, NativeStateId(1));
        assert_eq!(section.ordered_generator_word(), &[InputId(7)]);
        assert_eq!(
            section.reconstruction_fibre().occurrences,
            BTreeSet::from([EventId(1)])
        );
    }

    #[test]
    fn native_addressed_section_returns_exact_unsupported_families() {
        let bundle = bundle();
        let section = bundle
            .addressed_section("spool/native-turn", "thread/turn-out", EventId(1))
            .expect("addressed section");

        let receiver = ReceiverInsufficiency::receiver_outside_family(
            &section,
            ReceiverId(10),
            vec!["receiver 10 remains outside the admitted family".to_owned()],
        )
        .expect("receiver insufficiency");
        assert_eq!(receiver.at_occurrence, EventId(1));
        assert_eq!(receiver.native, NativeStateId(1));
        assert_eq!(receiver.retained_fibre, BTreeSet::from([EventId(1)]));
        assert!(matches!(
            receiver.cause,
            ReceiverInsufficiencyCause::ReceiverOutsideFamily { requested, admitted }
                if requested == ReceiverId(10)
                    && admitted == BTreeSet::from([ReceiverId(9)])
        ));

        let word = ReceiverInsufficiency::successor_word_outside_family(
            &section,
            vec![InputId(7), InputId(8)],
            vec!["generator 8 remains outside the admitted family".to_owned()],
        )
        .expect("successor insufficiency");
        assert!(matches!(
            word.cause,
            ReceiverInsufficiencyCause::SuccessorOutsideFamily {
                requested_word,
                admitted_generators,
            } if requested_word == vec![InputId(7), InputId(8)]
                && admitted_generators == BTreeSet::from([InputId(7)])
        ));

        let absent = ReceiverInsufficiency::section_outside_family(
            &section,
            EventId(3),
            vec!["occurrence 3 remains outside the admitted section family".to_owned()],
        )
        .expect("section insufficiency");
        assert!(matches!(
            absent.cause,
            ReceiverInsufficiencyCause::SectionOutsideFamily { requested, admitted }
                if requested == EventId(3)
                    && admitted == BTreeSet::from([EventId(1), EventId(2)])
        ));

        assert!(matches!(
            ReceiverInsufficiency::receiver_outside_family(
                &section,
                ReceiverId(9),
                vec!["not actually outside".to_owned()],
            ),
            Err(NativeSpoolRefusal::Insufficiency)
        ));
        assert!(matches!(
            ReceiverInsufficiency::successor_word_outside_family(
                &section,
                vec![InputId(7)],
                vec!["not actually outside".to_owned()],
            ),
            Err(NativeSpoolRefusal::Insufficiency)
        ));
        assert!(matches!(
            ReceiverInsufficiency::section_outside_family(
                &section,
                EventId(2),
                vec!["not actually outside".to_owned()],
            ),
            Err(NativeSpoolRefusal::Insufficiency)
        ));
    }

    #[test]
    fn serial_receipt_must_retain_the_complete_pullback_population() {
        let mut spool = spool();
        spool.serial_pullbacks[0].occurrences.clear();
        assert!(matches!(
            spool.validate(),
            Err(NativeSpoolRefusal::Pullback(_, _))
        ));
    }

    #[test]
    fn an_unobstructed_all_zero_thread_is_not_productive() {
        let mut thread = thread("thread/zero", 4, 20, 21, 0, 1, 7);
        for cell in &mut thread.parametrons {
            cell.section = ExactComplexWaveCurrent::zero();
            cell.current = ExactComplexWaveCurrent::zero();
        }
        assert!(matches!(
            thread.validate(),
            Err(NativeSpoolRefusal::Parametron(_))
        ));
    }

    #[test]
    fn insufficiency_exhibits_the_reopened_native_fibre() {
        let insufficiency = ReceiverInsufficiency {
            schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
            at_occurrence: EventId(8),
            native: NativeStateId(3),
            retained_fibre: BTreeSet::from([EventId(8), EventId(9)]),
            cause: ReceiverInsufficiencyCause::ReconstructionFibreReopened {
                separator: NativeShortestSeparator {
                    left: EventId(8),
                    right: EventId(9),
                    word: vec![InputId(4)],
                    receiver: ReceiverId(11),
                    left_observation: Observation(1),
                    right_observation: Observation(2),
                },
            },
            open_exterior: vec!["successor outside the admitted section".to_owned()],
        };
        insufficiency.validate().expect("exact insufficiency");
    }
}
