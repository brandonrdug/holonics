//! Receiver-history descent for addressed cultivated factor realizations.
//!
//! A returned factor is not global morphology merely because it can be represented in the same
//! ambient projection. Its founding causal sections are additional receiver faces. This module
//! composes those faces with an already-founded receiver-history action and recomputes the exact
//! stable quotient. The result is the coarsest refinement on which every original receiver,
//! admitted generator, and factor-support predicate factors.
//!
//! ```text
//!             T_i                         U_i
//!       X ------------> X          Q ------------> Q
//!       |               |          |               |
//!     q'|               |q'        | factor faces  |
//!       v               v          v               v
//!      Q' ------------> Q'       {outside, inside}
//!             U'_i
//! ```
//!
//! The owner retains the full reconstruction fibres and one shortest, zero-generator separator
//! for every proper support. Unknown source current returns an obstruction. No foreign tower is a
//! fallback for that refusal.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    cuda_refine::CudaRefineExecutor,
    receiver_exact_compression::{
        InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress, compress_on_device,
    },
    receiver_history_compression::{
        NativeStateId, PartialReceiverHistoryCompression, ReceiverHistoryCompression,
        ReceiverHistoryRefusal,
    },
};

use super::{
    foreign_section_descent::{
        ForeignCoefficientReceiverQuotient, ForeignCoefficientWordSeparator,
    },
    session_factor_complex::TowerFactorRealization,
};

const SCHEMA: &str = "holonic-engine.phoenix.receiver-restricted-factor-descent.v1";
const ANATOMY_SCHEMA: &str = "holonic-engine.phoenix.native-anatomy-rest.v1";

/// One factor realization and the complete source occurrences which founded it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistorySupportedFactor {
    pub realization: TowerFactorRealization,
    pub founding_sources: BTreeSet<ItemId>,
}

/// The immediate receiver which reopens a support erased by a poorer quotient.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactorSupportSeparator {
    pub receiver: ReceiverId,
    pub inside: ItemId,
    pub outside: ItemId,
    pub inside_observation: Observation,
    pub outside_observation: Observation,
}

/// One realization after its support has descended to the refined native action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DescendedFactorSupport {
    pub realization: TowerFactorRealization,
    pub founding_sources: BTreeSet<ItemId>,
    pub native_support: BTreeSet<NativeStateId>,
    pub separator: FactorSupportSeparator,
}

/// Deterministic apparatus testimony for founding the refined quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactorDescentApparatus {
    pub device: String,
    pub launches: u64,
    pub cpu_device_partition_equal: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Source-detached standing for the descended support relation.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverRestrictedFactorDescent {
    pub schema: String,
    pub quotient: ReceiverHistoryCompression,
    pub factors: Vec<DescendedFactorSupport>,
    pub apparatus: FactorDescentApparatus,
}

/// What one native history section admits without opening the foreign tower.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AdmittedFactorSection {
    pub source: ItemId,
    pub native: NativeStateId,
    pub reconstruction_fibre: BTreeSet<ItemId>,
    pub realization_addresses: BTreeSet<String>,
}

/// One caused successor occurrence entering the already-founded factor-support receiver. The
/// foreign carrier class is a receiver face, never its occurrence identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccessorSupportOccurrence {
    pub occurrence: String,
    pub predecessor_occurrence: String,
    pub parent_source: ItemId,
    pub emitted_native_address: u32,
    pub foreign_receiver_class: usize,
}

/// The support current transported from one addressed parent into its successor occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarriedSuccessorSupport {
    pub occurrence: String,
    pub predecessor_occurrence: String,
    pub parent_source: ItemId,
    pub parent_native: NativeStateId,
    pub parent_reconstruction_fibre: BTreeSet<ItemId>,
    pub emitted_native_address: u32,
    pub foreign_receiver_class: usize,
    pub support_receiver_class: usize,
    pub realization_addresses: BTreeSet<String>,
}

/// Complete occurrence fibre of the emitted Athena face and factor support. Foreign carrier
/// classes are retained as reconstruction testimony and never participate in this class key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccessorSupportReceiverClass {
    pub class: usize,
    pub emitted_native_address: u32,
    pub foreign_receiver_classes: BTreeSet<usize>,
    pub realization_addresses: BTreeSet<String>,
    pub occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignSupportReopening {
    pub foreign_receiver_class: usize,
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub left_realization_addresses: BTreeSet<String>,
    pub right_realization_addresses: BTreeSet<String>,
}

/// Typed addressed passage obtained by carrying the existing support receiver over emitted
/// successors. It creates no self-loop or invented later observation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SuccessorSupportPassage {
    pub occurrences: Vec<CarriedSuccessorSupport>,
    pub classes: Vec<SuccessorSupportReceiverClass>,
    pub foreign_support_reopenings: Vec<ForeignSupportReopening>,
}

/// One addressed coefficient occurrence before the native anatomical quotient is taken.
/// `foreign_receiver_class` and `inherited_history_state` are construction testimony only.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnatomicalOccurrence {
    pub occurrence: String,
    pub predecessor_occurrence: Option<String>,
    pub coefficient_node: usize,
    pub inherited_history_state: u64,
    pub foreign_receiver_class: usize,
    pub emitted_native_address: u32,
    pub emitted_surface: String,
    pub realization_addresses: BTreeSet<String>,
}

/// Exact receiver-face catalogs used to found the anatomy. Ordinals are canonical addresses only;
/// no arithmetic or order relation between observations is consumed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnatomyReceiverCatalog {
    pub emitted_address_faces: BTreeMap<u32, Observation>,
    pub surface_faces: BTreeMap<String, Observation>,
    pub factor_support_faces: Vec<(BTreeSet<String>, Observation)>,
}

/// One native cell class and its complete local incidence at the declared aperture.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeAnatomyClass {
    pub native: NativeStateId,
    pub occurrences: Vec<String>,
    pub coefficient_nodes: Vec<usize>,
    pub inherited_history_states: BTreeSet<u64>,
    pub foreign_receiver_classes: BTreeSet<usize>,
    pub emitted_native_address: u32,
    pub emitted_surface: String,
    pub realization_addresses: BTreeSet<String>,
    pub predecessor_classes: BTreeSet<NativeStateId>,
    pub successor_classes: BTreeSet<NativeStateId>,
}

/// The functional receiver-to-receiver map from one foreign carrier class into native anatomy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignToNativeClassFactor {
    pub foreign_receiver_class: usize,
    pub native: NativeStateId,
    pub occurrences: Vec<String>,
}

/// A distinction visible to the foreign coordinate receiver which the complete declared native
/// receiver/history family lawfully condenses.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignOnlyDistinction {
    pub native: NativeStateId,
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub left_foreign_receiver_class: usize,
    pub right_foreign_receiver_class: usize,
    pub foreign_separator: ForeignCoefficientWordSeparator,
}

/// Independent lineages realizing one receiver/history consequence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalogousAnatomyWitness {
    pub native: NativeStateId,
    pub left_occurrence: String,
    pub right_occurrence: String,
}

/// Two analogous sections which also share an addressed cultivated morphology ancestor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HomologousAnatomyWitness {
    pub native: NativeStateId,
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub common_realization_addresses: BTreeSet<String>,
}

/// Deterministic apparatus testimony for the native anatomical quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeAnatomyApparatus {
    pub device: String,
    pub launches: u64,
    pub cpu_device_partition_equal: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// Source-detached native anatomy. The foreign atlas remains only in the explicit factor and
/// reconstruction witnesses below; it never occurs in the native receiver key.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAnatomyRest {
    pub schema: String,
    pub quotient: PartialReceiverHistoryCompression,
    pub occurrences: Vec<AnatomicalOccurrence>,
    pub receivers: AnatomyReceiverCatalog,
    pub classes: Vec<NativeAnatomyClass>,
    pub foreign_to_native: Vec<ForeignToNativeClassFactor>,
    pub foreign_only_distinctions: Vec<ForeignOnlyDistinction>,
    pub analogous_sections: Vec<AnalogousAnatomyWitness>,
    pub homologous_sections: Vec<HomologousAnatomyWitness>,
    pub apparatus: NativeAnatomyApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OutOfSectionObstruction {
    pub source: ItemId,
    pub declared_source_population: usize,
    pub foreign_fallback_permitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ReceiverRestrictedFactorRefusal {
    #[error("the support relation is empty, total, duplicated, or leaves the source population")]
    InvalidSupport,
    #[error("the factor realization address is empty or repeated")]
    InvalidAddress,
    #[error("the refined quotient failed to separate one factor support")]
    SupportDoesNotFactor,
    #[error("receiver-history descent refused: {0}")]
    History(#[from] ReceiverHistoryRefusal),
    #[error("resident quotient refinement refused: {0}")]
    Apparatus(String),
    #[error(
        "foreign receiver class {foreign_receiver_class} crosses native classes {left_native:?} and {right_native:?}"
    )]
    ForeignReceiverInsufficient {
        foreign_receiver_class: usize,
        left_native: NativeStateId,
        right_native: NativeStateId,
    },
    #[error("receiver-restricted factor wire refused: {0}")]
    Wire(String),
}

impl ReceiverRestrictedFactorDescent {
    /// Found the exact support refinement on the resident quotient apparatus and compare it to the
    /// exact reference before admitting the result.
    pub fn found_on_device(
        inherited: &ReceiverHistoryCompression,
        supported: Vec<HistorySupportedFactor>,
        executor: &mut CudaRefineExecutor,
    ) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        inherited.validate()?;
        let system = SupportRefinementSystem::found(inherited, supported)?;
        let reference = compress(&system);
        let launches_before = executor.launches();
        let exact = compress_on_device(&system, executor)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Apparatus(error.to_string()))?;
        if reference != exact {
            return Err(ReceiverRestrictedFactorRefusal::Apparatus(
                "resident and reference factor-support quotients disagree".to_owned(),
            ));
        }
        let quotient = ReceiverHistoryCompression::found(&system, &exact)?;
        let factors = system.descend(&quotient)?;
        let result = Self {
            schema: SCHEMA.to_owned(),
            quotient,
            factors,
            apparatus: FactorDescentApparatus {
                device: executor.device_name().to_owned(),
                launches: executor.launches().saturating_sub(launches_before),
                cpu_device_partition_equal: true,
                cpu_semantic_replay_after_device: false,
            },
        };
        result.validate()?;
        Ok(result)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        let descent: Self = serde_json::from_slice(bytes)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Wire(error.to_string()))?;
        descent.validate()?;
        Ok(descent)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ReceiverRestrictedFactorRefusal> {
        serde_json::to_vec(self)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), ReceiverRestrictedFactorRefusal> {
        if self.schema != SCHEMA
            || self.factors.is_empty()
            || !self.apparatus.cpu_device_partition_equal
            || self.apparatus.cpu_semantic_replay_after_device
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        self.quotient.validate()?;
        let source_population = self
            .quotient
            .source_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let native_population = self
            .quotient
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut addresses = BTreeSet::new();
        for factor in &self.factors {
            if factor.realization.address.is_empty()
                || !addresses.insert(factor.realization.address.as_str())
                || factor.founding_sources.is_empty()
                || factor.founding_sources == source_population
                || !factor.founding_sources.is_subset(&source_population)
                || factor.native_support.is_empty()
                || !factor.native_support.is_subset(&native_population)
                || !factor.founding_sources.contains(&factor.separator.inside)
                || factor.founding_sources.contains(&factor.separator.outside)
                || factor.separator.inside_observation == factor.separator.outside_observation
            {
                return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
            }
            for fibre in &self.quotient.reconstruction_fibres {
                let intersects = !fibre.sources.is_disjoint(&factor.founding_sources);
                let contained = fibre.sources.is_subset(&factor.founding_sources);
                if intersects != contained
                    || contained != factor.native_support.contains(&fibre.native)
                {
                    return Err(ReceiverRestrictedFactorRefusal::SupportDoesNotFactor);
                }
            }
        }
        Ok(())
    }

    /// Return only the factors whose exact support contains this source occurrence.
    pub fn admit_source(
        &self,
        source: ItemId,
    ) -> Result<AdmittedFactorSection, OutOfSectionObstruction> {
        let native = self
            .quotient
            .encode(source)
            .map_err(|_| OutOfSectionObstruction {
                source,
                declared_source_population: self.quotient.source_population.len(),
                foreign_fallback_permitted: false,
            })?;
        let reconstruction_fibre = self
            .quotient
            .reconstruction_fibres
            .iter()
            .find(|fibre| fibre.native == native)
            .map(|fibre| fibre.sources.clone())
            .expect("validated quotient retains every native fibre");
        let realization_addresses = self
            .factors
            .iter()
            .filter(|factor| factor.native_support.contains(&native))
            .map(|factor| factor.realization.address.clone())
            .collect();
        Ok(AdmittedFactorSection {
            source,
            native,
            reconstruction_fibre,
            realization_addresses,
        })
    }

    /// Carry the exact support face from each addressed parent into its emitted successor. The
    /// morphology has not changed during emission, so support is transported with the occurrence;
    /// if two foreign-equal successors carry different support, the support receiver explicitly
    /// reopens that foreign quotient instead of being erased.
    pub fn carry_successor_support(
        &self,
        entering: Vec<SuccessorSupportOccurrence>,
    ) -> Result<SuccessorSupportPassage, ReceiverRestrictedFactorRefusal> {
        self.validate()?;
        if entering.is_empty()
            || entering.iter().any(|occurrence| {
                occurrence.occurrence.is_empty() || occurrence.predecessor_occurrence.is_empty()
            })
            || entering
                .iter()
                .map(|occurrence| occurrence.occurrence.as_str())
                .collect::<BTreeSet<_>>()
                .len()
                != entering.len()
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }

        let mut carried = Vec::with_capacity(entering.len());
        let mut class_by_face = BTreeMap::<(u32, Vec<String>), usize>::new();
        let mut class_occurrences = Vec::<Vec<String>>::new();
        let mut class_faces = Vec::<(u32, BTreeSet<String>, BTreeSet<usize>)>::new();
        for occurrence in entering {
            let admitted = self
                .admit_source(occurrence.parent_source)
                .map_err(|_| ReceiverRestrictedFactorRefusal::InvalidSupport)?;
            let face = admitted
                .realization_addresses
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            let key = (occurrence.emitted_native_address, face);
            let class = match class_by_face.get(&key) {
                Some(class) => {
                    class_faces[*class]
                        .2
                        .insert(occurrence.foreign_receiver_class);
                    *class
                }
                None => {
                    let class = class_by_face.len();
                    class_by_face.insert(key, class);
                    class_occurrences.push(Vec::new());
                    class_faces.push((
                        occurrence.emitted_native_address,
                        admitted.realization_addresses.clone(),
                        BTreeSet::from([occurrence.foreign_receiver_class]),
                    ));
                    class
                }
            };
            class_occurrences[class].push(occurrence.occurrence.clone());
            carried.push(CarriedSuccessorSupport {
                occurrence: occurrence.occurrence,
                predecessor_occurrence: occurrence.predecessor_occurrence,
                parent_source: occurrence.parent_source,
                parent_native: admitted.native,
                parent_reconstruction_fibre: admitted.reconstruction_fibre,
                emitted_native_address: occurrence.emitted_native_address,
                foreign_receiver_class: occurrence.foreign_receiver_class,
                support_receiver_class: class,
                realization_addresses: admitted.realization_addresses,
            });
        }
        let classes = class_faces
            .iter()
            .enumerate()
            .map(
                |(
                    class,
                    (emitted_native_address, realization_addresses, foreign_receiver_classes),
                )| {
                    SuccessorSupportReceiverClass {
                        class,
                        emitted_native_address: *emitted_native_address,
                        foreign_receiver_classes: foreign_receiver_classes.clone(),
                        realization_addresses: realization_addresses.clone(),
                        occurrences: class_occurrences[class].clone(),
                    }
                },
            )
            .collect::<Vec<_>>();
        let mut foreign_support_reopenings = Vec::new();
        for left in 0..carried.len() {
            for right in left + 1..carried.len() {
                if carried[left].foreign_receiver_class == carried[right].foreign_receiver_class
                    && carried[left].support_receiver_class != carried[right].support_receiver_class
                {
                    foreign_support_reopenings.push(ForeignSupportReopening {
                        foreign_receiver_class: carried[left].foreign_receiver_class,
                        left_occurrence: carried[left].occurrence.clone(),
                        right_occurrence: carried[right].occurrence.clone(),
                        left_realization_addresses: carried[left].realization_addresses.clone(),
                        right_realization_addresses: carried[right].realization_addresses.clone(),
                    });
                }
            }
        }
        Ok(SuccessorSupportPassage {
            occurrences: carried,
            classes,
            foreign_support_reopenings,
        })
    }
}

impl NativeAnatomyRest {
    /// Found the coarsest exact Athena receiver/history anatomy on the resident quotient
    /// apparatus. The CPU reading is an admission reference taken before the resident deed; it is
    /// never a semantic replay after the device return.
    pub fn found_on_device(
        occurrences: Vec<AnatomicalOccurrence>,
        foreign: &ForeignCoefficientReceiverQuotient,
        executor: &mut CudaRefineExecutor,
    ) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        let system = NativeAnatomySystem::found(occurrences, foreign)?;
        let reference = compress(&system);
        let launches_before = executor.launches();
        let exact = compress_on_device(&system, executor)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Apparatus(error.to_string()))?;
        if reference != exact {
            return Err(ReceiverRestrictedFactorRefusal::Apparatus(
                "resident and reference native-anatomy quotients disagree".to_owned(),
            ));
        }
        let quotient = PartialReceiverHistoryCompression::found(&system, &exact)?;
        let native_by_item = quotient
            .quotient
            .iter()
            .map(|assignment| (assignment.source, assignment.native))
            .collect::<BTreeMap<_, _>>();

        let mut classes = Vec::with_capacity(quotient.native_population.len());
        for fibre in &quotient.reconstruction_fibres {
            let members = fibre
                .sources
                .iter()
                .map(|source| {
                    system
                        .occurrences
                        .get(source.0 as usize)
                        .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let first = members
                .first()
                .copied()
                .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
            if members.iter().any(|member| {
                member.emitted_native_address != first.emitted_native_address
                    || member.emitted_surface != first.emitted_surface
                    || member.realization_addresses != first.realization_addresses
            }) {
                return Err(ReceiverRestrictedFactorRefusal::SupportDoesNotFactor);
            }
            let mut predecessor_classes = BTreeSet::new();
            let mut successor_classes = BTreeSet::new();
            for source in &fibre.sources {
                let item = *source;
                if let Some(predecessor) = system.predecessor.get(&item) {
                    predecessor_classes.insert(native_by_item[predecessor]);
                }
                for successor in system
                    .successors
                    .iter()
                    .filter_map(|((from, _), to)| (*from == item).then_some(*to))
                {
                    successor_classes.insert(native_by_item[&successor]);
                }
            }
            classes.push(NativeAnatomyClass {
                native: fibre.native,
                occurrences: members
                    .iter()
                    .map(|member| member.occurrence.clone())
                    .collect(),
                coefficient_nodes: members
                    .iter()
                    .map(|member| member.coefficient_node)
                    .collect(),
                inherited_history_states: members
                    .iter()
                    .map(|member| member.inherited_history_state)
                    .collect(),
                foreign_receiver_classes: members
                    .iter()
                    .map(|member| member.foreign_receiver_class)
                    .collect(),
                emitted_native_address: first.emitted_native_address,
                emitted_surface: first.emitted_surface.clone(),
                realization_addresses: first.realization_addresses.clone(),
                predecessor_classes,
                successor_classes,
            });
        }

        let mut foreign_factors = BTreeMap::<usize, (NativeStateId, Vec<String>)>::new();
        for (item, occurrence) in system.occurrences.iter().enumerate() {
            let native = native_by_item[&ItemId(item as u64)];
            match foreign_factors.get_mut(&occurrence.foreign_receiver_class) {
                Some((existing, addresses)) => {
                    if *existing != native {
                        return Err(
                            ReceiverRestrictedFactorRefusal::ForeignReceiverInsufficient {
                                foreign_receiver_class: occurrence.foreign_receiver_class,
                                left_native: *existing,
                                right_native: native,
                            },
                        );
                    }
                    addresses.push(occurrence.occurrence.clone());
                }
                None => {
                    foreign_factors.insert(
                        occurrence.foreign_receiver_class,
                        (native, vec![occurrence.occurrence.clone()]),
                    );
                }
            }
        }
        let foreign_to_native = foreign_factors
            .into_iter()
            .map(
                |(foreign_receiver_class, (native, occurrences))| ForeignToNativeClassFactor {
                    foreign_receiver_class,
                    native,
                    occurrences,
                },
            )
            .collect::<Vec<_>>();

        let mut foreign_only_distinctions = Vec::new();
        for separator in &foreign.shortest_separators {
            let left = system
                .occurrences
                .get(separator.left_history)
                .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
            let right = system
                .occurrences
                .get(separator.right_history)
                .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
            let left_native = native_by_item[&ItemId(separator.left_history as u64)];
            let right_native = native_by_item[&ItemId(separator.right_history as u64)];
            if left_native == right_native
                && left.foreign_receiver_class != right.foreign_receiver_class
            {
                foreign_only_distinctions.push(ForeignOnlyDistinction {
                    native: left_native,
                    left_occurrence: left.occurrence.clone(),
                    right_occurrence: right.occurrence.clone(),
                    left_foreign_receiver_class: left.foreign_receiver_class,
                    right_foreign_receiver_class: right.foreign_receiver_class,
                    foreign_separator: separator.clone(),
                });
            }
        }

        let mut analogous_sections = Vec::new();
        let mut homologous_sections = Vec::new();
        for class in &classes {
            for left in 0..class.occurrences.len() {
                for right in left + 1..class.occurrences.len() {
                    analogous_sections.push(AnalogousAnatomyWitness {
                        native: class.native,
                        left_occurrence: class.occurrences[left].clone(),
                        right_occurrence: class.occurrences[right].clone(),
                    });
                    let left_occurrence = system
                        .occurrences
                        .iter()
                        .find(|occurrence| occurrence.occurrence == class.occurrences[left])
                        .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
                    let right_occurrence = system
                        .occurrences
                        .iter()
                        .find(|occurrence| occurrence.occurrence == class.occurrences[right])
                        .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
                    let common_realization_addresses = left_occurrence
                        .realization_addresses
                        .intersection(&right_occurrence.realization_addresses)
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    if !common_realization_addresses.is_empty() {
                        homologous_sections.push(HomologousAnatomyWitness {
                            native: class.native,
                            left_occurrence: class.occurrences[left].clone(),
                            right_occurrence: class.occurrences[right].clone(),
                            common_realization_addresses,
                        });
                    }
                }
            }
        }

        let rest = Self {
            schema: ANATOMY_SCHEMA.to_owned(),
            quotient,
            occurrences: system.occurrences,
            receivers: system.receivers,
            classes,
            foreign_to_native,
            foreign_only_distinctions,
            analogous_sections,
            homologous_sections,
            apparatus: NativeAnatomyApparatus {
                device: executor.device_name().to_owned(),
                launches: executor.launches().saturating_sub(launches_before),
                cpu_device_partition_equal: true,
                cpu_semantic_replay_after_device: false,
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ReceiverRestrictedFactorRefusal> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| ReceiverRestrictedFactorRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), ReceiverRestrictedFactorRefusal> {
        if self.schema != ANATOMY_SCHEMA
            || self.occurrences.is_empty()
            || !self.apparatus.cpu_device_partition_equal
            || self.apparatus.cpu_semantic_replay_after_device
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        self.quotient.validate()?;
        if self.quotient.source_population.len() != self.occurrences.len()
            || self.classes.len() != self.quotient.native_population.len()
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        let occurrence_addresses = self
            .occurrences
            .iter()
            .map(|occurrence| occurrence.occurrence.as_str())
            .collect::<BTreeSet<_>>();
        if occurrence_addresses.len() != self.occurrences.len() {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        let class_occurrences = self
            .classes
            .iter()
            .flat_map(|class| class.occurrences.iter().map(String::as_str))
            .collect::<BTreeSet<_>>();
        if class_occurrences != occurrence_addresses {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        let foreign_occurrences = self
            .foreign_to_native
            .iter()
            .flat_map(|factor| factor.occurrences.iter().map(String::as_str))
            .collect::<BTreeSet<_>>();
        if foreign_occurrences != occurrence_addresses {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        Ok(())
    }
}

struct NativeAnatomySystem {
    occurrences: Vec<AnatomicalOccurrence>,
    receivers: AnatomyReceiverCatalog,
    predecessor: BTreeMap<ItemId, ItemId>,
    successors: BTreeMap<(ItemId, InputId), ItemId>,
    inputs: Vec<InputId>,
}

impl NativeAnatomySystem {
    fn found(
        mut occurrences: Vec<AnatomicalOccurrence>,
        foreign: &ForeignCoefficientReceiverQuotient,
    ) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        occurrences.sort_by_key(|occurrence| occurrence.coefficient_node);
        if occurrences.is_empty()
            || foreign.history_to_class.len() != occurrences.len()
            || occurrences.iter().enumerate().any(|(node, occurrence)| {
                occurrence.coefficient_node != node
                    || occurrence.occurrence.is_empty()
                    || occurrence.emitted_surface.is_empty()
                    || occurrence.foreign_receiver_class != foreign.history_to_class[node]
            })
            || occurrences
                .iter()
                .map(|occurrence| occurrence.occurrence.as_str())
                .collect::<BTreeSet<_>>()
                .len()
                != occurrences.len()
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        let by_address = occurrences
            .iter()
            .enumerate()
            .map(|(node, occurrence)| (occurrence.occurrence.as_str(), ItemId(node as u64)))
            .collect::<BTreeMap<_, _>>();
        let mut predecessor = BTreeMap::new();
        let mut successors = BTreeMap::new();
        let mut inputs = BTreeSet::new();
        for (node, occurrence) in occurrences.iter().enumerate() {
            if let Some(parent_address) = &occurrence.predecessor_occurrence {
                let parent = *by_address
                    .get(parent_address.as_str())
                    .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
                let child = ItemId(node as u64);
                if parent == child {
                    return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
                }
                let parent_face = occurrences[parent.0 as usize].emitted_native_address;
                let input = InputId(u64::from(parent_face));
                if predecessor.insert(child, parent).is_some()
                    || successors.insert((parent, input), child).is_some()
                {
                    return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
                }
                inputs.insert(input);
            }
        }
        let emitted_address_faces = occurrences
            .iter()
            .map(|occurrence| occurrence.emitted_native_address)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(face, address)| (address, Observation(face as u64)))
            .collect::<BTreeMap<_, _>>();
        let surface_faces = occurrences
            .iter()
            .map(|occurrence| occurrence.emitted_surface.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(face, surface)| (surface, Observation(face as u64)))
            .collect::<BTreeMap<_, _>>();
        let factor_support_faces = occurrences
            .iter()
            .map(|occurrence| occurrence.realization_addresses.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(face, support)| (support, Observation(face as u64)))
            .collect::<Vec<_>>();
        let receivers = AnatomyReceiverCatalog {
            emitted_address_faces,
            surface_faces,
            factor_support_faces,
        };
        Ok(Self {
            occurrences,
            receivers,
            predecessor,
            successors,
            inputs: inputs.into_iter().collect(),
        })
    }
}

impl ObservedSystem for NativeAnatomySystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.occurrences.len())
            .map(|item| ItemId(item as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1), ReceiverId(2)]
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let occurrence = &self.occurrences[item.0 as usize];
        match receiver.0 {
            0 => self.receivers.emitted_address_faces[&occurrence.emitted_native_address],
            1 => self.receivers.surface_faces[&occurrence.emitted_surface],
            2 => self
                .receivers
                .factor_support_faces
                .iter()
                .find_map(|(support, face)| {
                    (*support == occurrence.realization_addresses).then_some(*face)
                })
                .expect("founded anatomy catalogs every factor-support face"),
            _ => panic!("receiver left the founded anatomy family"),
        }
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.successors.get(&(item, input)).copied()
    }

    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        Some(
            self.successors
                .iter()
                .filter_map(|((from, generator), to)| (*generator == input).then_some((*from, *to)))
                .collect(),
        )
    }
}

struct SupportRefinementSystem<'a> {
    inherited: &'a ReceiverHistoryCompression,
    supported: Vec<HistorySupportedFactor>,
    original_receivers: Vec<ReceiverId>,
    support_receivers: Vec<ReceiverId>,
    source_successors: BTreeMap<(ItemId, InputId), ItemId>,
}

impl<'a> SupportRefinementSystem<'a> {
    fn found(
        inherited: &'a ReceiverHistoryCompression,
        supported: Vec<HistorySupportedFactor>,
    ) -> Result<Self, ReceiverRestrictedFactorRefusal> {
        let source_population = inherited
            .source_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut addresses = BTreeSet::new();
        if supported.is_empty()
            || supported.iter().any(|factor| {
                factor.realization.address.is_empty()
                    || !addresses.insert(factor.realization.address.as_str())
            })
        {
            return Err(ReceiverRestrictedFactorRefusal::InvalidAddress);
        }
        if supported.iter().any(|factor| {
            factor.founding_sources.is_empty()
                || factor.founding_sources == source_population
                || !factor.founding_sources.is_subset(&source_population)
        }) {
            return Err(ReceiverRestrictedFactorRefusal::InvalidSupport);
        }
        let original_receivers = inherited
            .receiver_factors
            .iter()
            .map(|factor| factor.receiver)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let first_support = original_receivers
            .iter()
            .map(|receiver| receiver.0)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
        let support_receivers = (0..supported.len())
            .map(|at| {
                u64::try_from(at)
                    .ok()
                    .and_then(|at| first_support.checked_add(at))
                    .map(ReceiverId)
                    .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let source_successors = inherited
            .generators
            .iter()
            .flat_map(|square| {
                square
                    .source
                    .iter()
                    .map(move |edge| ((edge.from, square.generator), edge.to))
            })
            .collect();
        Ok(Self {
            inherited,
            supported,
            original_receivers,
            support_receivers,
            source_successors,
        })
    }

    fn descend(
        &self,
        quotient: &ReceiverHistoryCompression,
    ) -> Result<Vec<DescendedFactorSupport>, ReceiverRestrictedFactorRefusal> {
        self.supported
            .iter()
            .zip(&self.support_receivers)
            .map(|(factor, receiver)| {
                let native_support = quotient
                    .reconstruction_fibres
                    .iter()
                    .filter(|fibre| fibre.sources.is_subset(&factor.founding_sources))
                    .map(|fibre| fibre.native)
                    .collect::<BTreeSet<_>>();
                let inside = *factor
                    .founding_sources
                    .iter()
                    .next()
                    .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
                let outside = self
                    .inherited
                    .source_population
                    .iter()
                    .find(|source| !factor.founding_sources.contains(source))
                    .copied()
                    .ok_or(ReceiverRestrictedFactorRefusal::InvalidSupport)?;
                Ok(DescendedFactorSupport {
                    realization: factor.realization.clone(),
                    founding_sources: factor.founding_sources.clone(),
                    native_support,
                    separator: FactorSupportSeparator {
                        receiver: *receiver,
                        inside,
                        outside,
                        inside_observation: Observation(1),
                        outside_observation: Observation(0),
                    },
                })
            })
            .collect()
    }
}

impl ObservedSystem for SupportRefinementSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inherited.source_population.clone()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.original_receivers
            .iter()
            .chain(&self.support_receivers)
            .copied()
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inherited
            .generators
            .iter()
            .map(|square| square.generator)
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        if let Some(at) = self
            .support_receivers
            .iter()
            .position(|candidate| *candidate == receiver)
        {
            return Observation(u64::from(
                self.supported[at].founding_sources.contains(&item),
            ));
        }
        let native = self
            .inherited
            .encode(item)
            .expect("the refinement uses the inherited complete source population");
        self.inherited
            .decode(native, receiver)
            .expect("the refinement uses the inherited complete receiver family")
            .observation
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.source_successors.get(&(item, input)).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::receiver_exact_compression::{ReceiverExactCompression, compress};

    struct PairedHistories;

    impl ObservedSystem for PairedHistories {
        fn items(&self) -> Vec<ItemId> {
            (0..4).map(ItemId).collect()
        }

        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }

        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }

        fn observation(&self, item: ItemId, _: ReceiverId) -> Observation {
            Observation(item.0 % 2)
        }

        fn successor(&self, item: ItemId, _: InputId) -> Option<ItemId> {
            Some(ItemId((item.0 + 2) % 4))
        }
    }

    fn inherited() -> ReceiverHistoryCompression {
        let system = PairedHistories;
        let exact: ReceiverExactCompression = compress(&system);
        ReceiverHistoryCompression::found(&system, &exact).expect("inherited quotient")
    }

    fn realization() -> TowerFactorRealization {
        TowerFactorRealization {
            address: "factor-a".to_owned(),
            source_factor_addresses: vec!["returned-a".to_owned()],
            target_row: 7,
            selector_coordinate: 3,
            delta_entry: 1,
            selector_entry: 1,
        }
    }

    #[test]
    fn support_face_refines_the_quotient_and_gates_the_factor() {
        let inherited = inherited();
        assert_eq!(inherited.native_population.len(), 2);
        let system = SupportRefinementSystem::found(
            &inherited,
            vec![HistorySupportedFactor {
                realization: realization(),
                founding_sources: BTreeSet::from([ItemId(0), ItemId(1)]),
            }],
        )
        .expect("support system");
        let exact = compress(&system);
        let quotient = ReceiverHistoryCompression::found(&system, &exact).expect("refinement");
        let factors = system.descend(&quotient).expect("descent");
        let descent = ReceiverRestrictedFactorDescent {
            schema: SCHEMA.to_owned(),
            quotient,
            factors,
            apparatus: FactorDescentApparatus {
                device: "reference-test".to_owned(),
                launches: 0,
                cpu_device_partition_equal: true,
                cpu_semantic_replay_after_device: false,
            },
        };
        descent.validate().expect("valid descent");
        assert_eq!(descent.quotient.native_population.len(), 4);
        assert_eq!(
            descent
                .admit_source(ItemId(0))
                .expect("supported")
                .realization_addresses,
            BTreeSet::from(["factor-a".to_owned()])
        );
        assert!(
            descent
                .admit_source(ItemId(2))
                .expect("known control")
                .realization_addresses
                .is_empty()
        );
        assert_eq!(
            descent
                .admit_source(ItemId(99))
                .expect_err("outside source population")
                .foreign_fallback_permitted,
            false
        );
        let bytes = descent.canonical_bytes().expect("canonical rest");
        assert_eq!(
            ReceiverRestrictedFactorDescent::read(&bytes).expect("remount"),
            descent
        );

        let carried = descent
            .carry_successor_support(vec![
                SuccessorSupportOccurrence {
                    occurrence: "successor-a".to_owned(),
                    predecessor_occurrence: "parent-a".to_owned(),
                    parent_source: ItemId(0),
                    emitted_native_address: 11,
                    foreign_receiver_class: 7,
                },
                SuccessorSupportOccurrence {
                    occurrence: "successor-b".to_owned(),
                    predecessor_occurrence: "parent-b".to_owned(),
                    parent_source: ItemId(1),
                    emitted_native_address: 11,
                    foreign_receiver_class: 8,
                },
            ])
            .expect("carried support");
        assert_eq!(carried.classes.len(), 1);
        assert_eq!(carried.classes[0].occurrences.len(), 2);
        assert_eq!(
            carried.classes[0].foreign_receiver_classes,
            BTreeSet::from([7, 8])
        );
        assert!(carried.foreign_support_reopenings.is_empty());

        let reopened = descent
            .carry_successor_support(vec![
                SuccessorSupportOccurrence {
                    occurrence: "successor-a".to_owned(),
                    predecessor_occurrence: "parent-a".to_owned(),
                    parent_source: ItemId(0),
                    emitted_native_address: 11,
                    foreign_receiver_class: 7,
                },
                SuccessorSupportOccurrence {
                    occurrence: "successor-control".to_owned(),
                    predecessor_occurrence: "parent-control".to_owned(),
                    parent_source: ItemId(2),
                    emitted_native_address: 11,
                    foreign_receiver_class: 7,
                },
            ])
            .expect("support reopening");
        assert_eq!(reopened.classes.len(), 2);
        assert_eq!(reopened.foreign_support_reopenings.len(), 1);
    }
}
