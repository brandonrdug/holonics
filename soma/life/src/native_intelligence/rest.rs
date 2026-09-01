use std::collections::{BTreeMap, BTreeSet, VecDeque};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        IntoDismantlingBoundaryReturn, NativeEcologyProfile, NativeTransportRequest,
        RestedTransportEcology,
    },
    native_spool::NativeSpoolConductReturn,
    native_spool::NativeTransportScaffold,
    receiver_exact_compression::{InputId, ReceiverId},
    receiver_history_compression::NativeStateId,
    BoundaryId, EventId,
};
use sha2::{Digest, Sha256};

use super::types::{
    NativeEcologyError, NativeEcologyRest, NativeSectionAddress, ReceiverHistoryRealizationPassage,
    NATIVE_ECOLOGY_REST_SCHEMA, RECEIVER_HISTORY_REALIZATION_SCHEMA,
};

/// Cold reconstruction and open testimony physically departed from one hot native ecology rest.
#[derive(Debug, PartialEq, Eq)]
pub struct DepartedDismantlingLanes<ColdWitness, Insufficiency> {
    pub cold_witness: ColdWitness,
    pub insufficiency: Insufficiency,
}

/// Consume a three-lane dismantling return into one hot rest plus physically separate testimony.
pub fn consume_dismantling_return<Returned>(
    returned: Returned,
) -> Result<
    (
        NativeEcologyRest,
        DepartedDismantlingLanes<Returned::ColdWitness, Returned::Insufficiency>,
    ),
    NativeEcologyError,
>
where
    Returned: IntoDismantlingBoundaryReturn<Productive = NativeTransportScaffold>,
{
    let (productive, cold_witness, insufficiency) = returned.into_lanes();
    let hot = NativeEcologyRest::found(productive)?;
    Ok((
        hot,
        DepartedDismantlingLanes {
            cold_witness,
            insufficiency,
        },
    ))
}

impl ReceiverHistoryRealizationPassage {
    pub fn found(ecology: &NativeTransportScaffold) -> Result<Self, NativeEcologyError> {
        ecology
            .validate()
            .map_err(|error| NativeEcologyError::Ecology(error.to_string()))?;
        let passage = Self::projection(ecology);
        passage.validate(ecology)?;
        Ok(passage)
    }

    pub fn validate(&self, ecology: &NativeTransportScaffold) -> Result<(), NativeEcologyError> {
        ecology
            .validate()
            .map_err(|error| NativeEcologyError::Ecology(error.to_string()))?;
        if self.schema != RECEIVER_HISTORY_REALIZATION_SCHEMA {
            return Err(NativeEcologyError::Realization(
                "unknown receiver-history realization schema".to_owned(),
            ));
        }
        let expected = Self::projection(ecology);
        if self != &expected {
            return Err(NativeEcologyError::Realization(
                "the section atlas is not the exact projection of the owned ecology".to_owned(),
            ));
        }
        if self.sections.is_empty()
            || self.ingress_sections.is_empty()
            || self.native_population.is_empty()
            || self.receiver_family.is_empty()
            || self.generator_family.is_empty()
            || self.boundary_population.is_empty()
            || self.connected_components.is_empty()
            || self.connected_components.iter().any(Vec::is_empty)
        {
            return Err(NativeEcologyError::Realization(
                "the addressed section population is empty or disconnected".to_owned(),
            ));
        }
        Ok(())
    }

    fn projection(ecology: &NativeTransportScaffold) -> Self {
        let mut sections = Vec::new();
        let mut ingress_sections = Vec::new();
        let mut native_population = BTreeSet::<NativeStateId>::new();
        let mut receiver_family = BTreeSet::<ReceiverId>::new();
        let mut generator_family = BTreeSet::<InputId>::new();
        let mut boundary_population = BTreeSet::<BoundaryId>::new();
        let mut open_exterior = ecology.open_exterior.clone();
        for spool in &ecology.spools {
            native_population.extend(spool.native_population.iter().copied());
            receiver_family.extend(spool.receiver_family.iter().copied());
            generator_family.extend(spool.generator_family.iter().copied());
            open_exterior.extend(spool.open_exterior.iter().cloned());
            for thread in &spool.threads {
                boundary_population.insert(thread.entering_boundary);
                boundary_population.insert(thread.emitting_boundary);
                open_exterior.extend(thread.open_exterior.iter().cloned());
                for occurrence in &thread.occurrences {
                    let address = NativeSectionAddress {
                        spool: spool.address.clone(),
                        thread: thread.address.clone(),
                        occurrence: occurrence.occurrence,
                    };
                    if occurrence.predecessor.is_none() {
                        ingress_sections.push(address.clone());
                    }
                    sections.push(address);
                }
            }
        }
        sections.sort();
        ingress_sections.sort();
        open_exterior.sort();
        open_exterior.dedup();
        let connected_components = components_through_native_cells(ecology, &sections);
        if connected_components.len() > 1 {
            open_exterior.push(format!(
                "{} causal components await a returned interaction",
                connected_components.len()
            ));
        }
        Self {
            schema: RECEIVER_HISTORY_REALIZATION_SCHEMA.to_owned(),
            sections,
            ingress_sections,
            native_population,
            receiver_family,
            generator_family,
            boundary_population,
            connected_components,
            open_exterior,
        }
    }
}

impl NativeEcologyRest {
    pub fn found(ecology: NativeTransportScaffold) -> Result<Self, NativeEcologyError> {
        let realization = ReceiverHistoryRealizationPassage::found(&ecology)?;
        let rest = Self {
            schema: NATIVE_ECOLOGY_REST_SCHEMA.to_owned(),
            ecology,
            realization,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeEcologyError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeEcologyError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeEcologyError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeEcologyError::Wire(error.to_string()))
    }

    pub fn wire_sha256(&self) -> Result<String, NativeEcologyError> {
        Ok(Sha256::digest(self.canonical_bytes()?)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }

    pub fn validate(&self) -> Result<(), NativeEcologyError> {
        if self.schema != NATIVE_ECOLOGY_REST_SCHEMA {
            return Err(NativeEcologyError::Wire(
                "unknown native ecology rest schema".to_owned(),
            ));
        }
        self.realization.validate(&self.ecology)
    }
}

impl RestedTransportEcology for NativeEcologyRest {
    type Error = NativeEcologyError;
    type Request = NativeTransportRequest;
    type Return = NativeSpoolConductReturn;
    type Profile<'a> = NativeEcologyProfile<'a>;

    fn validate_rest(&self) -> Result<(), Self::Error> {
        self.validate()
    }

    fn intrinsic_profile(&self) -> Result<Self::Profile<'_>, Self::Error> {
        self.ecology
            .intrinsic_holon_profile()
            .map_err(|error| NativeEcologyError::Ecology(error.to_string()))
    }

    fn conduct(&self, request: &Self::Request) -> Result<Self::Return, Self::Error> {
        RestedTransportEcology::conduct(&self.ecology, request)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()))
    }

    fn canonical_rest_bytes(&self) -> Result<Vec<u8>, Self::Error> {
        self.canonical_bytes()
    }
}

fn components_through_native_cells(
    ecology: &NativeTransportScaffold,
    sections: &[NativeSectionAddress],
) -> Vec<Vec<NativeSectionAddress>> {
    let mut native_to_sections = BTreeMap::<NativeStateId, BTreeSet<usize>>::new();
    let mut occurrence_to_section = BTreeMap::new();
    let section_positions = sections
        .iter()
        .enumerate()
        .map(|(at, address)| (address, at))
        .collect::<BTreeMap<_, _>>();
    let mut section_to_natives = vec![BTreeSet::new(); sections.len()];
    let mut found = 0usize;
    for spool in &ecology.spools {
        for thread in &spool.threads {
            for occurrence in &thread.occurrences {
                let address = NativeSectionAddress {
                    spool: spool.address.clone(),
                    thread: thread.address.clone(),
                    occurrence: occurrence.occurrence,
                };
                let Some(at) = section_positions.get(&address).copied() else {
                    return Vec::new();
                };
                let pair = BTreeSet::from([occurrence.entering_native, occurrence.emitting_native]);
                for native in &pair {
                    native_to_sections.entry(*native).or_default().insert(at);
                }
                occurrence_to_section.insert(occurrence.occurrence, at);
                section_to_natives[at] = pair;
                found += 1;
            }
        }
    }
    let mut mutual_neighbors = BTreeMap::<EventId, BTreeSet<EventId>>::new();
    for response in ecology
        .spools
        .iter()
        .flat_map(|spool| &spool.mutual_constitutive_responses)
    {
        mutual_neighbors
            .entry(response.left_occurrence)
            .or_default()
            .insert(response.right_occurrence);
        mutual_neighbors
            .entry(response.right_occurrence)
            .or_default()
            .insert(response.left_occurrence);
    }
    if sections.is_empty() || found != sections.len() {
        return Vec::new();
    }
    let mut unreached = (0..sections.len()).collect::<BTreeSet<_>>();
    let mut components = Vec::new();
    while let Some(start) = unreached.first().copied() {
        let mut reached = BTreeSet::from([start]);
        let mut queue = VecDeque::from([start]);
        let mut expanded_natives = BTreeSet::new();
        while let Some(at) = queue.pop_front() {
            for native in &section_to_natives[at] {
                if expanded_natives.insert(*native) {
                    for next in &native_to_sections[native] {
                        if reached.insert(*next) {
                            queue.push_back(*next);
                        }
                    }
                }
            }
            let occurrence = sections[at].occurrence;
            if let Some(neighbors) = mutual_neighbors.get(&occurrence) {
                for other in neighbors {
                    if let Some(next) = occurrence_to_section.get(other) {
                        if reached.insert(*next) {
                            queue.push_back(*next);
                        }
                    }
                }
            }
        }
        unreached.retain(|at| !reached.contains(at));
        components.push(reached.into_iter().map(|at| sections[at].clone()).collect());
    }
    components
}

#[cfg(test)]
mod tests {
    use super::*;

    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            lift_bf16_excitations, ExteriorModality, ForeignBf16Excitation,
        },
        receiver_exact_compression::ReceiverId,
        BoundaryId, EventId,
    };

    #[test]
    fn wire_digest_is_testimony_not_the_structural_identity_operator() {
        assert_ne!(NATIVE_ECOLOGY_REST_SCHEMA, "sha256");
    }

    #[test]
    fn dismantling_handoff_consumes_productive_scaffold_and_keeps_cold_testimony_outside_hot_rest()
    {
        let returned = lift_bf16_excitations(
            ReceiverId(7),
            vec![ForeignBf16Excitation {
                event: EventId(1),
                predecessor: None,
                entering_boundary: BoundaryId(10),
                emitting_boundary: BoundaryId(11),
                source_occurrence: "cold/source/text".to_owned(),
                exterior_modality: ExteriorModality::Text,
                entering_codewords: vec![0x3f80],
                returned_codewords: vec![0x4000],
                interventions: BTreeSet::from(["cold/intervention".to_owned()]),
                receiver_consequences: BTreeSet::from(["cold/consequence".to_owned()]),
            }],
        )
        .expect("lift");
        let (hot, departed) = consume_dismantling_return(returned).expect("handoff");
        hot.validate().expect("hot rest");
        let wire = String::from_utf8(hot.canonical_bytes().expect("wire"))
            .expect("JSON")
            .to_ascii_lowercase();
        for cold in [
            "cold/source",
            "cold/intervention",
            "cold/consequence",
            "text",
        ] {
            assert!(!wire.contains(cold));
        }
        assert_eq!(departed.cold_witness.excitations.len(), 1);
        assert_eq!(departed.insufficiency.retained_fibre.len(), 1);
    }
}
