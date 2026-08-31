use std::collections::{BTreeMap, BTreeSet, VecDeque};

use holonic_engine::{
    native_spool::NativeSpoolBundle,
    receiver_exact_compression::{InputId, ReceiverId},
    receiver_history_compression::NativeStateId,
    BoundaryId, EventId,
};
use sha2::{Digest, Sha256};

use super::types::{
    AthenaNativeError, AthenaNativeRest, NativeSectionAddress, ReceiverHistoryRealizationPassage,
    ATHENA_NATIVE_REST_SCHEMA, RECEIVER_HISTORY_REALIZATION_SCHEMA,
};

impl ReceiverHistoryRealizationPassage {
    pub fn found(ecology: &NativeSpoolBundle) -> Result<Self, AthenaNativeError> {
        ecology
            .validate()
            .map_err(|error| AthenaNativeError::Ecology(error.to_string()))?;
        let passage = Self::projection(ecology);
        passage.validate(ecology)?;
        Ok(passage)
    }

    pub fn validate(&self, ecology: &NativeSpoolBundle) -> Result<(), AthenaNativeError> {
        ecology
            .validate()
            .map_err(|error| AthenaNativeError::Ecology(error.to_string()))?;
        if self.schema != RECEIVER_HISTORY_REALIZATION_SCHEMA {
            return Err(AthenaNativeError::Realization(
                "unknown receiver-history realization schema".to_owned(),
            ));
        }
        let expected = Self::projection(ecology);
        if self != &expected {
            return Err(AthenaNativeError::Realization(
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
            return Err(AthenaNativeError::Realization(
                "the addressed section population is empty or disconnected".to_owned(),
            ));
        }
        Ok(())
    }

    fn projection(ecology: &NativeSpoolBundle) -> Self {
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

impl AthenaNativeRest {
    pub fn found(ecology: NativeSpoolBundle) -> Result<Self, AthenaNativeError> {
        let realization = ReceiverHistoryRealizationPassage::found(&ecology)?;
        let rest = Self {
            schema: ATHENA_NATIVE_REST_SCHEMA.to_owned(),
            ecology,
            realization,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, AthenaNativeError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| AthenaNativeError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, AthenaNativeError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| AthenaNativeError::Wire(error.to_string()))
    }

    pub fn wire_sha256(&self) -> Result<String, AthenaNativeError> {
        Ok(Sha256::digest(self.canonical_bytes()?)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }

    pub fn validate(&self) -> Result<(), AthenaNativeError> {
        if self.schema != ATHENA_NATIVE_REST_SCHEMA {
            return Err(AthenaNativeError::Wire(
                "unknown Athena native rest schema".to_owned(),
            ));
        }
        self.realization.validate(&self.ecology)
    }
}

fn components_through_native_cells(
    ecology: &NativeSpoolBundle,
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
        components.push(
            reached
                .into_iter()
                .map(|at| sections[at].clone())
                .collect(),
        );
    }
    components
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_digest_is_testimony_not_the_structural_identity_operator() {
        assert_ne!(ATHENA_NATIVE_REST_SCHEMA, "sha256");
    }
}
