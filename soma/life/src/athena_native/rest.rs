use std::collections::{BTreeMap, BTreeSet, VecDeque};

use holonic_engine::{
    BoundaryId,
    native_spool::NativeSpoolBundle,
    receiver_exact_compression::{InputId, ReceiverId},
    receiver_history_compression::NativeStateId,
};
use sha2::{Digest, Sha256};

use super::types::{
    ATHENA_NATIVE_REST_SCHEMA, AthenaNativeError, AthenaNativeRest, NativeSectionAddress,
    RECEIVER_HISTORY_REALIZATION_SCHEMA, ReceiverHistoryRealizationPassage,
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
        for address in &self.sections {
            ecology
                .addressed_section(&address.spool, &address.thread, address.occurrence)
                .map_err(|error| AthenaNativeError::Realization(error.to_string()))?;
        }
        if self.sections.is_empty()
            || self.ingress_sections.is_empty()
            || self.native_population.is_empty()
            || self.receiver_family.is_empty()
            || self.generator_family.is_empty()
            || self.boundary_population.is_empty()
            || !connected_through_native_cells(ecology, &self.sections)
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
        Self {
            schema: RECEIVER_HISTORY_REALIZATION_SCHEMA.to_owned(),
            sections,
            ingress_sections,
            native_population,
            receiver_family,
            generator_family,
            boundary_population,
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

fn connected_through_native_cells(
    ecology: &NativeSpoolBundle,
    sections: &[NativeSectionAddress],
) -> bool {
    let mut native_to_sections = BTreeMap::<NativeStateId, BTreeSet<usize>>::new();
    let mut occurrence_to_section = BTreeMap::new();
    let mut section_to_natives = Vec::with_capacity(sections.len());
    for (at, address) in sections.iter().enumerate() {
        let Ok(section) =
            ecology.addressed_section(&address.spool, &address.thread, address.occurrence)
        else {
            return false;
        };
        let pair = BTreeSet::from([
            section.occurrence().entering_native,
            section.occurrence().emitting_native,
        ]);
        for native in &pair {
            native_to_sections.entry(*native).or_default().insert(at);
        }
        occurrence_to_section.insert(section.occurrence().occurrence, at);
        section_to_natives.push(pair);
    }
    if sections.is_empty() {
        return false;
    }
    let mut reached = BTreeSet::from([0usize]);
    let mut queue = VecDeque::from([0usize]);
    while let Some(at) = queue.pop_front() {
        for native in &section_to_natives[at] {
            for next in &native_to_sections[native] {
                if reached.insert(*next) {
                    queue.push_back(*next);
                }
            }
        }
        let occurrence = sections[at].occurrence;
        for response in ecology
            .spools
            .iter()
            .flat_map(|spool| &spool.mutual_constitutive_responses)
            .filter(|response| {
                response.left_occurrence == occurrence || response.right_occurrence == occurrence
            })
        {
            let other = if response.left_occurrence == occurrence {
                response.right_occurrence
            } else {
                response.left_occurrence
            };
            if let Some(next) = occurrence_to_section.get(&other) {
                if reached.insert(*next) {
                    queue.push_back(*next);
                }
            }
        }
    }
    reached.len() == sections.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_digest_is_testimony_not_the_structural_identity_operator() {
        assert_ne!(ATHENA_NATIVE_REST_SCHEMA, "sha256");
    }
}
