use holonic_engine::{
    native_spool::{ReceiverInsufficiency, ReceiverInsufficiencyCause},
    receiver_exact_compression::ReceiverId,
    EventId,
};

use super::types::{
    AthenaNativeConsequence, AthenaNativeError, AthenaNativePassage, AthenaNativeRest,
    NativeConductedSection, NativeSectionAddress,
};

impl AthenaNativeRest {
    /// Conduct one addressed native occurrence through the single ecology. An admitted dependent
    /// receiver returns its exact face; an unsupported receiver or section returns a concrete
    /// retained fibre. No exterior realization, lexical route, or fallback is reachable.
    pub fn conduct(
        &self,
        requested: &NativeSectionAddress,
        receiver: ReceiverId,
    ) -> Result<AthenaNativeConsequence, AthenaNativeError> {
        self.validate()?;
        let Some(anchor_address) = self.realization.ingress_sections.first() else {
            return Err(AthenaNativeError::Realization(
                "the ecology has no ingress section".to_owned(),
            ));
        };
        let anchor = self
            .ecology
            .addressed_section(
                &anchor_address.spool,
                &anchor_address.thread,
                anchor_address.occurrence,
            )
            .map_err(|error| AthenaNativeError::Realization(error.to_string()))?;
        if !self.realization.sections.contains(requested) {
            return ReceiverInsufficiency::section_outside_family(
                &anchor,
                requested.occurrence,
                vec!["the entering section is outside this Athena ecology".to_owned()],
            )
            .map(AthenaNativeConsequence::Insufficient)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()));
        }
        let section = self
            .ecology
            .addressed_section(&requested.spool, &requested.thread, requested.occurrence)
            .map_err(|error| AthenaNativeError::Realization(error.to_string()))?;
        if !section.spool().receiver_family.contains(&receiver) {
            return ReceiverInsufficiency::receiver_outside_family(
                &section,
                receiver,
                vec!["the requested dependent receiver is outside this native family".to_owned()],
            )
            .map(AthenaNativeConsequence::Insufficient)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()));
        }
        let word = section.ordered_generator_word().to_vec();
        if word
            .iter()
            .any(|generator| !section.spool().generator_family.contains(generator))
        {
            return ReceiverInsufficiency::successor_word_outside_family(
                &section,
                word,
                vec!["the section's ordered successor leaves the admitted family".to_owned()],
            )
            .map(AthenaNativeConsequence::Insufficient)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()));
        }

        let occurrence = section.occurrence().clone();
        let incidence = section.incidence().clone();
        let entering_parametron = section.entering_parametron().clone();
        let emitting_parametron = section.emitting_parametron().clone();
        let constitutive_response = section
            .thread()
            .constitutive_responses
            .iter()
            .find(|response| {
                response.native == occurrence.emitting_native && response.receiver == receiver
            })
            .cloned()
            .ok_or_else(|| {
                AthenaNativeError::Conduct(
                    "the admitted receiver has no constitutive response at the emitted native"
                        .to_owned(),
                )
            })?;
        let observation = section
            .thread()
            .receiver_consequences
            .iter()
            .find(|consequence| {
                consequence.native == occurrence.emitting_native && consequence.receiver == receiver
            })
            .map(|consequence| consequence.observation)
            .ok_or_else(|| {
                AthenaNativeError::Conduct(
                    "the admitted receiver has no consequence at the emitted native".to_owned(),
                )
            })?;
        let reconstruction_fibre = section.reconstruction_fibre().occurrences.clone();
        let mut mutual_constitutive_responses = section
            .spool()
            .mutual_constitutive_responses
            .iter()
            .filter(|response| {
                response.left_occurrence == occurrence.occurrence
                    || response.right_occurrence == occurrence.occurrence
            })
            .cloned()
            .collect::<Vec<_>>();
        mutual_constitutive_responses
            .sort_by_key(|response| (response.left_occurrence, response.right_occurrence));
        let mut successors = self
            .realization
            .sections
            .iter()
            .filter_map(|address| {
                let candidate = self
                    .ecology
                    .addressed_section(&address.spool, &address.thread, address.occurrence)
                    .ok()?;
                (candidate.occurrence().predecessor == Some(occurrence.occurrence))
                    .then_some(address.clone())
            })
            .collect::<Vec<_>>();
        successors.sort();

        let mut resident_word = self
            .ecology
            .mount_word(&requested.spool, &word)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()))?;
        let word_return = resident_word
            .conduct(&[occurrence.entering_native], receiver)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()))?;
        if word_return.native_end.as_slice() != [occurrence.emitting_native]
            || word_return.observations.as_slice() != [observation]
            || word_return.apparatus.invariant_transport_reuploaded
        {
            return Err(AthenaNativeError::Conduct(
                "the resident word did not return the addressed dependent face".to_owned(),
            ));
        }
        let mut resident_current = self
            .ecology
            .mount_thread_current(&requested.spool, &requested.thread)
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()))?;
        let current_return = resident_current
            .conduct()
            .map_err(|error| AthenaNativeError::Conduct(error.to_string()))?;
        if current_return.invariant_transport_reuploaded
            || current_return.cpu_semantic_replay_after_device
            || current_return.binary_receiver_taken
        {
            return Err(AthenaNativeError::Conduct(
                "the Complex-Parametron current left the resident pre-locking path".to_owned(),
            ));
        }
        let mut open_exterior = section.thread().open_exterior.clone();
        open_exterior.extend(self.realization.open_exterior.iter().cloned());
        open_exterior.sort();
        open_exterior.dedup();
        let conducted = NativeConductedSection {
            address: requested.clone(),
            predecessor: occurrence.predecessor,
            entering_boundary: section.thread().entering_boundary,
            emitting_boundary: section.thread().emitting_boundary,
            entering_port: occurrence.entering_port,
            emitting_port: occurrence.emitting_port,
            entering_native: occurrence.entering_native,
            emitting_native: occurrence.emitting_native,
            incidence,
            entering_section: entering_parametron.section,
            entering_current: entering_parametron.current,
            emitting_section: emitting_parametron.section,
            emitting_current: emitting_parametron.current,
            relative_phase: emitting_parametron.relative_phase,
            hand: emitting_parametron.hand,
            constitutive_response,
            mutual_constitutive_responses,
            ordered_word: word,
            receiver,
            observation,
            reconstruction_fibre,
            successor_sections: successors,
            open_exterior,
        };
        Ok(AthenaNativeConsequence::Returned(AthenaNativePassage {
            schema: "soma-life.athena-native-passage.v2".to_owned(),
            rest_wire_sha256: self.wire_sha256()?,
            section: conducted,
            word_return,
            current_return,
            source_fallback_permitted: false,
        }))
    }

    /// Ask the open boundary about an occurrence without inventing a state for absent material.
    pub fn conduct_occurrence(
        &self,
        occurrence: EventId,
        receiver: ReceiverId,
    ) -> Result<AthenaNativeConsequence, AthenaNativeError> {
        let requested = self
            .realization
            .sections
            .iter()
            .find(|address| address.occurrence == occurrence)
            .cloned()
            .unwrap_or_else(|| NativeSectionAddress {
                spool: String::new(),
                thread: String::new(),
                occurrence,
            });
        self.conduct(&requested, receiver)
    }

    pub fn returns_insufficiency(
        consequence: &AthenaNativeConsequence,
    ) -> Option<&ReceiverInsufficiencyCause> {
        match consequence {
            AthenaNativeConsequence::Returned(_) => None,
            AthenaNativeConsequence::Insufficient(insufficiency) => Some(&insufficiency.cause),
        }
    }
}
