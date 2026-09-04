use holonic_engine::{
    native_spool::{ReceiverInsufficiency, ReceiverInsufficiencyCause},
    receiver_exact_compression::ReceiverId,
    EventId,
};

use super::types::{
    NativeBatchSectionAddress, NativeConductBatchPassage, NativeConductConsequence,
    NativeConductPassage, NativeConductedSection, NativeEcologyError, NativeEcologyRest,
    NativeSectionAddress, NativeThreadResidentBatchReturn,
};

impl NativeEcologyRest {
    pub fn conduct_population(
        &self,
        receiver: ReceiverId,
    ) -> Result<NativeConductBatchPassage, NativeEcologyError> {
        self.validate()?;
        let mut reconstruction_fibres = Vec::new();
        let mut fibre_addresses = BTreeMap::new();
        for spool in &self.ecology.spools {
            for fibre in &spool.reconstruction_fibres {
                let address = u32::try_from(reconstruction_fibres.len()).map_err(|_| {
                    NativeEcologyError::Conduct("the fibre atlas exceeded its address".to_owned())
                })?;
                fibre_addresses.insert((spool.address.as_str(), fibre.native), address);
                reconstruction_fibres.push(fibre.clone());
            }
        }
        let mut sections = Vec::with_capacity(self.realization.sections.len());
        for spool in &self.ecology.spools {
            for thread in &spool.threads {
                for occurrence in &thread.occurrences {
                    sections.push(NativeBatchSectionAddress {
                        section: NativeSectionAddress {
                            spool: spool.address.clone(),
                            thread: thread.address.clone(),
                            occurrence: occurrence.occurrence,
                        },
                        reconstruction_fibre: fibre_addresses
                            [&(spool.address.as_str(), occurrence.emitting_native)],
                    });
                }
            }
        }
        sections.sort_by(|left, right| left.section.cmp(&right.section));
        if sections
            .iter()
            .zip(&self.realization.sections)
            .any(|(section, expected)| &section.section != expected)
            || sections.len() != self.realization.sections.len()
        {
            return Err(NativeEcologyError::Conduct(
                "the batch section atlas departed from the admitted realization".to_owned(),
            ));
        }
        let mut resident_threads = Vec::new();
        for spool in &self.ecology.spools {
            if !spool.receiver_family.contains(&receiver) {
                return Err(NativeEcologyError::Conduct(
                    "the batch receiver is outside one spool family".to_owned(),
                ));
            }
            for thread in &spool.threads {
                let entering = thread
                    .occurrences
                    .iter()
                    .map(|occurrence| occurrence.entering_native)
                    .collect::<BTreeSet<_>>();
                let mut resident_word = self
                    .ecology
                    .mount_word(&spool.address, &thread.chronology)
                    .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
                let mut word_returns = Vec::new();
                for native in entering {
                    let returned = resident_word
                        .conduct(&[native], receiver)
                        .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
                    if returned.apparatus.invariant_transport_reuploaded {
                        return Err(NativeEcologyError::Conduct(
                            "the batch word reuploaded invariant transport".to_owned(),
                        ));
                    }
                    word_returns.push(returned);
                }
                let mut current = self
                    .ecology
                    .mount_thread_current(&spool.address, &thread.address)
                    .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
                let current_return = current
                    .conduct()
                    .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
                if current_return.invariant_transport_reuploaded
                    || current_return.cpu_semantic_replay_after_device
                    || current_return.binary_receiver_taken
                {
                    return Err(NativeEcologyError::Conduct(
                        "the batch current left the resident pre-locking path".to_owned(),
                    ));
                }
                resident_threads.push(NativeThreadResidentBatchReturn {
                    spool: spool.address.clone(),
                    thread: thread.address.clone(),
                    word_returns,
                    current_return,
                });
            }
        }
        Ok(NativeConductBatchPassage {
            schema: "soma-life.native-conduct-batch-passage.v1".to_owned(),
            rest_wire_sha256: self.wire_sha256()?,
            sections,
            reconstruction_fibres,
            resident_threads,
            source_fallback_permitted: false,
        })
    }

    /// Conduct one addressed native occurrence through the single ecology. An admitted dependent
    /// receiver returns its exact face; an unsupported receiver or section returns a concrete
    /// retained fibre. No exterior realization, lexical route, or fallback is reachable.
    pub fn conduct(
        &self,
        requested: &NativeSectionAddress,
        receiver: ReceiverId,
    ) -> Result<NativeConductConsequence, NativeEcologyError> {
        self.validate()?;
        let Some(anchor_address) = self.realization.ingress_sections.first() else {
            return Err(NativeEcologyError::Realization(
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
            .map_err(|error| NativeEcologyError::Realization(error.to_string()))?;
        if !self.realization.sections.contains(requested) {
            return ReceiverInsufficiency::section_outside_family(
                &anchor,
                requested.occurrence,
                vec!["the entering section is outside this native ecology".to_owned()],
            )
            .map(NativeConductConsequence::Insufficient)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()));
        }
        let section = self
            .ecology
            .addressed_section(&requested.spool, &requested.thread, requested.occurrence)
            .map_err(|error| NativeEcologyError::Realization(error.to_string()))?;
        if !section.spool().receiver_family.contains(&receiver) {
            return ReceiverInsufficiency::receiver_outside_family(
                &section,
                receiver,
                vec!["the requested dependent receiver is outside this native family".to_owned()],
            )
            .map(NativeConductConsequence::Insufficient)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()));
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
            .map(NativeConductConsequence::Insufficient)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()));
        }

        let mut conducted = self.project_admitted_section(requested, receiver)?;
        conducted.successor_sections = self.successor_sections(requested.occurrence);
        let mut resident_word = self
            .ecology
            .mount_word(&requested.spool, &conducted.ordered_word)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
        let word_return = resident_word
            .conduct(&[conducted.entering_native], receiver)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
        if word_return.native_end.as_slice() != [conducted.emitting_native]
            || word_return.observations.as_slice() != [conducted.observation]
            || word_return.apparatus.invariant_transport_reuploaded
        {
            return Err(NativeEcologyError::Conduct(
                "the resident word did not return the addressed dependent face".to_owned(),
            ));
        }
        let mut resident_current = self
            .ecology
            .mount_thread_current(&requested.spool, &requested.thread)
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
        let current_return = resident_current
            .conduct()
            .map_err(|error| NativeEcologyError::Conduct(error.to_string()))?;
        if current_return.invariant_transport_reuploaded
            || current_return.cpu_semantic_replay_after_device
            || current_return.binary_receiver_taken
        {
            return Err(NativeEcologyError::Conduct(
                "the Complex-Parametron current left the resident pre-locking path".to_owned(),
            ));
        }
        Ok(NativeConductConsequence::Returned(NativeConductPassage {
            schema: "soma-life.native-conduct-passage.v1".to_owned(),
            rest_wire_sha256: self.wire_sha256()?,
            section: conducted,
            word_return,
            current_return,
            source_fallback_permitted: false,
        }))
    }

    /// Project one already-admitted section from the native topology without launching apparatus.
    /// This is the shared structural owner used by both resident conduct and factorized product
    /// formation; it performs no source lookup and no receiver condensation beyond the named face.
    pub fn project_admitted_section(
        &self,
        requested: &NativeSectionAddress,
        receiver: ReceiverId,
    ) -> Result<NativeConductedSection, NativeEcologyError> {
        let section = self
            .ecology
            .addressed_section(&requested.spool, &requested.thread, requested.occurrence)
            .map_err(|error| NativeEcologyError::Realization(error.to_string()))?;
        if !section.spool().receiver_family.contains(&receiver) {
            return Err(NativeEcologyError::Conduct(
                "the projected section or receiver is outside the admitted family".to_owned(),
            ));
        }
        let word = section.ordered_generator_word().to_vec();
        if word
            .iter()
            .any(|generator| !section.spool().generator_family.contains(generator))
        {
            return Err(NativeEcologyError::Conduct(
                "the projected section leaves the admitted successor family".to_owned(),
            ));
        }
        let occurrence = section.occurrence().clone();
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
                NativeEcologyError::Conduct(
                    "the projected section has no emitted constitutive face".to_owned(),
                )
            })?;
        let observation = section
            .thread()
            .receiver_consequences
            .iter()
            .find(|face| face.native == occurrence.emitting_native && face.receiver == receiver)
            .map(|face| face.observation)
            .ok_or_else(|| {
                NativeEcologyError::Conduct(
                    "the projected section has no emitted receiver consequence".to_owned(),
                )
            })?;
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
        let mut open_exterior = section.thread().open_exterior.clone();
        open_exterior.extend(self.realization.open_exterior.iter().cloned());
        open_exterior.sort();
        open_exterior.dedup();
        Ok(NativeConductedSection {
            address: requested.clone(),
            predecessor: occurrence.predecessor,
            entering_boundary: section.thread().entering_boundary,
            emitting_boundary: section.thread().emitting_boundary,
            entering_port: occurrence.entering_port,
            emitting_port: occurrence.emitting_port,
            entering_native: occurrence.entering_native,
            emitting_native: occurrence.emitting_native,
            incidence: section.incidence().clone(),
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
            reconstruction_fibre: section.reconstruction_fibre().occurrences.clone(),
            successor_sections: Vec::new(),
            open_exterior,
        })
    }

    pub fn successor_sections(&self, occurrence: EventId) -> Vec<NativeSectionAddress> {
        let mut successors = self
            .ecology
            .spools
            .iter()
            .flat_map(|spool| {
                spool.threads.iter().flat_map(move |thread| {
                    thread.occurrences.iter().filter_map(move |candidate| {
                        (candidate.predecessor == Some(occurrence)).then(|| NativeSectionAddress {
                            spool: spool.address.clone(),
                            thread: thread.address.clone(),
                            occurrence: candidate.occurrence,
                        })
                    })
                })
            })
            .collect::<Vec<_>>();
        successors.sort();
        successors
    }

    /// Project the complete admitted population in one traversal. This is the owner used by
    /// factorized product construction; it prevents one address lookup and one successor scan per
    /// section while returning exactly the same structural sections as the scalar projector.
    pub fn project_admitted_population(
        &self,
        receiver: ReceiverId,
    ) -> Result<BTreeMap<NativeSectionAddress, NativeConductedSection>, NativeEcologyError> {
        self.validate()?;
        let mut successors = BTreeMap::<EventId, Vec<NativeSectionAddress>>::new();
        for spool in &self.ecology.spools {
            for thread in &spool.threads {
                for occurrence in &thread.occurrences {
                    if let Some(predecessor) = occurrence.predecessor {
                        successors
                            .entry(predecessor)
                            .or_default()
                            .push(NativeSectionAddress {
                                spool: spool.address.clone(),
                                thread: thread.address.clone(),
                                occurrence: occurrence.occurrence,
                            });
                    }
                }
            }
        }
        for sections in successors.values_mut() {
            sections.sort();
        }
        let mut projected = BTreeMap::new();
        for spool in &self.ecology.spools {
            if !spool.receiver_family.contains(&receiver) {
                return Err(NativeEcologyError::Conduct(
                    "the projected population receiver is outside one spool family".to_owned(),
                ));
            }
            for thread in &spool.threads {
                let incidence = thread
                    .incidence
                    .iter()
                    .map(|term| (term.occurrence, term))
                    .collect::<BTreeMap<_, _>>();
                let parametrons = thread
                    .parametrons
                    .iter()
                    .map(|cell| (cell.native, cell))
                    .collect::<BTreeMap<_, _>>();
                for occurrence in &thread.occurrences {
                    let address = NativeSectionAddress {
                        spool: spool.address.clone(),
                        thread: thread.address.clone(),
                        occurrence: occurrence.occurrence,
                    };
                    let entering =
                        parametrons
                            .get(&occurrence.entering_native)
                            .ok_or_else(|| {
                                NativeEcologyError::Conduct(
                                    "the projected population lost an entering parametron"
                                        .to_owned(),
                                )
                            })?;
                    let emitting =
                        parametrons
                            .get(&occurrence.emitting_native)
                            .ok_or_else(|| {
                                NativeEcologyError::Conduct(
                                    "the projected population lost an emitting parametron"
                                        .to_owned(),
                                )
                            })?;
                    let constitutive_response = thread
                        .constitutive_responses
                        .iter()
                        .find(|response| {
                            response.native == occurrence.emitting_native
                                && response.receiver == receiver
                        })
                        .cloned()
                        .ok_or_else(|| {
                            NativeEcologyError::Conduct(
                                "the projected population lost a constitutive response".to_owned(),
                            )
                        })?;
                    let observation = thread
                        .receiver_consequences
                        .iter()
                        .find(|face| {
                            face.native == occurrence.emitting_native && face.receiver == receiver
                        })
                        .map(|face| face.observation)
                        .ok_or_else(|| {
                            NativeEcologyError::Conduct(
                                "the projected population lost a receiver consequence".to_owned(),
                            )
                        })?;
                    let fibre = spool
                        .reconstruction_fibres
                        .iter()
                        .find(|fibre| fibre.native == occurrence.emitting_native)
                        .ok_or_else(|| {
                            NativeEcologyError::Conduct(
                                "the projected population lost a reconstruction fibre".to_owned(),
                            )
                        })?;
                    let mut mutual = spool
                        .mutual_constitutive_responses
                        .iter()
                        .filter(|response| {
                            response.left_occurrence == occurrence.occurrence
                                || response.right_occurrence == occurrence.occurrence
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    mutual.sort_by_key(|response| {
                        (response.left_occurrence, response.right_occurrence)
                    });
                    let mut open_exterior = thread.open_exterior.clone();
                    open_exterior.extend(self.realization.open_exterior.iter().cloned());
                    open_exterior.sort();
                    open_exterior.dedup();
                    projected.insert(
                        address.clone(),
                        NativeConductedSection {
                            address,
                            predecessor: occurrence.predecessor,
                            entering_boundary: thread.entering_boundary,
                            emitting_boundary: thread.emitting_boundary,
                            entering_port: occurrence.entering_port,
                            emitting_port: occurrence.emitting_port,
                            entering_native: occurrence.entering_native,
                            emitting_native: occurrence.emitting_native,
                            incidence: (*incidence[&occurrence.occurrence]).clone(),
                            entering_section: entering.section.clone(),
                            entering_current: entering.current.clone(),
                            emitting_section: emitting.section.clone(),
                            emitting_current: emitting.current.clone(),
                            relative_phase: emitting.relative_phase.clone(),
                            hand: emitting.hand,
                            constitutive_response,
                            mutual_constitutive_responses: mutual,
                            ordered_word: thread.chronology.clone(),
                            receiver,
                            observation,
                            reconstruction_fibre: fibre.occurrences.clone(),
                            successor_sections: successors
                                .get(&occurrence.occurrence)
                                .cloned()
                                .unwrap_or_default(),
                            open_exterior,
                        },
                    );
                }
            }
        }
        if projected.keys().ne(self.realization.sections.iter()) {
            return Err(NativeEcologyError::Realization(
                "the one-pass projection departed from the admitted section atlas".to_owned(),
            ));
        }
        Ok(projected)
    }

    /// Ask the open boundary about an occurrence without inventing a state for absent material.
    pub fn conduct_occurrence(
        &self,
        occurrence: EventId,
        receiver: ReceiverId,
    ) -> Result<NativeConductConsequence, NativeEcologyError> {
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
        consequence: &NativeConductConsequence,
    ) -> Option<&ReceiverInsufficiencyCause> {
        match consequence {
            NativeConductConsequence::Returned(_) => None,
            NativeConductConsequence::Insufficient(insufficiency) => Some(&insufficiency.cause),
        }
    }
}
use std::collections::{BTreeMap, BTreeSet};
