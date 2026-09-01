use super::refusal::NativeSpoolRefusal;
use super::*;
use crate::cuda_refine::{
    ResidentComplexIncidence, ResidentComplexIncidenceReturn, ResidentNativeWord,
    ResidentNativeWordReturn,
};
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
    pub(crate) spool_address: String,
    pub(crate) states: Vec<NativeStateId>,
    pub(crate) state_index: BTreeMap<NativeStateId, u32>,
    /// States on which the mounted ordered word has a realized descent rather than an open face.
    pub(crate) active_states: BTreeSet<NativeStateId>,
    pub(crate) receiver_factors: BTreeMap<(NativeStateId, ReceiverId), Observation>,
    pub(crate) device: String,
    pub(crate) block_threads: u32,
    pub(crate) resident: ResidentNativeWord,
}

/// One resident native Complex-Parametron thread. It owns its exact current front and card
/// incidence; neither source coordinates nor an exterior reconstruction edge are reachable.
pub struct ResidentNativeThreadCurrent {
    pub(crate) front: Vec<ExactComplexWaveCurrent>,
    pub(crate) resident: ResidentComplexIncidence,
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
        if native_start
            .iter()
            .any(|native| !self.active_states.contains(native))
        {
            return Err(NativeSpoolRefusal::UnknownNative(
                native_start
                    .iter()
                    .find(|native| !self.active_states.contains(native))
                    .copied()
                    .unwrap_or(NativeStateId(0)),
            ));
        }
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
