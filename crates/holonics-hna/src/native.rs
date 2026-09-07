//! Native HNA application interface over the existing developing ecology. This module owns
//! exterior codecs and linear source-handle delivery, never a replacement learning mechanism.
use holonic_engine::dimensional_wave::ExactComplexWaveCurrent;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveFibreError, ConstitutiveReading, NativeConstitutiveEcology,
    NativeCurrentOccurrence, NativeEmissionHandle, NativeJunctionSeed, NativePhaseCurrent,
};
use holonic_engine::resident_section::{ResidentSurface, TransferCensus};
use serde::{Deserialize, Serialize};
use thiserror::Error;

mod wire;
pub use wire::*;
mod batch;
pub use batch::NativeBatchReceive;
mod checkpoint;
pub use checkpoint::NativeSavedSession;
mod acoustic;
pub mod acoustic_field;
pub use acoustic::{
    AcousticApplication, AcousticInterruption, AcousticPendingReceive, AcousticRun,
    AcousticRunOptions, AcousticSavedApplication, append_acoustic, resume_acoustic,
    run_acoustic_with_options,
};
mod speech;
pub use speech::{
    SpeechExposureApplication, SpeechPendingReceive, SpeechRun, SpeechRunOptions,
    SpeechSavedApplication, resume_speech, run_speech_with_options,
};
mod wave_control;
pub use wave_control::{
    PendingWaveReceive, WAVE_CONTROL_SCHEMA, WaveApplication, WaveBoundary, WaveChange,
    WaveControlRun, WaveControlSpec, WaveCycle, WaveInterruption, WaveIntervention, WaveRunOptions,
    WaveSavedApplication, WaveWorldSpec, resume_wave_control, run_wave_control,
    run_wave_control_with_options,
};

#[derive(Debug, Error)]
pub enum NativeSessionError {
    #[error("native artifact I/O: {0}")]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Publication(#[from] crate::publication::PublicationError),
    #[error(transparent)]
    Engine(#[from] ConstitutiveFibreError),
    #[error(transparent)]
    Codec(#[from] serde_json::Error),
    #[error("native application: {0}")]
    Application(String),
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeSessionAnatomy {
    pub model_kind: &'static str,
    pub nodes: usize,
    pub occurrences: usize,
    pub frame: u64,
    pub confirmed_rank: usize,
    pub available_sources: Vec<u64>,
    pub uncertain: bool,
    pub census: TransferCensus,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFrameWire {
    pub ordinal: u64,
    pub root_to_local: Vec<CurrentWire>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeReceivedWire {
    pub source: Option<u64>,
    pub native_source_occurrence: usize,
    pub former_receiver_fibre: ReceiverWire,
    pub arrived: CurrentWire,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSessionStep {
    /// A coordinate of a linear handle in THIS running session, not a portable source identity.
    pub source: u64,
    pub native_occurrence: usize,
    pub predecessor_state: Option<usize>,
    pub received_from: Option<u64>,
    pub native_received_from: Option<usize>,
    pub frame: NativeFrameWire,
    pub local_source_currents: Vec<CurrentWire>,
    pub root_source_currents: Vec<CurrentWire>,
    pub receiver: ReceiverWire,
    pub received_difference: Option<NativeReceivedWire>,
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeRelationSnapshot {
    pub after_occurrences: usize,
    pub frame: NativeFrameWire,
    pub source_extent: usize,
    pub target_extent: usize,
    /// Echelon basis of paired current points, not a selected total weight matrix or a checkpoint.
    pub paired_basis: Vec<Vec<RationalWire>>,
}

pub struct NativeSession<'chart> {
    body: NativeConstitutiveEcology<'chart>,
    sources: Vec<Option<NativeEmissionHandle>>,
    confirmed_rank: usize,
}

/// One mount and one continuing owner for the entire callback. Persistent native artifacts are
/// a separate construction, not an inherited-model checkpoint masquerading as this body.
pub fn with_native_session<R>(
    spec: &NativeModelSpec,
    operation: impl FnOnce(&mut NativeSession<'_>) -> Result<R, NativeSessionError>,
) -> Result<R, NativeSessionError> {
    let material = spec.material()?;
    let readout =
        ResidentReadout::new().map_err(|e| NativeSessionError::Application(e.to_string()))?;
    let surface = ResidentSurface::on(&readout)
        .map_err(|e| NativeSessionError::Application(e.to_string()))?;
    let body = NativeConstitutiveEcology::found(&surface, material)?;
    let mut session = NativeSession {
        body,
        sources: Vec::new(),
        confirmed_rank: 0,
    };
    let returned = operation(&mut session);
    drop(session);
    returned
}

impl NativeSession<'_> {
    pub fn nodes(&self) -> usize {
        self.body.material().len()
    }
    pub fn occurrence_count(&self) -> usize {
        self.body.occurrence_count()
    }
    /// O(1) exterior delivery-slot check; this is not a lookup of a model answer.
    pub fn has_source(&self, source: u64) -> bool {
        usize::try_from(source)
            .ok()
            .and_then(|s| self.sources.get(s))
            .is_some_and(Option::is_some)
    }
    pub fn matches_untouched_seed(
        &self,
        spec: &NativeModelSpec,
    ) -> Result<bool, NativeSessionError> {
        Ok(self.occurrence_count() == 0
            && self.body.recharts().is_empty()
            && self.body.incidence_changes().is_empty()
            && self.body.material() == spec.material()?)
    }
    pub fn relation_snapshot(&self) -> Result<NativeRelationSnapshot, NativeSessionError> {
        let rest = self.body.inspect_relation()?;
        Ok(NativeRelationSnapshot {
            after_occurrences: self.body.occurrence_count(),
            frame: NativeFrameWire {
                ordinal: self.body.current_frame().ordinal(),
                root_to_local: self
                    .body
                    .current_frame()
                    .root_to_local()
                    .iter()
                    .map(|p| CurrentWire::from_current(&p.current()))
                    .collect(),
            },
            source_extent: 2 * self.body.material().len(),
            target_extent: 2,
            paired_basis: rest
                .intervals
                .chunks_exact(rest.width)
                .map(|r| {
                    r.iter()
                        .map(|(lo, hi)| {
                            if lo != hi {
                                return Err(NativeSessionError::Application(
                                    "relation is not a point chart".into(),
                                ));
                            }
                            Ok(RationalWire::integer(*lo))
                        })
                        .collect()
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
    pub fn inspect(&self) -> NativeSessionAnatomy {
        NativeSessionAnatomy {
            model_kind: "native-constitutive-phase-v1",
            nodes: self.body.material().len(),
            occurrences: self.body.occurrence_count(),
            frame: self.body.current_frame().ordinal(),
            confirmed_rank: self.confirmed_rank,
            available_sources: self
                .sources
                .iter()
                .enumerate()
                .filter_map(|(i, s)| s.as_ref().map(|_| i as u64))
                .collect(),
            uncertain: self.body.pending_lineage().is_some(),
            census: self.body.census(),
        }
    }

    pub fn receive(
        &mut self,
        current: &CurrentWire,
        source: Option<u64>,
    ) -> Result<NativeSessionStep, NativeSessionError> {
        let current = current.native()?;
        let next_source = u64::try_from(self.sources.len()).map_err(|_| {
            NativeSessionError::Application("session source coordinates exhausted".into())
        })?;
        self.sources
            .try_reserve(1)
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        let at = source
            .map(|s| {
                usize::try_from(s).map_err(|_| {
                    NativeSessionError::Application(
                        "source coordinate is outside this apparatus".into(),
                    )
                })
            })
            .transpose()?;
        let mut occurrence = if let Some(at) = at {
            let handle = self
                .sources
                .get_mut(at)
                .and_then(Option::take)
                .ok_or_else(|| {
                    NativeSessionError::Application(
                        "source handle is absent or already consumed in this session".into(),
                    )
                })?;
            NativeCurrentOccurrence::through(handle, current)
        } else {
            NativeCurrentOccurrence::entering(current)
        };
        let step = match self.body.advance(&mut occurrence) {
            Ok(step) => step,
            Err(error) => {
                if let Some(at) = at {
                    self.sources[at] = occurrence.take_source();
                }
                return Err(error.into());
            }
        };
        Ok(self.commit_return(step, source, next_source))
    }

    fn commit_return(
        &mut self,
        step: holonic_engine::native_ecology::constitutive_fibre::NativeCurrentStep,
        source: Option<u64>,
        next_source: u64,
    ) -> NativeSessionStep {
        let root = step.root_source_currents();
        let wire = NativeSessionStep {
            source: next_source,
            native_occurrence: step.lineage.occurrence,
            predecessor_state: step.lineage.predecessor_state,
            received_from: source,
            native_received_from: step.lineage.received_from,
            frame: NativeFrameWire {
                ordinal: step.frame.ordinal(),
                root_to_local: step
                    .frame
                    .root_to_local()
                    .iter()
                    .map(|p| CurrentWire::from_current(&p.current()))
                    .collect(),
            },
            local_source_currents: step
                .source_currents
                .iter()
                .map(CurrentWire::from_current)
                .collect(),
            root_source_currents: root.iter().map(CurrentWire::from_current).collect(),
            receiver: ReceiverWire::from(&step.receiver),
            received_difference: step
                .received_difference
                .as_ref()
                .map(|d| NativeReceivedWire {
                    source,
                    native_source_occurrence: d.source_occurrence,
                    former_receiver_fibre: ReceiverWire::from(&d.former_receiver_fibre),
                    arrived: CurrentWire::from_current(&d.arrived),
                }),
            formed_pivot: step.formed_pivot,
            successor_rank: step.successor_rank,
        };
        self.confirmed_rank = step.successor_rank;
        self.sources.push(Some(step.source));
        wire
    }

    pub fn rechart(
        &mut self,
        gauges: &[CurrentWire],
    ) -> Result<NativeFrameWire, NativeSessionError> {
        let gauges = gauges
            .iter()
            .map(CurrentWire::native)
            .collect::<Result<Vec<_>, _>>()?;
        let receipt = self.body.rechart(&gauges)?;
        Ok(NativeFrameWire {
            ordinal: receipt.after.ordinal(),
            root_to_local: receipt
                .after
                .root_to_local()
                .iter()
                .map(|p| CurrentWire::from_current(&p.current()))
                .collect(),
        })
    }

    pub fn replace_incidence(
        &mut self,
        node: usize,
        transport: &CurrentWire,
    ) -> Result<(), NativeSessionError> {
        self.body
            .replace_incoming_transport(node, transport.native()?)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests;
