//! Curated speech exposure: one WAV occurrence followed by its transcript occurrence.
//!
//! The transcript is retained as a separate exterior byte source. It is delivered through the
//! same native session only after the acoustic occurrence completes, and the first transcript
//! byte consumes the actual last acoustic source handle. Bytes are ordinary later occurrences;
//! they are not labels, expected answers, or a speech competence claim.

use super::*;
use crate::{HnaStreamState, publication::PublicationReceipt};
use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
use life::mathematical_source::ExactAcousticOccurrence;
use life::native_intelligence::{
    NativeAcousticProductionMorphology, NativeAcousticProductionSection,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

const SPEECH_APPLICATION_SCHEMA: &str = "org.holonics.hna.curated-speech-exposure.v1";

#[cfg(test)]
mod tests;

/// Exact source/response annotations over recorded acoustic intervals. This exterior chart
/// supplies lineage and clocks; native conditional conduct retains its own owner.
pub mod recorded;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpeechPendingReceive {
    pub transcript_byte: usize,
    pub current: CurrentWire,
    pub source: Option<u64>,
    pub detail: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpeechExposureApplication {
    schema: String,
    acoustic: AcousticApplication,
    transcript: Vec<u8>,
    transcript_sha256: String,
    transcript_divisor: i64,
    transcript_cursor: usize,
    transcript_steps: Vec<NativeSessionStep>,
    pending: Option<SpeechPendingReceive>,
}

#[derive(Clone, Debug, Default)]
pub struct SpeechRunOptions {
    pub occurrences: Option<usize>,
    pub checkpoint: Option<PathBuf>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SpeechRun {
    pub schema: &'static str,
    pub acoustic_cursor: usize,
    pub transcript_cursor: usize,
    pub complete: bool,
    pub acoustic_steps: Vec<NativeSessionStep>,
    pub transcript_steps: Vec<NativeSessionStep>,
    pub pending: Option<SpeechPendingReceive>,
    pub acoustic_pending: Option<AcousticPendingReceive>,
    pub interruption: Option<String>,
    pub checkpoint: Option<PathBuf>,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
}

pub struct SpeechSavedApplication {
    native: NativeSavedSession,
    application: SpeechExposureApplication,
}

impl SpeechExposureApplication {
    pub fn found(
        spec: &NativeModelSpec,
        occurrence: &ExactAcousticOccurrence,
        original_wav: &[u8],
        pcm_divisor: i64,
        return_couplings: Option<Vec<CurrentWire>>,
        transcript: &[u8],
        transcript_divisor: i64,
        session: &mut NativeSession<'_>,
    ) -> Result<Self, NativeSessionError> {
        if transcript.is_empty() || transcript_divisor <= 0 {
            return Err(invalid("speech transcript or positive digital divisor"));
        }
        let acoustic = AcousticApplication::found(
            spec,
            occurrence,
            original_wav,
            pcm_divisor,
            return_couplings,
            session,
        )?;
        Ok(Self {
            schema: SPEECH_APPLICATION_SCHEMA.to_owned(),
            acoustic,
            transcript: transcript.to_vec(),
            transcript_sha256: hex(Sha256::digest(transcript)),
            transcript_divisor,
            transcript_cursor: 0,
            transcript_steps: Vec::new(),
            pending: None,
        })
    }

    pub fn acoustic(&self) -> &AcousticApplication {
        &self.acoustic
    }
    pub fn transcript(&self) -> &[u8] {
        &self.transcript
    }
    pub fn transcript_cursor(&self) -> usize {
        self.transcript_cursor
    }
    pub fn transcript_steps(&self) -> &[NativeSessionStep] {
        &self.transcript_steps
    }
    pub fn complete(&self) -> bool {
        self.acoustic.complete() && self.transcript_cursor == self.transcript.len()
    }
    pub fn pending(&self) -> Option<&SpeechPendingReceive> {
        self.pending.as_ref()
    }

    pub fn production(
        &self,
        rested_identity_sha256: impl Into<String>,
        session_lineage_sha256: impl Into<String>,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
    ) -> Result<
        (
            NativeAcousticProductionMorphology,
            NativeAcousticProductionSection,
        ),
        NativeSessionError,
    > {
        let emissions = self
            .acoustic
            .steps()
            .iter()
            .chain(&self.transcript_steps)
            .map(|step| {
                Ok((
                    step.native_occurrence as u64,
                    step.root_source_currents
                        .iter()
                        .map(CurrentWire::current)
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            })
            .collect::<Result<Vec<_>, NativeSessionError>>()?;
        NativeAcousticProductionMorphology::found_phase_session(
            rested_identity_sha256,
            session_lineage_sha256,
            receiver,
            lineage,
            origin,
            sample_step,
            &emissions,
        )
        .map_err(|error| invalid(error))
    }

    pub fn advance_one(
        &mut self,
        session: &mut NativeSession<'_>,
    ) -> Result<bool, NativeSessionError> {
        self.validate_session(session)?;
        if self.complete() {
            return Ok(false);
        }
        if !self.acoustic.complete() {
            self.acoustic.advance_one(session)?;
            return Ok(true);
        }
        let (current, source) = if let Some(pending) = self.pending.clone() {
            (pending.current, pending.source)
        } else {
            self.transcript_current_for(self.transcript_cursor)?
        };
        self.transcript_steps
            .try_reserve(1)
            .map_err(|error| invalid(format!("speech step allocation: {error}")))?;
        self.pending = Some(SpeechPendingReceive {
            transcript_byte: self.transcript_cursor,
            current: current.clone(),
            source,
            detail: None,
        });
        match session.receive(&current, source) {
            Ok(step) => {
                self.transcript_steps.push(step);
                self.transcript_cursor += 1;
                self.pending = None;
                Ok(true)
            }
            Err(error) => {
                if let Some(pending) = self.pending.as_mut() {
                    pending.detail = Some(error.to_string());
                }
                Err(error)
            }
        }
    }

    fn transcript_current_for(
        &self,
        at: usize,
    ) -> Result<(CurrentWire, Option<u64>), NativeSessionError> {
        let byte = *self
            .transcript
            .get(at)
            .ok_or_else(|| invalid("transcript cursor is complete"))?;
        let base = ExactComplexWaveCurrent::new(
            Rat::new(BigInt::from(byte), BigInt::from(self.transcript_divisor)),
            Rat::from_integer(BigInt::from(0)),
        );
        let Some(couplings) = self.acoustic.return_couplings() else {
            return Ok((CurrentWire::from_current(&base), None));
        };
        let prior = self
            .transcript_steps
            .last()
            .or_else(|| self.acoustic.steps().last())
            .ok_or_else(|| invalid("digital transcript return has no prior emission"))?;
        if couplings.len() != prior.root_source_currents.len() {
            return Err(invalid("digital transcript return population differs"));
        }
        let mut returned = ExactComplexWaveCurrent::zero();
        for (gain, root) in couplings.iter().zip(&prior.root_source_currents) {
            returned = returned.add(&gain.current()?.multiply(&root.current()?));
        }
        Ok((
            CurrentWire::from_current(&base.add(&returned)),
            Some(prior.source),
        ))
    }

    pub fn checkpoint(
        &self,
        session: &NativeSession<'_>,
        path: impl AsRef<Path>,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        self.validate_session(session)?;
        session.checkpoint_application(path, &HnaStreamState::default(), &serde_json::to_vec(self)?)
    }

    fn validate(&self) -> Result<(), NativeSessionError> {
        if self.schema != SPEECH_APPLICATION_SCHEMA
            || self.transcript.is_empty()
            || self.transcript_cursor > self.transcript.len()
            || self.transcript_steps.len() != self.transcript_cursor
            || self.transcript_divisor <= 0
            || self.pending.as_ref().is_some_and(|pending| {
                pending.transcript_byte != self.transcript_cursor
                    || pending.current.current().is_err()
            })
        {
            return Err(invalid("speech application position or transcript lineage"));
        }
        if (self.transcript_cursor > 0 || self.pending.is_some()) && !self.acoustic.complete() {
            return Err(invalid(
                "transcript began before acoustic occurrence completed",
            ));
        }
        if let Some(pending) = &self.pending {
            let (current, source) = self.transcript_current_for(self.transcript_cursor)?;
            if pending.current != current || pending.source != source {
                return Err(invalid(
                    "pending transcript current is not the declared return",
                ));
            }
        }
        Ok(())
    }

    fn validate_checkpoint(&self, native: &NativeSavedSession) -> Result<(), NativeSessionError> {
        self.validate()?;
        self.acoustic.validate_checkpoint()?;
        if self.transcript_sha256 != hex(Sha256::digest(&self.transcript))
            || native.nodes() != self.acoustic.spec().nodes.len()
            || native.occurrences() != self.acoustic.cursor() + self.transcript_cursor
            || *native.transport() != HnaStreamState::default()
        {
            return Err(invalid("speech checkpoint source or extent"));
        }
        let nodes = self.acoustic.spec().nodes.len();
        for (index, step) in self
            .acoustic
            .steps()
            .iter()
            .chain(&self.transcript_steps)
            .enumerate()
        {
            if step.native_occurrence != index
                || step.predecessor_state != index.checked_sub(1)
                || step.root_source_currents.len() != nodes
                || step.local_source_currents.len() != nodes
                || step.frame.root_to_local.len() != nodes
            {
                return Err(invalid("speech checkpoint step/frame population"));
            }
        }
        let total = self.acoustic.cursor() + self.transcript_cursor;
        let mut consumed = vec![false; total];
        if self.acoustic.return_couplings().is_some() {
            for index in 1..self.acoustic.cursor() {
                consumed[index - 1] = true;
            }
            for index in 0..self.transcript_cursor {
                consumed[self.acoustic.cursor() + index - 1] = true;
            }
        }
        for (index, step) in self
            .acoustic
            .steps()
            .iter()
            .chain(&self.transcript_steps)
            .enumerate()
        {
            let expected = if consumed[index] { None } else { Some(index) };
            if native.source_slots().get(step.source as usize) != Some(&expected) {
                return Err(invalid("speech checkpoint source-slot lineage"));
            }
        }
        Ok(())
    }

    fn validate_session(&self, session: &NativeSession<'_>) -> Result<(), NativeSessionError> {
        self.validate()?;
        let expected = self.acoustic.cursor() + self.transcript_cursor;
        if session.occurrence_count() != expected
            || session.nodes() != self.acoustic.spec().nodes.len()
        {
            return Err(invalid("speech native cursor or node boundary"));
        }
        let last = self
            .transcript_steps
            .last()
            .or_else(|| self.acoustic.steps().last());
        if last.is_some_and(|step| !session.has_source(step.source)) {
            return Err(invalid("speech source handle boundary"));
        }
        Ok(())
    }
}

pub fn run_speech_with_options(
    spec: &NativeModelSpec,
    occurrence: &ExactAcousticOccurrence,
    original_wav: &[u8],
    pcm_divisor: i64,
    return_couplings: Option<Vec<CurrentWire>>,
    transcript: &[u8],
    transcript_divisor: i64,
    options: &SpeechRunOptions,
) -> Result<SpeechRun, NativeSessionError> {
    preflight(options)?;
    with_native_session(spec, |session| {
        let mut app = SpeechExposureApplication::found(
            spec,
            occurrence,
            original_wav,
            pcm_divisor,
            return_couplings,
            transcript,
            transcript_divisor,
            session,
        )?;
        execute(&mut app, session, options)
    })
}

pub fn resume_speech(
    path: impl AsRef<Path>,
    options: &SpeechRunOptions,
) -> Result<SpeechRun, NativeSessionError> {
    preflight(options)?;
    SpeechSavedApplication::read(path)?
        .with_application(|session, application| execute(application, session, options))
}

impl SpeechSavedApplication {
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let native = NativeSavedSession::read(path)?;
        let bytes = native
            .application_state()
            .ok_or_else(|| invalid("checkpoint has no speech application state"))?;
        let application: SpeechExposureApplication = serde_json::from_slice(bytes)?;
        application.validate_checkpoint(&native)?;
        if application
            .transcript_steps
            .iter()
            .enumerate()
            .any(|(index, step)| {
                step.native_occurrence != application.acoustic.cursor() + index
                    || step.predecessor_state != Some(application.acoustic.cursor() + index - 1)
            })
        {
            return Err(invalid("checkpoint/native speech boundary differs"));
        }
        Ok(Self {
            native,
            application,
        })
    }

    pub fn application(&self) -> &SpeechExposureApplication {
        &self.application
    }

    pub fn with_application<R>(
        self,
        operation: impl FnOnce(
            &mut NativeSession<'_>,
            &mut SpeechExposureApplication,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let mut application = self.application;
        self.native
            .with_application_session(|session, _, _| operation(session, &mut application))
    }
}

fn execute(
    app: &mut SpeechExposureApplication,
    session: &mut NativeSession<'_>,
    options: &SpeechRunOptions,
) -> Result<SpeechRun, NativeSessionError> {
    let mut remaining = options.occurrences.unwrap_or(usize::MAX);
    let mut interruption = None;
    while remaining > 0 && !app.complete() {
        if let Err(error) = app.advance_one(session) {
            interruption = Some(error.to_string());
            break;
        }
        remaining -= 1;
    }
    let (checkpoint_octets, checkpoint_error) = if let Some(path) = &options.checkpoint {
        match app.checkpoint(session, path) {
            Ok(receipt) => (Some(receipt.bytes), None),
            Err(error) => (None, Some(error.to_string())),
        }
    } else {
        (None, None)
    };
    Ok(SpeechRun {
        schema: SPEECH_APPLICATION_SCHEMA,
        acoustic_cursor: app.acoustic.cursor(),
        transcript_cursor: app.transcript_cursor,
        complete: app.complete(),
        acoustic_steps: app.acoustic.steps().to_vec(),
        transcript_steps: app.transcript_steps.clone(),
        pending: app.pending.clone(),
        acoustic_pending: app.acoustic.pending().cloned(),
        interruption,
        checkpoint: options.checkpoint.clone(),
        checkpoint_octets,
        checkpoint_error,
    })
}

fn preflight(options: &SpeechRunOptions) -> Result<(), NativeSessionError> {
    if let Some(path) = &options.checkpoint {
        if path.exists() {
            return Err(crate::publication::PublicationError::ExistingTarget {
                path: path.clone(),
            }
            .into());
        }
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            std::fs::create_dir_all(parent)?;
        }
    }
    Ok(())
}

fn invalid(detail: impl std::fmt::Display) -> NativeSessionError {
    NativeSessionError::Application(format!("speech exposure: {detail}"))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
