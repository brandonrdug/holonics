//! Public digital PCM probe over the continuing native phase session.
//!
//! This probe chooses one native occurrence per admitted sample. That is an application control,
//! not the native grain of acoustic holons; see docs/plans/HOLONICS_ON_APPLE_SILICON.md.
//! PCM remains exterior source material, never a label, classifier, or replayed output.

use super::*;
use crate::{HnaStreamState, publication::PublicationReceipt};
use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
use life::mathematical_source::ExactAcousticOccurrence;
use life::native_intelligence::{
    NativeAcousticProductionMorphology, NativeAcousticProductionSection,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

const ACOUSTIC_APPLICATION_SCHEMA: &str = "org.holonics.hna.acoustic-application.v1";
const ACOUSTIC_CORPUS_SCHEMA: &str = "org.holonics.hna.acoustic-application.v2";

#[cfg(test)]
mod tests;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcousticApplication {
    schema: String,
    spec: NativeModelSpec,
    occurrence: ExactAcousticOccurrence,
    /// Original WAV bytes remain cold source lineage beside the decoded PCM occurrence.
    original_wav: Vec<u8>,
    /// Digital amplitude chart: sample `s` enters as `(s / pcm_divisor, 0)`.
    pcm_divisor: i64,
    /// Optional one-sample digital return law, one exact gain per native node.
    return_couplings: Option<Vec<CurrentWire>>,
    cursor: usize,
    steps: Vec<NativeSessionStep>,
    pending: Option<AcousticPendingReceive>,
    /// Earlier complete recordings in this same native owner. These are cold source/return
    /// records, not independently mountable ecologies. Entries never contain nested archives.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    completed_recordings: Vec<AcousticApplication>,
    #[serde(default, skip_serializing_if = "is_zero")]
    native_start: usize,
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcousticPendingReceive {
    pub sample: usize,
    pub current: CurrentWire,
    pub source: Option<u64>,
    pub detail: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct AcousticInterruption {
    pub sample: usize,
    pub detail: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct AcousticRun {
    pub schema: &'static str,
    pub steps: Vec<NativeSessionStep>,
    pub cursor: usize,
    pub complete: bool,
    pub interruption: Option<AcousticInterruption>,
    pub pending: Option<AcousticPendingReceive>,
    pub checkpoint: Option<PathBuf>,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct AcousticRunOptions {
    pub samples: Option<usize>,
    pub checkpoint: Option<PathBuf>,
}

impl AcousticApplication {
    pub fn found(
        spec: &NativeModelSpec,
        occurrence: &ExactAcousticOccurrence,
        original_wav: &[u8],
        pcm_divisor: i64,
        return_couplings: Option<Vec<CurrentWire>>,
        session: &mut NativeSession<'_>,
    ) -> Result<Self, NativeSessionError> {
        if occurrence.samples.is_empty()
            || !session.matches_untouched_seed(spec)?
            || !source_matches(occurrence, original_wav)?
        {
            return Err(invalid(
                "acoustic source, divisor, or untouched native seed",
            ));
        }
        let nodes = spec.nodes.len();
        if return_couplings
            .as_ref()
            .is_some_and(|couplings| couplings.len() != nodes)
        {
            return Err(invalid("digital return gain population differs"));
        }
        let app = Self {
            schema: ACOUSTIC_APPLICATION_SCHEMA.to_owned(),
            spec: spec.clone(),
            occurrence: occurrence.clone(),
            original_wav: original_wav.to_vec(),
            pcm_divisor,
            return_couplings,
            cursor: 0,
            steps: Vec::new(),
            pending: None,
            completed_recordings: Vec::new(),
            native_start: 0,
        };
        app.validate_chart()?;
        Ok(app)
    }

    pub fn cursor(&self) -> usize {
        self.cursor
    }
    pub fn native_start(&self) -> usize {
        self.native_start
    }
    pub fn recording_count(&self) -> usize {
        self.completed_recordings.len() + 1
    }
    pub fn completed_recordings(&self) -> &[AcousticApplication] {
        &self.completed_recordings
    }

    /// Attach a distinct recording without resetting or cloning the native successor. The
    /// first sample is exterior ingress: recording adjacency cannot manufacture a return edge.
    /// An explicitly supplied digital return circuit begins within this recording only.
    pub fn append_recording(
        &mut self,
        session: &mut NativeSession<'_>,
        occurrence: &ExactAcousticOccurrence,
        original_wav: &[u8],
        pcm_divisor: i64,
        return_couplings: Option<Vec<CurrentWire>>,
    ) -> Result<(), NativeSessionError> {
        self.validate_session(session)?;
        if !self.complete() || self.pending.is_some() {
            return Err(invalid(
                "finish the current recording before appending another",
            ));
        }
        if occurrence.samples.is_empty() || !source_matches(occurrence, original_wav)? {
            return Err(invalid("new recording source does not decode identically"));
        }
        let next = Self {
            schema: ACOUSTIC_CORPUS_SCHEMA.to_owned(),
            spec: self.spec.clone(),
            occurrence: occurrence.clone(),
            original_wav: original_wav.to_vec(),
            pcm_divisor,
            return_couplings,
            cursor: 0,
            steps: Vec::new(),
            pending: None,
            completed_recordings: Vec::new(),
            native_start: session.occurrence_count(),
        };
        next.validate_chart()?;
        self.completed_recordings
            .try_reserve(1)
            .map_err(|error| invalid(format!("recording allocation: {error}")))?;
        // Every fallible check precedes this move. The old source bytes and returns remain
        // attached, while the single session retains precisely its existing resident successor.
        let mut previous = std::mem::replace(self, next);
        self.completed_recordings = std::mem::take(&mut previous.completed_recordings);
        self.completed_recordings.push(previous);
        Ok(())
    }
    pub fn complete(&self) -> bool {
        self.cursor == self.occurrence.samples.len()
    }
    pub fn steps(&self) -> &[NativeSessionStep] {
        &self.steps
    }
    pub fn occurrence(&self) -> &ExactAcousticOccurrence {
        &self.occurrence
    }
    pub fn spec(&self) -> &NativeModelSpec {
        &self.spec
    }
    pub fn pcm_divisor(&self) -> i64 {
        self.pcm_divisor
    }
    pub fn return_couplings(&self) -> Option<&[CurrentWire]> {
        self.return_couplings.as_deref()
    }
    pub fn pending(&self) -> Option<&AcousticPendingReceive> {
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
            .steps
            .iter()
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

    fn validate(&self) -> Result<(), NativeSessionError> {
        if ![ACOUSTIC_APPLICATION_SCHEMA, ACOUSTIC_CORPUS_SCHEMA].contains(&self.schema.as_str())
            || self.pcm_divisor <= 0
            || self.cursor > self.occurrence.samples.len()
            || self.steps.len() != self.cursor
            || self.pending.as_ref().is_some_and(|pending| {
                pending.sample != self.cursor
                    || pending.current.current().is_err()
                    || pending.source
                        != self
                            .steps
                            .last()
                            .and_then(|step| self.return_couplings.as_ref().map(|_| step.source))
            })
            || self
                .return_couplings
                .as_ref()
                .is_some_and(|couplings| couplings.len() != self.spec.nodes.len())
        {
            return Err(invalid("acoustic application position or source"));
        }
        self.spec.material()?;
        if let Some(pending) = &self.pending {
            let expected_source = self
                .return_couplings
                .as_ref()
                .and_then(|_| self.steps.last().map(|step| step.source));
            if pending.sample != self.cursor
                || pending.source != expected_source
                || pending.current != self.current_for(self.cursor)?
            {
                return Err(invalid(
                    "acoustic pending current is not the declared digital return",
                ));
            }
        }
        Ok(())
    }

    fn validate_recordings(&self) -> Result<(), NativeSessionError> {
        let mut start = 0usize;
        for prior in &self.completed_recordings {
            prior.validate()?;
            prior.validate_chart()?;
            if !prior.completed_recordings.is_empty()
                || !prior.complete()
                || prior.pending.is_some()
                || prior.native_start != start
                || prior.spec != self.spec
            {
                return Err(invalid("completed recording chronology"));
            }
            start = start
                .checked_add(prior.cursor)
                .ok_or_else(|| invalid("recording extent overflow"))?;
        }
        if start != self.native_start {
            return Err(invalid("recording/native start differs"));
        }
        Ok(())
    }

    fn validate_chart(&self) -> Result<(), NativeSessionError> {
        if self.pcm_divisor <= 0 {
            return Err(invalid("PCM divisor must be positive"));
        }
        if let Some(couplings) = &self.return_couplings {
            if couplings.len() != self.spec.nodes.len() {
                return Err(invalid("digital return gain population differs"));
            }
            for coupling in couplings {
                coupling.current()?;
            }
        }
        Ok(())
    }

    pub(crate) fn validate_checkpoint(&self) -> Result<(), NativeSessionError> {
        self.validate()?;
        self.validate_chart()?;
        self.validate_recordings()?;
        for recording in self
            .completed_recordings
            .iter()
            .chain(std::iter::once(self))
        {
            if !source_matches(&recording.occurrence, &recording.original_wav)? {
                return Err(invalid("acoustic source does not decode identically"));
            }
        }
        Ok(())
    }

    fn validate_session(&self, session: &NativeSession<'_>) -> Result<(), NativeSessionError> {
        self.validate()?;
        self.validate_chart()?;
        if self.native_start.checked_add(self.cursor) != Some(session.occurrence_count())
            || session.nodes() != self.spec.nodes.len()
            || self
                .steps
                .last()
                .is_some_and(|step| !session.has_source(step.source))
        {
            return Err(invalid("acoustic native cursor/source boundary"));
        }
        Ok(())
    }

    fn receive_next(
        &mut self,
        session: &mut NativeSession<'_>,
        source: Option<u64>,
    ) -> Result<(), NativeSessionError> {
        self.commit_receive(session, self.current_for(self.cursor)?, source)
    }

    fn current_for(&self, sample: usize) -> Result<CurrentWire, NativeSessionError> {
        let sample = *self
            .occurrence
            .samples
            .get(sample)
            .ok_or_else(|| invalid("acoustic cursor is complete"))?;
        let base = ExactComplexWaveCurrent::new(
            Rat::new(BigInt::from(sample), BigInt::from(self.pcm_divisor)),
            Rat::from_integer(BigInt::from(0)),
        );
        let Some(couplings) = &self.return_couplings else {
            return Ok(CurrentWire::from_current(&base));
        };
        let Some(prior) = self.steps.last() else {
            return Ok(CurrentWire::from_current(&base));
        };
        if couplings.len() != prior.root_source_currents.len() {
            return Err(invalid("digital return gain population differs"));
        }
        let mut returned = ExactComplexWaveCurrent::zero();
        for (gain, root) in couplings.iter().zip(&prior.root_source_currents) {
            returned = returned.add(&gain.current()?.multiply(&root.current()?));
        }
        Ok(CurrentWire::from_current(&base.add(&returned)))
    }

    fn commit_receive(
        &mut self,
        session: &mut NativeSession<'_>,
        current: CurrentWire,
        source: Option<u64>,
    ) -> Result<(), NativeSessionError> {
        self.steps
            .try_reserve(1)
            .map_err(|error| invalid(format!("native step allocation: {error}")))?;
        self.pending = Some(AcousticPendingReceive {
            sample: self.cursor,
            current: current.clone(),
            source,
            detail: None,
        });
        match session.receive(&current, source) {
            Ok(next) => {
                self.steps.push(next);
                self.cursor += 1;
                self.pending = None;
                Ok(())
            }
            Err(error) => {
                if let Some(pending) = self.pending.as_mut() {
                    pending.detail = Some(error.to_string());
                }
                Err(error)
            }
        }
    }

    pub fn advance_one(
        &mut self,
        session: &mut NativeSession<'_>,
    ) -> Result<bool, NativeSessionError> {
        self.validate_session(session)?;
        if self.complete() {
            return Ok(false);
        }
        if let Some(pending) = self.pending.clone() {
            self.commit_receive(session, pending.current, pending.source)?;
            return Ok(true);
        }
        let source = self
            .return_couplings
            .as_ref()
            .and_then(|_| self.steps.last().map(|step| step.source));
        self.receive_next(session, source)?;
        Ok(true)
    }

    /// Deliver a bounded packet of independent exterior samples. Native operations remain
    /// ordered; neither packet boundaries nor neighboring recordings create return contact.
    /// A declared digital feedback circuit still uses `advance_one`, since its next input
    /// depends on the preceding output and is not known at packet ingress.
    pub fn advance_packet(
        &mut self,
        session: &mut NativeSession<'_>,
        samples: usize,
    ) -> Result<usize, NativeSessionError> {
        self.validate_session(session)?;
        if samples == 0 || self.complete() {
            return Ok(0);
        }
        if self.return_couplings.is_some() {
            return self.advance_one(session).map(usize::from);
        }
        let count = samples.min(self.occurrence.samples.len() - self.cursor);
        let currents = (self.cursor..self.cursor + count)
            .map(|i| self.current_for(i))
            .collect::<Result<Vec<_>, _>>()?;
        self.steps
            .try_reserve(count)
            .map_err(|e| invalid(format!("native step allocation: {e}")))?;
        self.pending = Some(AcousticPendingReceive {
            sample: self.cursor,
            current: currents[0].clone(),
            source: None,
            detail: None,
        });
        let returned = match session.receive_unlinked_batch(&currents) {
            Ok(returned) => returned,
            Err(error) => {
                self.pending.as_mut().expect("staged packet").detail = Some(error.to_string());
                return Err(error);
            }
        };
        let committed = returned.committed.len();
        self.steps.extend(returned.committed);
        self.cursor += committed;
        self.pending = None;
        if let Some(at) = returned.refused_at {
            let error = invalid(format!(
                "resident packet refusal: {:?}",
                returned.obstruction
            ));
            self.pending = Some(AcousticPendingReceive {
                sample: self.cursor,
                current: currents[at].clone(),
                source: None,
                detail: Some(error.to_string()),
            });
            return Err(error);
        }
        Ok(committed)
    }

    pub fn checkpoint(
        &self,
        session: &NativeSession<'_>,
        path: impl AsRef<Path>,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        self.validate_session(session)?;
        session.checkpoint_application(path, &HnaStreamState::default(), &serde_json::to_vec(self)?)
    }
}

pub fn run_acoustic_with_options(
    spec: &NativeModelSpec,
    occurrence: &ExactAcousticOccurrence,
    original_wav: &[u8],
    pcm_divisor: i64,
    return_couplings: Option<Vec<CurrentWire>>,
    options: &AcousticRunOptions,
) -> Result<AcousticRun, NativeSessionError> {
    preflight(options)?;
    with_native_session(spec, |session| {
        let mut app = AcousticApplication::found(
            spec,
            occurrence,
            original_wav,
            pcm_divisor,
            return_couplings,
            session,
        )?;
        execute(&mut app, session, options)
    })
}

pub fn resume_acoustic(
    path: impl AsRef<Path>,
    options: &AcousticRunOptions,
) -> Result<AcousticRun, NativeSessionError> {
    preflight(options)?;
    AcousticSavedApplication::read(path)?
        .with_application(|session, app| execute(app, session, options))
}

/// Continue a saved acoustic ecology with a new source recording, retaining every earlier
/// recording and native successor. This is corpus ingress, not an audio/language learner.
pub fn append_acoustic(
    path: impl AsRef<Path>,
    occurrence: &ExactAcousticOccurrence,
    original_wav: &[u8],
    pcm_divisor: i64,
    return_couplings: Option<Vec<CurrentWire>>,
    options: &AcousticRunOptions,
) -> Result<AcousticRun, NativeSessionError> {
    preflight(options)?;
    AcousticSavedApplication::read(path)?.with_application(|session, app| {
        app.append_recording(
            session,
            occurrence,
            original_wav,
            pcm_divisor,
            return_couplings,
        )?;
        execute(app, session, options)
    })
}

pub struct AcousticSavedApplication {
    native: NativeSavedSession,
    application: AcousticApplication,
}

impl AcousticSavedApplication {
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let native = NativeSavedSession::read(path)?;
        let bytes = native
            .application_state()
            .ok_or_else(|| invalid("checkpoint has no acoustic application state"))?;
        let application: AcousticApplication = serde_json::from_slice(bytes)?;
        application.validate_checkpoint()?;
        if native.nodes() != application.spec.nodes.len()
            || application.native_start.checked_add(application.cursor)
                != Some(native.occurrences())
            || *native.transport() != HnaStreamState::default()
        {
            return Err(invalid("checkpoint/native acoustic boundary differs"));
        }
        validate_saved_native(&native, &application)?;
        Ok(Self {
            native,
            application,
        })
    }

    pub fn application(&self) -> &AcousticApplication {
        &self.application
    }

    pub fn with_application<R>(
        self,
        operation: impl FnOnce(
            &mut NativeSession<'_>,
            &mut AcousticApplication,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let mut application = self.application;
        self.native
            .with_application_session(|session, _, _| operation(session, &mut application))
    }
}

fn execute(
    app: &mut AcousticApplication,
    session: &mut NativeSession<'_>,
    options: &AcousticRunOptions,
) -> Result<AcousticRun, NativeSessionError> {
    app.validate_session(session)?;
    let limit = options.samples.unwrap_or(usize::MAX);
    let mut interruption = None;
    let mut remaining = limit;
    while remaining > 0 && !app.complete() {
        match app.advance_packet(session, remaining.min(256)) {
            Ok(committed) => remaining -= committed,
            Err(error) => {
                interruption = Some(AcousticInterruption {
                    sample: app.cursor,
                    detail: error.to_string(),
                });
                break;
            }
        }
    }
    let (checkpoint_octets, checkpoint_error) = if let Some(path) = &options.checkpoint {
        match app.checkpoint(session, path) {
            Ok(receipt) => (Some(receipt.bytes), None),
            Err(error) => (None, Some(error.to_string())),
        }
    } else {
        (None, None)
    };
    Ok(AcousticRun {
        schema: if app.completed_recordings.is_empty() {
            ACOUSTIC_APPLICATION_SCHEMA
        } else {
            ACOUSTIC_CORPUS_SCHEMA
        },
        steps: app.steps.clone(),
        cursor: app.cursor,
        complete: app.complete(),
        interruption,
        pending: app.pending.clone(),
        checkpoint: options.checkpoint.clone(),
        checkpoint_octets,
        checkpoint_error,
    })
}

fn preflight(options: &AcousticRunOptions) -> Result<(), NativeSessionError> {
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
    NativeSessionError::Application(format!("acoustic application: {detail}"))
}

fn validate_saved_native(
    native: &NativeSavedSession,
    application: &AcousticApplication,
) -> Result<(), NativeSessionError> {
    for recording in application
        .completed_recordings
        .iter()
        .chain(std::iter::once(application))
    {
        if recording.steps.iter().enumerate().any(|(index, step)| {
            let ordinal = recording.native_start + index;
            step.native_occurrence != ordinal
                || step.source != ordinal as u64
                || step.predecessor_state != ordinal.checked_sub(1)
                || step.received_from
                    != if recording.return_couplings.is_some() && index > 0 {
                        Some((ordinal - 1) as u64)
                    } else {
                        None
                    }
                || native.source_slots().get(step.source as usize)
                    != Some(&if recording.return_couplings.is_some()
                        && index + 1 < recording.steps.len()
                    {
                        None
                    } else {
                        Some(ordinal)
                    })
        }) {
            return Err(invalid("checkpoint acoustic step/source lineage differs"));
        }
    }
    Ok(())
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn source_matches(
    occurrence: &ExactAcousticOccurrence,
    original_wav: &[u8],
) -> Result<bool, NativeSessionError> {
    if occurrence.source_octets != original_wav.len() as u64
        || hex(Sha256::digest(original_wav)) != occurrence.source_sha256
    {
        return Ok(false);
    }
    let decoded = ExactAcousticOccurrence::from_wav_bytes(
        original_wav,
        occurrence.occurrence.clone(),
        occurrence.locator.clone(),
        occurrence.frame_length,
        occurrence.frame_hop,
        occurrence.section.len(),
    )
    .map_err(|error| invalid(error))?;
    Ok(decoded == *occurrence)
}
