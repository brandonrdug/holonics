//! Addressed recording sections attached to a retained source/response annotation.
use super::{PcmFrameBounds, RecordedIntervalError, RecordedResponseLink};
use crate::native::acoustic_field::{AcousticFieldChart, AcousticFieldError};
use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
use life::mathematical_source::ExactAcousticOccurrence;
use num_rational::BigRational;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RecordedSectionError {
    #[error("recorded annotation has no resolved source/target pair")]
    Unresolved,
    #[error("recording occurrence does not match the annotation's declared session binding")]
    RecordingBinding,
    #[error(transparent)]
    Clock(#[from] RecordedIntervalError),
    #[error(transparent)]
    Acoustic(#[from] AcousticFieldError),
}

/// Complete source and target PCM intervals plus their original annotation relation. This is
/// an exterior attachment; it neither infers a native condition nor selects a fibre member.
pub struct RecordedResponseSections<'annotation> {
    link: &'annotation RecordedResponseLink,
    source: AcousticFieldChart,
    target: AcousticFieldChart,
    source_frames: PcmFrameBounds,
    target_frames: PcmFrameBounds,
}

impl<'annotation> RecordedResponseSections<'annotation> {
    /// The caller binds the decoded occurrence to a source-qualified corpus session. The
    /// equality below checks that exterior binding; it does not establish semantic identity.
    /// Both endpoint charts use the same mono receiver. Speaker IDs never become microphones.
    #[allow(clippy::too_many_arguments)]
    pub fn bind(
        link: &'annotation RecordedResponseLink,
        recording: &ExactAcousticOccurrence,
        receiver: PhaseCurrentReceiverId,
        source_lineage: PhaseCurrentLineageId,
        target_lineage: PhaseCurrentLineageId,
        recording_origin: BigRational,
        port_extent: usize,
        divisor: i64,
    ) -> Result<Self, RecordedSectionError> {
        let (source, target) = link.resolved().ok_or(RecordedSectionError::Unresolved)?;
        if link.session.as_deref() != Some(recording.occurrence.as_str()) {
            return Err(RecordedSectionError::RecordingBinding);
        }
        let bounds = |interval: &super::RecordedInterval| {
            interval.covering_frames(
                u64::from(recording.sample_rate),
                recording.samples.len() as u64,
            )
        };
        let source_frames = bounds(&source.interval)?;
        let target_frames = bounds(&target.interval)?;
        // Bounds have been checked against this usize-sized sample population.
        let chart = |frames: &PcmFrameBounds, lineage| {
            AcousticFieldChart::from_acoustic_range(
                recording,
                receiver,
                lineage,
                recording_origin.clone(),
                frames.begin_frame as usize..frames.end_frame as usize,
                port_extent,
                divisor,
            )
        };
        let source = chart(&source_frames, source_lineage)?;
        let target = chart(&target_frames, target_lineage)?;
        Ok(Self {
            link,
            source,
            target,
            source_frames,
            target_frames,
        })
    }

    pub fn link(&self) -> &'annotation RecordedResponseLink {
        self.link
    }
    pub fn source(&self) -> &AcousticFieldChart {
        &self.source
    }
    pub fn target(&self) -> &AcousticFieldChart {
        &self.target
    }
    pub fn source_frames(&self) -> &PcmFrameBounds {
        &self.source_frames
    }
    pub fn target_frames(&self) -> &PcmFrameBounds {
        &self.target_frames
    }
}
