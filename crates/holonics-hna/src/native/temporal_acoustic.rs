//! Continuing recorded temporal response through the native condition-contact owner.
//!
//! A checkpoint retains the response construction and the exterior recording/contact chronology.
//! It does not archive raw recordings or checkpoint an entire acoustic model. Numerical sections
//! stay resident until a caller explicitly invokes a cold output receiver in the callback.

use super::acoustic_field::{AcousticFieldChart, AcousticFieldError};
use crate::{
    checkpoint::{hash_prefix, read_blob, write_len},
    publication::{PublicationError, PublicationReceipt, publish_new},
};
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ResidentTemporalConditionContact, ResidentTemporalConditionCurrent,
        ResidentTemporalConditionPreimage, ResidentTemporalConditionRest,
        ResidentTemporalConditionSnapshot,
    },
    phase_current::{
        PhaseCurrentLineageId, PhaseCurrentReceiverId,
        resident::{
            PhaseComparisonSupport, ResidentEnclosedPhaseConvolution,
            ResidentEnclosedPhaseDifference, ResidentPhaseCurrentError, compare_enclosed_resident,
            convolve_enclosed_resident,
        },
    },
    resident_section::{ResidentSurface, TransferCensus},
};
use life::mathematical_source::ExactAcousticOccurrence;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
    time::Instant,
};
use thiserror::Error;

const MAGIC: &[u8] = b"HNA-TEMPORAL-ACOUSTIC\x01";
const END: &[u8] = b"HNA-TEMPORAL-ACOUSTIC-END\x01";

#[derive(Debug, Error)]
pub enum TemporalAcousticError {
    #[error(transparent)]
    Native(#[from] ResidentPhaseCurrentError),
    #[error(transparent)]
    Constitutive(
        #[from] holonic_engine::native_ecology::constitutive_fibre::ConstitutiveFibreError,
    ),
    #[error(transparent)]
    Chart(#[from] AcousticFieldError),
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error(transparent)]
    Json(#[from] serde_json::Error),
    #[error(transparent)]
    Publication(#[from] PublicationError),
    #[error(transparent)]
    Checkpoint(#[from] crate::checkpoint::CheckpointError),
    #[error("recorded temporal response: {0}")]
    Invalid(String),
}
type Result<T> = std::result::Result<T, TemporalAcousticError>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TemporalAcousticChart {
    pub sample_rate: u32,
    pub pcm_divisor: i64,
    pub source_receiver: PhaseCurrentReceiverId,
    pub output_receiver: PhaseCurrentReceiverId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TemporalRecording {
    pub occurrence: String,
    pub locator: String,
    pub sha256: String,
    pub octets: u64,
    pub frames: usize,
    pub sample_rate: u32,
    pub origin: Rat,
}
impl TemporalRecording {
    fn from_occurrence(source: &ExactAcousticOccurrence, origin: Rat) -> Self {
        Self {
            occurrence: source.occurrence.clone(),
            locator: source.locator.clone(),
            sha256: source.source_sha256.clone(),
            octets: source.source_octets,
            frames: source.samples.len(),
            sample_rate: source.sample_rate,
            origin,
        }
    }
}

/// Source coordinates are exterior lineage. A cut counts actual completed contacts; it never
/// supplies a semantic grain, a speaker identity or an inferred physical delay.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TemporalAcousticContactReceipt {
    pub source: TemporalRecording,
    pub observed: TemporalRecording,
    pub producing_cut: u64,
    pub successor_cut: u64,
    pub prediction_lineage: PhaseCurrentLineageId,
    pub difference_lineage: PhaseCurrentLineageId,
    pub contact_lineage: PhaseCurrentLineageId,
    pub support: PhaseComparisonSupport,
}

#[derive(Clone, Debug, Serialize)]
pub struct TemporalAcousticWork {
    pub seconds: f64,
    pub deeds: u64,
    pub section_readouts: u64,
    pub numerical_egress_octets: u64,
    pub ingress_octets: u64,
    pub receipt_egress_octets: u64,
    pub resident_octets_peak: u64,
}
impl TemporalAcousticWork {
    fn between(before: TransferCensus, after: TransferCensus, started: Instant) -> Self {
        Self {
            seconds: started.elapsed().as_secs_f64(),
            deeds: after.deed_launches - before.deed_launches,
            section_readouts: after.section_read_outs - before.section_read_outs,
            numerical_egress_octets: after.egress_section_octets - before.egress_section_octets,
            ingress_octets: after.ingress_octets - before.ingress_octets,
            receipt_egress_octets: after.egress_receipt_octets - before.egress_receipt_octets,
            resident_octets_peak: after.resident_octets_peak,
        }
    }
}

/// The callback borrows the completed producing carriers and all native return legs. Its return
/// may itself be a Result: an output failure after contact does not rewind the changed owner.
pub struct TemporalAcousticReturn<'a, 'c> {
    pub prediction: &'a ResidentEnclosedPhaseConvolution<'a, 'a, 'c>,
    pub difference: &'a ResidentEnclosedPhaseDifference<'a, 'a, 'c>,
    pub contact: &'a ResidentTemporalConditionContact<'a, 'c>,
    pub receipt: &'a TemporalAcousticContactReceipt,
    pub prediction_work: TemporalAcousticWork,
    pub difference_work: TemporalAcousticWork,
    pub contact_work: TemporalAcousticWork,
}

pub struct TemporalAcousticSession<'c> {
    surface: &'c ResidentSurface<'c>,
    current: ResidentTemporalConditionCurrent<'c>,
    chart: TemporalAcousticChart,
    history: Vec<TemporalAcousticContactReceipt>,
}
impl<'c> TemporalAcousticSession<'c> {
    /// Transfer an initial native response into the public recording boundary.
    pub fn retain(
        surface: &'c ResidentSurface<'c>,
        current: ResidentTemporalConditionCurrent<'c>,
        chart: TemporalAcousticChart,
    ) -> Result<Self> {
        if current.contacts() != 0 {
            return Err(TemporalAcousticError::Invalid(
                "noninitial response requires its saved chronology".into(),
            ));
        }
        validate_chart(&chart, current.snapshot().chart())?;
        Ok(Self {
            surface,
            current,
            chart,
            history: Vec::new(),
        })
    }
    pub fn contacts(&self) -> u64 {
        self.current.contacts()
    }
    pub fn snapshot(&self) -> ResidentTemporalConditionSnapshot<'c> {
        self.current.snapshot()
    }
    pub fn chart(&self) -> &TemporalAcousticChart {
        &self.chart
    }
    pub fn history(&self) -> &[TemporalAcousticContactReceipt] {
        &self.history
    }

    fn source_chart(
        &self,
        source: &ExactAcousticOccurrence,
        origin: Rat,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
    ) -> Result<AcousticFieldChart> {
        if source.sample_rate != self.chart.sample_rate {
            return Err(TemporalAcousticError::Invalid(
                "recording clock differs from response clock".into(),
            ));
        }
        Ok(AcousticFieldChart::from_acoustic(
            source,
            receiver,
            lineage,
            origin,
            self.current.snapshot().chart().phase_extent as usize,
            self.chart.pcm_divisor,
        )?)
    }

    /// Complete one recording-relative operation before the next contact. Both origins are
    /// caller-supplied coordinates on the same clock; no alignment or target lookup is inferred.
    pub fn receive<T>(
        &mut self,
        source: &ExactAcousticOccurrence,
        source_origin: Rat,
        observed: &ExactAcousticOccurrence,
        observed_origin: Rat,
        returned: impl FnOnce(TemporalAcousticReturn<'_, 'c>) -> T,
    ) -> Result<T> {
        let cut = self.contacts();
        let next = cut
            .checked_add(1)
            .ok_or_else(|| TemporalAcousticError::Invalid("contact cut overflow".into()))?;
        let base = cut
            .checked_mul(8)
            .and_then(|v| v.checked_add(16))
            .filter(|v| v.checked_add(4).is_some())
            .ok_or_else(|| TemporalAcousticError::Invalid("lineage extent".into()))?;
        let x = self.source_chart(
            source,
            source_origin.clone(),
            self.chart.source_receiver,
            PhaseCurrentLineageId(base),
        )?;
        let y = self.source_chart(
            observed,
            observed_origin.clone(),
            self.chart.output_receiver,
            PhaseCurrentLineageId(base + 1),
        )?;
        self.history
            .try_reserve(1)
            .map_err(|e| TemporalAcousticError::Invalid(e.to_string()))?;
        let x = x.mount_complete(self.surface)?;
        let producing = self.current.snapshot();
        let started = Instant::now();
        let before = self.surface.census();
        let prediction = convolve_enclosed_resident(
            self.surface,
            x.temporal_view()?,
            producing.view(),
            self.chart.output_receiver,
            PhaseCurrentLineageId(base + 2),
        )?;
        let prediction_work = TemporalAcousticWork::between(before, self.surface.census(), started);
        let y = y.mount_complete(self.surface)?;
        let started = Instant::now();
        let before = self.surface.census();
        let difference = compare_enclosed_resident(
            self.surface,
            prediction.view(),
            y.temporal_view()?,
            PhaseCurrentLineageId(base + 3),
        )?;
        let difference_work = TemporalAcousticWork::between(before, self.surface.census(), started);
        let receipt = TemporalAcousticContactReceipt {
            source: TemporalRecording::from_occurrence(source, source_origin),
            observed: TemporalRecording::from_occurrence(observed, observed_origin),
            producing_cut: cut,
            successor_cut: next,
            prediction_lineage: PhaseCurrentLineageId(base + 2),
            difference_lineage: PhaseCurrentLineageId(base + 3),
            contact_lineage: PhaseCurrentLineageId(base + 4),
            support: difference.support().clone(),
        };
        let family =
            ResidentTemporalConditionPreimage::from_return(&producing, &prediction, &difference)?;
        let started = Instant::now();
        let before = self.surface.census();
        let contact = self.current.contact(family, receipt.contact_lineage)?;
        let contact_work = TemporalAcousticWork::between(before, self.surface.census(), started);
        self.history.push(receipt);
        Ok(returned(TemporalAcousticReturn {
            prediction: &prediction,
            difference: &difference,
            contact: &contact,
            receipt: self.history.last().expect("completed contact receipt"),
            prediction_work,
            difference_work,
            contact_work,
        }))
    }

    /// Read the continuing response without a target recording or a condition update.
    pub fn predict<T>(
        &self,
        source: &ExactAcousticOccurrence,
        origin: Rat,
        lineage: PhaseCurrentLineageId,
        received: impl FnOnce(&ResidentEnclosedPhaseConvolution<'_, '_, 'c>, TemporalAcousticWork) -> T,
    ) -> Result<T> {
        let x = self.source_chart(source, origin, self.chart.source_receiver, lineage)?;
        let x = x.mount_complete(self.surface)?;
        let standing = self.current.snapshot();
        let started = Instant::now();
        let before = self.surface.census();
        let prediction = convolve_enclosed_resident(
            self.surface,
            x.temporal_view()?,
            standing.view(),
            self.chart.output_receiver,
            lineage,
        )?;
        let work = TemporalAcousticWork::between(before, self.surface.census(), started);
        Ok(received(&prediction, work))
    }

    /// Cold, atomic no-overwrite publication. The live owner stays available if publication fails.
    pub fn save(&self, path: impl AsRef<Path>) -> Result<PublicationReceipt<()>> {
        let path = path.as_ref();
        if path.exists() {
            return Err(PublicationError::ExistingTarget {
                path: path.to_path_buf(),
            }
            .into());
        }
        let rest = self.current.rest()?;
        let header = Header {
            chart: self.chart.clone(),
            history: self.history.clone(),
        };
        validate_history(&header, &rest)?;
        let header = serde_json::to_vec(&header)?;
        Ok(publish_new(path, |file| {
            file.write_all(MAGIC)?;
            write_len(file, header.len())?;
            file.write_all(&header)?;
            let length_at = file.stream_position()?;
            file.write_all(&0u64.to_le_bytes())?;
            let native_start = file.stream_position()?;
            rest.write(file).map_err(io::Error::other)?;
            let footer = file.stream_position()?;
            file.seek(SeekFrom::Start(length_at))?;
            file.write_all(&(footer - native_start).to_le_bytes())?;
            let digest = hash_prefix(file, footer)?;
            file.seek(SeekFrom::Start(footer))?;
            file.write_all(&digest)?;
            file.write_all(END)
        })?)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    chart: TemporalAcousticChart,
    history: Vec<TemporalAcousticContactReceipt>,
}

pub struct SavedTemporalAcousticSession {
    header: Header,
    response: ResidentTemporalConditionRest,
}
impl SavedTemporalAcousticSession {
    pub fn chart(&self) -> &TemporalAcousticChart {
        &self.header.chart
    }
    pub fn history(&self) -> &[TemporalAcousticContactReceipt] {
        &self.header.history
    }
    pub fn response(&self) -> &ResidentTemporalConditionRest {
        &self.response
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let mut file = File::open(path)?;
        let length = file.metadata()?.len();
        let minimum = (MAGIC.len() + END.len() + 32 + 16) as u64;
        if length < minimum {
            return Err(TemporalAcousticError::Invalid("checkpoint frame".into()));
        }
        let footer = length - END.len() as u64 - 32;
        file.seek(SeekFrom::Start(footer))?;
        let mut digest = [0; 32];
        file.read_exact(&mut digest)?;
        let mut end = vec![0; END.len()];
        file.read_exact(&mut end)?;
        if end != END || hash_prefix(&mut file, footer)? != digest {
            return Err(TemporalAcousticError::Invalid(
                "checkpoint checksum/footer".into(),
            ));
        }
        file.seek(SeekFrom::Start(0))?;
        let mut magic = vec![0; MAGIC.len()];
        file.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(TemporalAcousticError::Invalid(
                "checkpoint kind/version".into(),
            ));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut file, footer)?)?;
        let mut length = [0; 8];
        file.read_exact(&mut length)?;
        let length = u64::from_le_bytes(length);
        if file.stream_position()?.checked_add(length) != Some(footer) {
            return Err(TemporalAcousticError::Invalid("native rest extent".into()));
        }
        let response = ResidentTemporalConditionRest::read(&mut file, length)?;
        if file.stream_position()? != footer {
            return Err(TemporalAcousticError::Invalid(
                "trailing native rest".into(),
            ));
        }
        validate_history(&header, &response)?;
        Ok(Self { header, response })
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<TemporalAcousticSession<'c>> {
        validate_history(&self.header, &self.response)?;
        let current = ResidentTemporalConditionCurrent::remount(surface, self.response)?;
        Ok(TemporalAcousticSession {
            surface,
            current,
            chart: self.header.chart,
            history: self.header.history,
        })
    }
}

fn validate_chart(
    chart: &TemporalAcousticChart,
    response: &holonic_engine::native_ecology::constitutive_fibre::TemporalResponseChart,
) -> Result<()> {
    if response.raw_extent == 0
        || response.phase_extent == 0
        || chart.sample_rate == 0
        || chart.pcm_divisor <= 0
        || response.sample_step != Rat::new(1.into(), chart.sample_rate.into())
    {
        return Err(TemporalAcousticError::Invalid(
            "PCM/response chart clock or divisor".into(),
        ));
    }
    Ok(())
}
fn validate_history(header: &Header, response: &ResidentTemporalConditionRest) -> Result<()> {
    validate_chart(&header.chart, response.chart())?;
    if header.history.len() as u64 != response.contacts() {
        return Err(TemporalAcousticError::Invalid(
            "recording/contact population".into(),
        ));
    }
    for (cut, receipt) in header.history.iter().enumerate() {
        if receipt.producing_cut != cut as u64
            || receipt.successor_cut != cut as u64 + 1
            || receipt.source.sample_rate != header.chart.sample_rate
            || receipt.observed.sample_rate != header.chart.sample_rate
            || receipt.source.frames == 0
            || receipt.observed.frames == 0
        {
            return Err(TemporalAcousticError::Invalid(
                "recording/contact chronology".into(),
            ));
        }
        let prediction_extent = receipt
            .source
            .frames
            .checked_add(response.chart().raw_extent)
            .and_then(|n| n.checked_sub(1))
            .ok_or_else(|| TemporalAcousticError::Invalid("recording extent".into()))?;
        let step = &response.chart().sample_step;
        let support = holonic_engine::phase_current::resident::comparison_support(
            header.chart.output_receiver,
            &(&receipt.source.origin + &response.chart().origin),
            step,
            response.chart().phase_extent,
            prediction_extent,
            header.chart.output_receiver,
            &receipt.observed.origin,
            step,
            response.chart().phase_extent,
            receipt.observed.frames,
        )?;
        if receipt.support != support {
            return Err(TemporalAcousticError::Invalid(
                "recording comparison support".into(),
            ));
        }
        let base = (cut as u64)
            .checked_mul(8)
            .and_then(|n| n.checked_add(16))
            .filter(|v| v.checked_add(4).is_some())
            .ok_or_else(|| TemporalAcousticError::Invalid("contact lineage extent".into()))?;
        if receipt.prediction_lineage.0 != base + 2
            || receipt.difference_lineage.0 != base + 3
            || receipt.contact_lineage.0 != base + 4
        {
            return Err(TemporalAcousticError::Invalid(
                "contact lineage chronology".into(),
            ));
        }
        if response.lineage_at(receipt.successor_cut) != Some(receipt.contact_lineage) {
            return Err(TemporalAcousticError::Invalid(
                "native/application contact lineage".into(),
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
