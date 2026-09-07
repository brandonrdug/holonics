//! Exterior temporal sections entering the shared native material field.
//!
//! A chart cell supplies a complete addressed coefficient field, not a series of scalar native
//! operations. The existing constitutive field owns scattering, joint relation formation, both
//! source branches and the successor. Cell extent is a declared receiver aperture, never an
//! inferred semantic grain. The complete section stays available as the reconstruction fibre.

use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConstitutiveFibreError, NativeConstitutiveField, NativeFieldEmission,
        NativeFieldOccurrence, NativeFieldReceiverStatus, NativeFieldStep, NativePhaseCurrent,
        ResidentConstitutiveCurrent,
    },
    phase_current::{ExactPhaseCurrentSection, PhaseCurrentLineageId, PhaseCurrentReceiverId},
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use life::mathematical_source::ExactAcousticOccurrence;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use serde::Serialize;
use std::ops::Range;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AcousticFieldError {
    #[error("acoustic temporal chart: {0}")]
    Chart(String),
    #[error(transparent)]
    Native(#[from] ConstitutiveFibreError),
}

/// Exterior source coordinates only. Neither the occurrence number nor its clock supplies contact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AcousticFieldSupport {
    pub source_occurrence: String,
    pub cell: usize,
    pub coefficient_from: usize,
    pub coefficient_until: usize,
    pub begin: BigRational,
    pub end: BigRational,
    pub structural_padding: usize,
}

/// One immutable chart cell mounted as a resident rational current. The chart borrow keeps the
/// complete raw PCM source and its receiver/lineage testimony live while the cell is consumed.
pub struct AcousticFieldCell<'surface, 'source> {
    chart: &'source AcousticFieldChart,
    section: ResidentSection<'surface>,
    support: AcousticFieldSupport,
}

impl<'surface, 'source> AcousticFieldCell<'surface, 'source> {
    pub fn section(&self) -> &ResidentSection<'surface> {
        &self.section
    }

    pub fn rational(
        &self,
    ) -> Result<ResidentConstitutiveCurrent<'_, 'surface>, AcousticFieldError> {
        Ok(ResidentConstitutiveCurrent::rational(&self.section)?)
    }

    pub fn chart(&self) -> &'source AcousticFieldChart {
        self.chart
    }

    pub fn support(&self) -> &AcousticFieldSupport {
        &self.support
    }

    pub fn receiver(&self) -> PhaseCurrentReceiverId {
        self.chart.section.receiver
    }

    pub fn lineage(&self) -> PhaseCurrentLineageId {
        self.chart.section.lineage
    }

    pub fn divisor(&self) -> i64 {
        self.chart.divisor
    }

    pub fn sample_step(&self) -> &BigRational {
        &self.chart.section.sample_step
    }
}

/// A cold reversible chart over the existing phase-current section. Its private construction
/// prevents arbitrary serialized coefficients from being accepted as a validated PCM chart.
pub struct AcousticFieldChart {
    section: ExactPhaseCurrentSection,
    source_occurrence: String,
    // Exterior delivery lineage copied from the decoded occurrence, never semantic identity.
    source_locator: String,
    source_sha256: String,
    source_octets: u64,
    source_range: Range<usize>,
    recording_samples: usize,
    divisor: i64,
    cursor: usize,
}

impl AcousticFieldChart {
    pub fn from_acoustic(
        source: &ExactAcousticOccurrence,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: BigRational,
        port_extent: usize,
        divisor: i64,
    ) -> Result<Self, AcousticFieldError> {
        Self::from_acoustic_range(
            source,
            receiver,
            lineage,
            origin,
            0..source.samples.len(),
            port_extent,
            divisor,
        )
    }

    /// Address a half-open sample span of the original recording. The origin belongs to the
    /// recording's clock; the section starts at its actual offset on that clock. The selected
    /// PCM is retained exactly, and its parent address survives without copying the whole WAV.
    /// Annotation support and any sub-sample overhang belong to the caller's interval receipt.
    #[allow(clippy::too_many_arguments)]
    pub fn from_acoustic_range(
        source: &ExactAcousticOccurrence,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        recording_origin: BigRational,
        source_range: Range<usize>,
        port_extent: usize,
        divisor: i64,
    ) -> Result<Self, AcousticFieldError> {
        if source.sample_rate == 0 || divisor <= 0 {
            return Err(AcousticFieldError::Chart(
                "positive clock rate and divisor required".into(),
            ));
        }
        let samples = source
            .samples
            .get(source_range.clone())
            .filter(|samples| !samples.is_empty())
            .ok_or_else(|| {
                AcousticFieldError::Chart("empty or outside recording sample span".into())
            })?;
        let sample_step = BigRational::new(1.into(), source.sample_rate.into());
        let origin = recording_origin + &sample_step * BigInt::from(source_range.start);
        let section = ExactPhaseCurrentSection::from_integers(
            receiver,
            lineage,
            origin,
            sample_step,
            port_extent,
            samples.iter().map(|s| BigInt::from(*s)).collect(),
        )
        .map_err(|e| AcousticFieldError::Chart(e.to_string()))?;
        Ok(Self {
            section,
            source_occurrence: source.occurrence.clone(),
            source_locator: source.locator.clone(),
            source_sha256: source.source_sha256.clone(),
            source_octets: source.source_octets,
            source_range,
            recording_samples: source.samples.len(),
            divisor,
            cursor: 0,
        })
    }

    pub fn section(&self) -> &ExactPhaseCurrentSection {
        &self.section
    }
    pub fn source_locator(&self) -> &str {
        &self.source_locator
    }
    pub fn source_sha256(&self) -> &str {
        &self.source_sha256
    }
    pub fn source_octets(&self) -> u64 {
        self.source_octets
    }
    pub fn source_range(&self) -> Range<usize> {
        self.source_range.clone()
    }
    pub fn recording_samples(&self) -> usize {
        self.recording_samples
    }
    pub fn divisor(&self) -> i64 {
        self.divisor
    }
    pub fn cursor(&self) -> usize {
        self.cursor
    }
    pub fn is_complete(&self) -> bool {
        self.cursor == self.section.cells.len()
    }

    /// Complete inverse of this exterior chart, including zeros but excluding structural padding.
    pub fn reconstruct_samples(&self) -> Vec<i16> {
        // The only constructor accepts i16; neither execution nor callers can mutate coefficients.
        self.section
            .flat_values()
            .iter()
            .map(|v| v.to_i16().expect("validated source"))
            .collect()
    }

    fn support_at(&self, cell: usize) -> Result<AcousticFieldSupport, AcousticFieldError> {
        if cell >= self.section.cells.len() {
            return Err(AcousticFieldError::Chart("cell out of range".into()));
        }
        let width = self.section.phase_extent as usize;
        let from = cell * width;
        let until = (from + width).min(self.section.raw_extent());
        let at = |i: usize| &self.section.origin + &self.section.sample_step * BigInt::from(i);
        Ok(AcousticFieldSupport {
            source_occurrence: self.source_occurrence.clone(),
            cell,
            coefficient_from: self.source_range.start + from,
            coefficient_until: self.source_range.start + until,
            begin: at(from),
            end: at(until),
            structural_padding: width - (until - from),
        })
    }

    pub fn next_support(&self) -> Option<AcousticFieldSupport> {
        self.support_at(self.cursor).ok()
    }

    /// Mount one chosen temporal cell as `(sample / divisor, 0)` complex coordinates. The
    /// operation is read-only with respect to this chart: it neither advances `cursor` nor
    /// changes the retained PCM source or its receiver-local chronology.
    pub fn mount_cell<'surface, 'source>(
        &'source self,
        surface: &'surface ResidentSurface<'surface>,
        cell: usize,
    ) -> Result<AcousticFieldCell<'surface, 'source>, AcousticFieldError> {
        let support = self.support_at(cell)?;
        let width = self.section.phase_extent as usize;
        let mut words = Vec::with_capacity(2 * width + 1);
        for sample in &self.section.cells[cell] {
            let sample = sample.to_i64().expect("validated source");
            words.push((sample, sample));
            words.push((0, 0));
        }
        words.push((self.divisor, self.divisor));
        let rest = ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
            .map_err(AcousticFieldError::Chart)?;
        let section = surface
            .mount_section_rest(&rest)
            .map_err(ConstitutiveFibreError::from)?;
        Ok(AcousticFieldCell {
            chart: self,
            section,
            support,
        })
    }

    fn prepare(&self, source: Option<NativeFieldEmission>) -> NativeFieldOccurrence {
        let incoming = self.section.cells[self.cursor]
            .iter()
            .map(|v| {
                NativePhaseCurrent::new(v.to_i64().expect("validated source"), 0, self.divisor)
                    .expect("positive divisor")
            })
            .collect();
        match source {
            Some(source) => NativeFieldOccurrence::through(source, incoming),
            None => NativeFieldOccurrence::entering(incoming),
        }
    }

    /// Conduct one complete coefficient field through the caller's existing native owner.
    ///
    /// A source handle is accepted only when the application declares an actual receiving
    /// interaction. Time adjacency alone never supplies one. Refusal restores that same handle
    /// and leaves the chart cursor unchanged. Success advances only this exterior source cursor.
    /// The returned classification is an observer projection; the full native fibre stays resident.
    pub fn advance_status(
        &mut self,
        field: &mut NativeConstitutiveField<'_>,
        receiving: &mut Option<NativeFieldEmission>,
    ) -> Result<
        (
            AcousticFieldSupport,
            NativeFieldStep<NativeFieldReceiverStatus>,
        ),
        AcousticFieldError,
    > {
        let support = self
            .next_support()
            .ok_or_else(|| AcousticFieldError::Chart("source complete".into()))?;
        if field.nodes() != self.section.phase_extent as usize {
            return Err(AcousticFieldError::Chart(
                "material port extent differs from temporal chart".into(),
            ));
        }
        let mut occurrence = self.prepare(receiving.take());
        match field.advance_status(&mut occurrence) {
            Ok(step) => {
                self.cursor += 1;
                Ok((support, step))
            }
            Err(error) => {
                *receiving = occurrence.take_source();
                Err(error.into())
            }
        }
    }
}

#[cfg(test)]
mod tests;
