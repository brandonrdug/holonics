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
    },
    phase_current::{ExactPhaseCurrentSection, PhaseCurrentLineageId, PhaseCurrentReceiverId},
};
use life::mathematical_source::ExactAcousticOccurrence;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use serde::Serialize;
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

/// A cold reversible chart over the existing phase-current section. Its private construction
/// prevents arbitrary serialized coefficients from being accepted as a validated PCM chart.
pub struct AcousticFieldChart {
    section: ExactPhaseCurrentSection,
    source_occurrence: String,
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
        if source.sample_rate == 0 || divisor <= 0 {
            return Err(AcousticFieldError::Chart(
                "positive clock rate and divisor required".into(),
            ));
        }
        let section = ExactPhaseCurrentSection::from_integers(
            receiver,
            lineage,
            origin,
            BigRational::new(1.into(), source.sample_rate.into()),
            port_extent,
            source.samples.iter().map(|s| BigInt::from(*s)).collect(),
        )
        .map_err(|e| AcousticFieldError::Chart(e.to_string()))?;
        Ok(Self {
            section,
            source_occurrence: source.occurrence.clone(),
            divisor,
            cursor: 0,
        })
    }

    pub fn section(&self) -> &ExactPhaseCurrentSection {
        &self.section
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

    pub fn next_support(&self) -> Option<AcousticFieldSupport> {
        if self.is_complete() {
            return None;
        }
        let width = self.section.phase_extent as usize;
        let from = self.cursor * width;
        let until = (from + width).min(self.section.raw_extent());
        let at = |i: usize| &self.section.origin + &self.section.sample_step * BigInt::from(i);
        Some(AcousticFieldSupport {
            source_occurrence: self.source_occurrence.clone(),
            cell: self.cursor,
            coefficient_from: from,
            coefficient_until: until,
            begin: at(from),
            end: at(until),
            structural_padding: width - (until - from),
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
