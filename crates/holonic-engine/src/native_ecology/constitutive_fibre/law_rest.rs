//! Rest of the learned local law, without its observation population or a current waveform.
//! The echelon relation retains domain and vertical fibre. Remount consumes one cold chart;
//! subsequent currents use the existing resident operation and can further develop that law.
use super::circulation::rest::{blob, expect, point_bytes, point_section, read_blob, read_point};
use super::*;
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-CONSTITUTIVE-FIBRE\x01";
const END: &[u8] = b"HOLONIC-CONSTITUTIVE-END\x01";

#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LawChart {
    source_width: usize,
    target_width: usize,
    source_chart: ConstitutiveSourceChart,
    occurrences: u64,
}

/// The relation is generative material for its declared local source law. Chronology is a cut,
/// not stored observation history. This is not a whole-ecology or pending-current checkpoint.
/// Source provenance belongs to the causing application/record; validation does not invent it.
#[derive(Debug, PartialEq, Eq)]
pub struct ConstitutiveFibreRest {
    chart: LawChart,
    basis: ResidentSectionRest,
}

impl ConstitutiveFibreRest {
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.chart.source_chart
    }
    pub fn source_width(&self) -> usize {
        self.chart.source_width
    }
    pub fn target_width(&self) -> usize {
        self.chart.target_width
    }
    pub fn occurrences(&self) -> u64 {
        self.chart.occurrences
    }
    pub fn relation(&self) -> &ResidentSectionRest {
        &self.basis
    }
    pub fn rank(&self) -> usize {
        (0..self.basis.width)
            .filter(|p| self.basis.intervals[p * self.basis.width + p].0 > 0)
            .count()
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let h = &self.chart;
        let width = h
            .source_width
            .checked_add(h.target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if h.source_width == 0 || h.target_width == 0 || width > u32::MAX as usize - 4 {
            return Err(ConstitutiveFibreError::Shape);
        }
        if let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = h.source_chart
        {
            let expected = source_complex
                .checked_mul(condition_complex)
                .and_then(|n| n.checked_add(source_complex))
                .and_then(|n| n.checked_add(condition_complex))
                .and_then(|n| n.checked_mul(2));
            if source_complex == 0
                || condition_complex == 0
                || expected != Some(h.source_width)
                || h.target_width % 2 != 0
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        point_section(&self.basis, width, width)?;
        for p in 0..width {
            let row = &self.basis.intervals[p * width..(p + 1) * width];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(ConstitutiveFibreError::Rest(
                    "constitutive law is not positive-pivot echelon material".into(),
                ));
            }
        }
        if self.rank() as u64 > h.occurrences {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(MAGIC).map_err(rest_error)?;
        blob(out, &serde_json::to_vec(&self.chart).map_err(rest_error)?)?;
        blob(out, &point_bytes(&self.basis)?)?;
        out.write_all(END).map_err(rest_error)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let chart = serde_json::from_slice(&read_blob(&mut input)?).map_err(rest_error)?;
        let basis = read_point(&read_blob(&mut input)?)?;
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(rest_error("trailing constitutive law bytes"));
        }
        let result = Self { chart, basis };
        result.validate()?;
        Ok(result)
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        self.validate()?;
        ResidentConstitutiveFibre::check_extent(
            surface,
            self.chart.source_width,
            self.chart.target_width,
        )?;
        Ok(ResidentConstitutiveFibre {
            basis: surface.mount_section_rest(&self.basis)?,
            surface,
            source_width: self.chart.source_width,
            target_width: self.chart.target_width,
            source_chart: self.chart.source_chart,
            occurrences: self.chart.occurrences,
            usable: true,
        })
    }
}
fn rest_error(error: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(error.to_string())
}

impl ResidentConstitutiveFibre<'_> {
    /// A cold view of the current learned law, with no source/current archive. The caller may
    /// persist this rest and release the live owner; remount takes the rest by value.
    pub fn rest(&self) -> Result<ConstitutiveFibreRest, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let rest = ConstitutiveFibreRest {
            chart: LawChart {
                source_width: self.source_width,
                target_width: self.target_width,
                source_chart: self.source_chart,
                occurrences: self.occurrences,
            },
            basis: self.surface.detach_section(&self.basis, 64)?,
        };
        rest.validate()?;
        Ok(rest)
    }
}

#[cfg(test)]
mod tests;
