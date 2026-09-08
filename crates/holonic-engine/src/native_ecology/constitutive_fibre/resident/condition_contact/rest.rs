use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_section, read_blob,
};
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HNA-CONDITION-CURRENT-REST\x01";
const END: &[u8] = b"HNA-CONDITION-CURRENT-END\x01";
type Error = ConstitutiveFibreError;

fn invalid(detail: impl std::fmt::Display) -> Error {
    Error::Rest(format!("condition current rest: {detail}"))
}

#[cfg(test)]
mod tests;

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    source_complex: usize,
    condition_complex: usize,
    width: usize,
    metric: ConditionContactMetric,
    contacts: u64,
}

/// Exact cold state of one retained bilinear condition current. This is a carrier for the
/// current's continuing owner, not a relation rest and not a source-capability archive.
#[derive(Debug, PartialEq, Eq)]
pub struct ResidentConditionCurrentRest {
    header: Header,
    section: ResidentSectionRest,
}

fn exact_sum(a: i64, b: i64, c: i64) -> bool {
    BigInt::from(a) + BigInt::from(b) == BigInt::from(c)
}

fn exact_difference(a: i64, b: i64, c: i64) -> bool {
    BigInt::from(a) - BigInt::from(b) == BigInt::from(c)
}

fn energy_sum(values: impl Iterator<Item = i64>) -> BigInt {
    values.fold(BigInt::from(0), |sum, value| {
        sum + BigInt::from(value) * BigInt::from(value)
    })
}

impl ResidentConditionCurrentRest {
    pub fn width(&self) -> usize {
        self.header.width
    }

    pub fn contacts(&self) -> u64 {
        self.header.contacts
    }

    pub fn metric(&self) -> ConditionContactMetric {
        self.header.metric
    }

    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        ConstitutiveSourceChart::BilinearContact {
            source_complex: self.header.source_complex,
            condition_complex: self.header.condition_complex,
        }
    }

    /// Validate exact carrier shape and the equations emitted by the condition-contact kernel.
    /// This checks recorded structure only; it does not fit or infer a contact law.
    pub fn validate(&self) -> Result<(), Error> {
        let h = &self.header;
        if h.source_complex == 0 || h.condition_complex == 0 {
            return Err(invalid("bilinear chart dimension"));
        }
        let source_width = h
            .source_complex
            .checked_mul(h.condition_complex)
            .and_then(|n| n.checked_add(h.source_complex))
            .and_then(|n| n.checked_add(h.condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| invalid("flattened source chart extent"))?;
        if source_width == 0 || source_width > u32::MAX as usize - 4 {
            return Err(invalid("flattened source chart aperture"));
        }
        let width = h
            .condition_complex
            .checked_mul(2)
            .ok_or_else(|| invalid("condition chart extent"))?;
        let section_width = width
            .checked_mul(5)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(|| invalid("condition section extent"))?;
        if h.width != width {
            return Err(invalid("condition width does not match chart"));
        }
        point_section(&self.section, 1, section_width)?;
        let words = &self.section.intervals;
        if words.iter().any(|(lo, hi)| lo != hi) {
            return Err(invalid("condition section is not point-valued"));
        }
        let denominator = words[5 * width].0;
        if denominator <= 0 {
            return Err(invalid("condition denominator"));
        }
        let status = words[5 * width + 1].0;
        if !matches!(status, 0 | 1) {
            return Err(invalid("condition disposition"));
        }
        if h.contacts == 0 && status != 0 {
            return Err(invalid(
                "initial current cannot carry an inferred empty family",
            ));
        }
        let row = |at: usize, j: usize| words[at * width + j].0;
        if status == 1 {
            for j in 0..width {
                if row(0, j) != row(1, j) || row(2, j) != 0 || row(3, j) != 0 || row(4, j) != 0 {
                    return Err(invalid("outside-family current was not preserved"));
                }
            }
        } else {
            for j in 0..width {
                if !exact_difference(row(2, j), row(3, j), row(4, j))
                    || !exact_sum(row(0, j), row(4, j), row(1, j))
                {
                    return Err(invalid("condition contact equations"));
                }
            }
            if energy_sum(
                (0..width)
                    .map(|j| row(0, j))
                    .chain((0..width).map(|j| row(2, j))),
            ) != energy_sum(
                (0..width)
                    .map(|j| row(1, j))
                    .chain((0..width).map(|j| row(3, j))),
            ) {
                return Err(invalid("unit-admittance contact energy"));
            }
            if h.contacts == 0
                && (0..width).any(|j| {
                    row(0, j) != row(1, j) || row(2, j) != 0 || row(3, j) != 0 || row(4, j) != 0
                })
            {
                return Err(invalid("initial condition current was not preserved"));
            }
        }
        Ok(())
    }

    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &self.section.canonical_bytes().map_err(invalid)?)?;
        out.write_all(END).map_err(invalid)
    }

    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let section = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(invalid("trailing condition rest bytes"));
        }
        let rest = Self { header, section };
        rest.validate()?;
        Ok(rest)
    }
}

impl<'chart> ResidentConditionCurrent<'chart> {
    pub fn rest(&self) -> Result<ResidentConditionCurrentRest, Error> {
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.source_chart
        else {
            return Err(invalid("condition current requires bilinear chart"));
        };
        let rest = ResidentConditionCurrentRest {
            header: Header {
                source_complex,
                condition_complex,
                width: self.width,
                metric: self.metric,
                contacts: self.contacts,
            },
            section: self.surface.detach_section(&self.section, 64)?,
        };
        rest.validate()?;
        Ok(rest)
    }

    /// Consume one exact cold condition current into one new move owner. No native operation is
    /// replayed and no source capability is created; source/frame provenance belongs elsewhere.
    pub fn remount(
        surface: &'chart ResidentSurface<'chart>,
        rest: ResidentConditionCurrentRest,
    ) -> Result<Self, Error> {
        rest.validate()?;
        let ResidentConditionCurrentRest { header, section } = rest;
        Ok(Self {
            surface,
            section: Rc::new(surface.mount_section_rest(&section)?),
            source_chart: ConstitutiveSourceChart::BilinearContact {
                source_complex: header.source_complex,
                condition_complex: header.condition_complex,
            },
            metric: header.metric,
            width: header.width,
            contacts: header.contacts,
        })
    }
}
