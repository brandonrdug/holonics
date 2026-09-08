//! Cold persistence of the local relation, including its declared source law. The complete
//! echelon basis retains the open vertical fibre. Remount installs it without fitting or replay.
use super::circulation::rest::{blob, expect, point_section, read_blob};
use super::*;
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HNA-CONSTITUTIVE-FIBRE-REST\x01";
const END: &[u8] = b"HNA-CONSTITUTIVE-FIBRE-END\x01";
type Error = ConstitutiveFibreError;
fn invalid(detail: impl std::fmt::Display) -> Error {
    Error::Rest(detail.to_string())
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    source_width: usize,
    target_width: usize,
    source_chart: ConstitutiveSourceChart,
    occurrences: u64,
}

/// An exterior chart, deliberately not Clone. It does not replace the history/capability rest
/// of a containing field or circulation, nor authenticate externally authored development.
#[derive(Debug, PartialEq, Eq)]
pub struct ResidentConstitutiveFibreRest {
    header: Header,
    basis: ResidentSectionRest,
}

impl ResidentConstitutiveFibreRest {
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.header.source_chart
    }
    pub fn source_width(&self) -> usize {
        self.header.source_width
    }
    pub fn target_width(&self) -> usize {
        self.header.target_width
    }
    pub fn occurrences(&self) -> u64 {
        self.header.occurrences
    }

    /// Check the exact carrier and native echelon invariant at the exterior I/O boundary.
    /// This verifies a serialized state, not the truth of a supplied developmental history.
    pub fn validate(&self) -> Result<(), Error> {
        let h = &self.header;
        let width = h
            .source_width
            .checked_add(h.target_width)
            .ok_or(Error::Shape)?;
        if h.source_width == 0 || h.target_width == 0 || width > u32::MAX as usize - 4 {
            return Err(Error::Shape);
        }
        if let ConstitutiveSourceChart::BilinearContact {
            source_complex: s,
            condition_complex: c,
        } = h.source_chart
        {
            let expected = s
                .checked_mul(c)
                .and_then(|n| n.checked_add(s))
                .and_then(|n| n.checked_add(c))
                .and_then(|n| n.checked_mul(2));
            if s == 0 || c == 0 || expected != Some(h.source_width) || h.target_width % 2 != 0 {
                return Err(invalid("bilinear source/receiver chart dimensions"));
            }
        }
        point_section(&self.basis, width, width)?;
        let mut rank = 0u64;
        for p in 0..width {
            let row = &self.basis.intervals[p * width..(p + 1) * width];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(invalid("constitutive basis positive-pivot echelon chart"));
            }
            rank += u64::from(row[p].0 > 0);
        }
        if rank > h.occurrences {
            return Err(invalid("relation rank exceeds completed occurrences"));
        }
        Ok(())
    }

    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &self.basis.canonical_bytes().map_err(invalid)?)?;
        out.write_all(END).map_err(invalid)
    }
    /// `octets` is the containing wire's actual extent, not a native capacity.
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let basis = ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid)?;
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(invalid("trailing constitutive rest bytes"));
        }
        let rest = Self { header, basis };
        rest.validate()?;
        Ok(rest)
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    /// Explicit counted cold export. No native occurrence, fitting, or history replay occurs.
    pub fn rest(&self) -> Result<ResidentConstitutiveFibreRest, Error> {
        if !self.usable {
            return Err(Error::Uncertain);
        }
        let rest = ResidentConstitutiveFibreRest {
            header: Header {
                source_width: self.source_width,
                target_width: self.target_width,
                source_chart: self.source_chart,
                occurrences: self.occurrences,
            },
            basis: self.inspect_relation()?,
        };
        rest.validate()?;
        Ok(rest)
    }

    /// Consume one cold chart into one continuing move owner, preserving the full relation.
    pub fn remount(
        surface: &'chart ResidentSurface<'chart>,
        rest: ResidentConstitutiveFibreRest,
    ) -> Result<Self, Error> {
        rest.validate()?;
        let width = rest.header.source_width + rest.header.target_width;
        let required = ResidentSurface::constitutive_fibre_scratch(width).ok_or(Error::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if required > available as usize {
            return Err(Error::ScratchAperture {
                required,
                available,
            });
        }
        Ok(Self {
            basis: surface.mount_section_rest(&rest.basis)?,
            surface,
            source_width: rest.header.source_width,
            target_width: rest.header.target_width,
            source_chart: rest.header.source_chart,
            occurrences: rest.header.occurrences,
            usable: true,
        })
    }
}

#[cfg(test)]
mod tests;
