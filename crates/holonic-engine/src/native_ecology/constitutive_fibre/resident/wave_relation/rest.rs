use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-WAVE-RELATION\x01";
const END: &[u8] = b"HOLONIC-WAVE-RELATION-END\x01";
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
#[derive(Serialize, serde::Deserialize, Debug, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Header {
    roots: usize,
    conditions: usize,
    cut: u64,
}
#[derive(Debug, PartialEq, Eq)]
pub struct NormalWaveRelationRest {
    header: Header,
    basis: ResidentSectionRest,
    fixed: ResidentSectionRest,
}
impl NormalWaveRelationRest {
    pub fn roots(&self) -> usize {
        self.header.roots
    }
    pub fn relation_cut(&self) -> u64 {
        self.header.cut
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let n = self.header.roots;
        let k = self.header.conditions;
        let q = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let w = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let hw = k
            .checked_mul(2)
            .and_then(|v| v.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if n == 0 || k == 0 || w > u32::MAX as usize {
            return Err(ConstitutiveFibreError::Shape);
        }
        point_section(&self.basis, w, w)?;
        point_section(&self.fixed, 1, hw)?;
        if self.fixed.intervals[hw - 1].0 <= 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        for p in 0..w {
            let row = &self.basis.intervals[p * w..(p + 1) * w];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(invalid(
                    "derived wave relation is not positive-pivot echelon material",
                ));
            }
            // The declared chart preserves lambda and anchor and joins the actual c as next p.
            for j in 0..2 + 4 * n {
                if row[q + j].0 != row[j].0 {
                    return Err(invalid("wave relation changes the retained anchor"));
                }
            }
            for j in 0..2 * n {
                if row[q + 2 + 4 * n + j].0 != row[2 + 6 * n + j].0 {
                    return Err(invalid("wave relation loses its current join"));
                }
            }
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        blob(out, &point_bytes(&self.basis)?)?;
        blob(out, &point_bytes(&self.fixed)?)?;
        out.write_all(END).map_err(invalid)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let basis = read_point(&read_blob(&mut input)?)?;
        let fixed = read_point(&read_blob(&mut input)?)?;
        expect(&mut input, END)?;
        let mut extra = [0u8; 1];
        if input.read(&mut extra).map_err(invalid)? != 0 {
            return Err(invalid("trailing wave relation data"));
        }
        let rest = Self {
            header,
            basis,
            fixed,
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        self.validate()?;
        Ok(ResidentWaveRelation::new(
            s,
            s.mount_section_rest(&self.basis)?,
            s.mount_section_rest(&self.fixed)?,
            self.header.roots,
            self.header.conditions,
            self.header.cut,
            Rc::new(()),
        ))
    }
}
impl ResidentWaveRelation<'_> {
    pub fn rest(&self) -> Result<NormalWaveRelationRest, ConstitutiveFibreError> {
        let rest = NormalWaveRelationRest {
            header: Header {
                roots: self.roots,
                conditions: self.condition_complex,
                cut: self.relation_cut,
            },
            basis: self.surface.detach_section(&self.basis, 64)?,
            fixed: self.surface.detach_section(&self.fixed, 64)?,
        };
        rest.validate()?;
        Ok(rest)
    }
}
