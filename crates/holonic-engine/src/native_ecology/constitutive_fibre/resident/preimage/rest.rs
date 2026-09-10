//! Compact compatible-condition evidence: retain its constraint generator and right-hand side,
//! and decode the affine fibre on remount. No observation history or duplicate solved family.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-CONDITION-PREIMAGE\x01";
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    source_chart: ConstitutiveSourceChart,
    relation_cut: u64,
    source_width: usize,
    condition_width: usize,
    action_target_width: usize,
}
#[derive(Debug, PartialEq, Eq)]
pub struct ConditionPreimageRest {
    header: Header,
    constraint: ResidentSectionRest,
    rhs: ResidentSectionRest,
}
impl ConditionPreimageRest {
    pub fn source_chart(&self) -> ConstitutiveSourceChart {
        self.header.source_chart
    }
    pub fn relation_cut(&self) -> u64 {
        self.header.relation_cut
    }
    pub fn condition_width(&self) -> usize {
        self.header.condition_width
    }
    pub fn action_target_width(&self) -> usize {
        self.header.action_target_width
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let h = &self.header;
        let w = h
            .source_width
            .checked_add(h.condition_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if h.source_width == 0
            || h.condition_width == 0
            || h.condition_width % 2 != 0
            || h.action_target_width == 0
            || h.action_target_width % 2 != 0
            || w > u32::MAX as usize - 4
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = h.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        if source_complex == 0 || condition_complex.checked_mul(2) != Some(h.condition_width) {
            return Err(ConstitutiveFibreError::Shape);
        }
        point_section(&self.constraint, w, w)?;
        point_section(&self.rhs, 1, h.source_width + 1)?;
        if self.rhs.intervals[h.source_width].0 <= 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        for p in 0..w {
            let row = &self.constraint.intervals[p * w..(p + 1) * w];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(MAGIC).map_err(error)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(error)?)?;
        blob(out, &point_bytes(&self.constraint)?)?;
        blob(out, &point_bytes(&self.rhs)?)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header = serde_json::from_slice(&read_blob(&mut input)?).map_err(error)?;
        let constraint = read_point(&read_blob(&mut input)?)?;
        let rhs = read_point(&read_blob(&mut input)?)?;
        if input.limit() != 0 {
            return Err(error("trailing preimage bytes"));
        }
        let value = Self {
            header,
            constraint,
            rhs,
        };
        value.validate()?;
        Ok(value)
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentConditionPreimage<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let constraint = surface.mount_section_rest(&self.constraint)?;
        let rhs = surface.mount_section_rest(&self.rhs)?;
        let returned = ResidentConstitutiveReturn::allocate(
            surface,
            self.header.source_width,
            self.header.condition_width,
            self.header.relation_cut,
            self.header.source_chart,
        )?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_query(
                &lane,
                &constraint,
                ResidentConstitutiveCurrent::rational(&rhs)?,
                returned.report(),
            )?;
        }
        passage.close(0, returned.report(), 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(error(format!(
                "condition evidence decoder: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentConditionPreimage {
            inner: Rc::new(ConditionPreimageData {
                returned,
                constraint,
                rhs,
                action_target_width: self.header.action_target_width,
            }),
        })
    }
}
fn error(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl ResidentConditionPreimage<'_> {
    pub fn rest(&self) -> Result<ConditionPreimageRest, ConstitutiveFibreError> {
        let f = &self.inner.returned;
        let value = ConditionPreimageRest {
            header: Header {
                source_chart: f.source_chart,
                relation_cut: f.occurrence,
                source_width: f.source_width,
                condition_width: f.target_width,
                action_target_width: self.inner.action_target_width,
            },
            constraint: f.surface.detach_section(&self.inner.constraint, 64)?,
            rhs: f.surface.detach_section(&self.inner.rhs, 64)?,
        };
        value.validate()?;
        Ok(value)
    }
}
