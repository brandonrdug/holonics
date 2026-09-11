use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use crate::native_ecology::constitutive_fibre::{ConstitutiveReturnRest, NormalWaveRelationRest};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-ANCHORED-WAVE-FAMILY\x01";
const END: &[u8] = b"HOLONIC-ANCHORED-WAVE-FAMILY-END\x01";
#[derive(Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    passages: u64,
}
/// Complete immutable family chart, including its normal producing fibre, actual anchor ball,
/// current affine relation and last fixed-condition passage. It contains no observation archive.
#[derive(Debug,PartialEq,Eq)]
pub struct NormalWaveFamilyRest {
    origin: NormalWaveRest,
    anchor: ResidentSectionRest,
    relation: ConstitutiveReturnRest,
    last: Option<NormalWaveRelationRest>,
    coverage: Option<ResidentSectionRest>,
    passages: u64,
}
impl NormalWaveFamilyRest {
    pub(crate) fn roots(&self)->usize{self.origin.material().roots()}
    pub(crate) fn grain(&self)->ResidentGrain{self.origin.material().grain()}
    pub(crate) fn source_transport(&self)->NormalWaveTransport{self.origin.transport()}

    pub(crate) fn current_epoch(&self)->Result<u64,ConstitutiveFibreError>{self.origin.epoch().checked_add(self.passages).ok_or(ConstitutiveFibreError::Shape)}
    pub(crate) fn last_relation(&self)->Option<&NormalWaveRelationRest>{self.last.as_ref()}

    pub fn passages(&self) -> u64 {
        self.passages
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let n = self.origin.material().roots();
        let a = n.checked_mul(4).ok_or(ConstitutiveFibreError::Shape)?;
        let t = a
            .checked_mul(2)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let aw = a
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.origin
            .epoch()
            .checked_add(self.passages)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.origin.material().validate()?;
        self.relation.validate_constant_prefix(&[1, 0])?;
        point_section(&self.anchor, 1, aw)?;
        if self.origin.pending_count() != 0
            || self.relation.target_width() != t
            || wides(&self.anchor.intervals)?[a] < 0
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        match (&self.last, &self.coverage, self.passages) {
            (None, None, 0)
                if self.relation.source_width() == 1
                    && self.relation.occurrence() == self.origin.epoch() => {}
            (Some(last), Some(coverage), p) if p > 0 && self.relation.source_width() == 2 * t => {
                last.validate()?;
                let cw = t
                    .checked_mul(3)
                    .and_then(|v| v.checked_add(4))
                    .ok_or(ConstitutiveFibreError::Shape)?;
                point_section(coverage, 1, cw)?;
                if last.relation_cut() != self.relation.occurrence()
                    || self.relation.outside_domain() != matches!(coverage.intervals[0].0, 2 | 3)
                    || last.roots() != n
                    || !(0..=3).contains(&coverage.intervals[0].0)
                    || coverage.intervals[2].0 <= 0
                    || coverage.intervals[3 + t].0 <= 0
                {
                    return Err(ConstitutiveFibreError::Shape);
                }
            }
            _ => return Err(ConstitutiveFibreError::Shape),
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(
            out,
            &serde_json::to_vec(&Header {
                passages: self.passages,
            })
            .map_err(invalid)?,
        )?;
        let mut bytes = Vec::new();
        self.origin.write(&mut bytes)?;
        blob(out, &bytes)?;
        blob(out, &point_bytes(&self.anchor)?)?;
        blob(out, &serde_json::to_vec(&self.relation).map_err(invalid)?)?;
        if let (Some(last), Some(coverage)) = (&self.last, &self.coverage) {
            bytes.clear();
            last.write(&mut bytes)?;
            blob(out, &bytes)?;
            blob(out, &point_bytes(coverage)?)?;
        }
        out.write_all(END).map_err(invalid)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let bytes = read_blob(&mut input)?;
        let origin = NormalWaveRest::read_normal(&mut bytes.as_slice(), bytes.len() as u64)?;
        let anchor = read_point(&read_blob(&mut input)?)?;
        let relation = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let (last, coverage) = if header.passages > 0 {
            let bytes = read_blob(&mut input)?;
            (
                Some(NormalWaveRelationRest::read(
                    &mut bytes.as_slice(),
                    bytes.len() as u64,
                )?),
                Some(read_point(&read_blob(&mut input)?)?),
            )
        } else {
            (None, None)
        };
        expect(&mut input, END)?;
        let mut extra = [0u8; 1];
        if input.read(&mut extra).map_err(invalid)? != 0 {
            return Err(invalid("trailing anchored family data"));
        }
        let rest = Self {
            origin,
            anchor,
            relation,
            last,
            coverage,
            passages: header.passages,
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<NormalWaveFamily<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let source_body = self.origin.remount(s, |_| {})?;
        let origin = source_body.joint_source();
        if s.detach_section(origin.joint().section, 64)? != self.anchor {
            return Err(invalid("anchor does not match its producing wave fibre"));
        }
        if self.passages == 0 {
            let initial = source_body.read_family()?;
            if serde_json::to_vec(&initial.relation.rest()?).map_err(invalid)?
                != serde_json::to_vec(&self.relation).map_err(invalid)?
            {
                return Err(invalid(
                    "initial family does not describe its declared anchored join",
                ));
            }
        }
        Ok(NormalWaveFamily {
            origin: Rc::new(origin),
            relation: self.relation.remount(s)?,
            last_relation: self.last.map(|v| v.remount(s).map(Rc::new)).transpose()?,
            affine_coverage: self
                .coverage
                .map(|v| s.mount_section_rest(&v))
                .transpose()?,
            passages: self.passages,
        })
    }
}
impl NormalWaveFamily<'_> {
    pub fn rest(&self) -> Result<NormalWaveFamilyRest, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let rest = NormalWaveFamilyRest {
            origin: self.origin.fibre().rest_source()?,
            anchor: s.detach_section(self.anchor().section, 64)?,
            relation: self.relation.rest()?,
            last: self.last_relation.as_ref().map(|v| v.rest()).transpose()?,
            coverage: self
                .affine_coverage
                .as_ref()
                .map(|v| s.detach_section(v, 64))
                .transpose()?,
            passages: self.passages,
        };
        rest.validate()?;
        Ok(rest)
    }
}
#[cfg(test)]
mod tests;
