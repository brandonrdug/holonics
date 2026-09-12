//! Exterior encoding of the executable dependent continuation, using existing native frames.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x01";
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceHeader {
    member: usize,
    chart: WaveSourceReceiver,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    prediction: u64,
    sources: Vec<SourceHeader>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct CoupledConstitutiveRest {
    header: Header,
    base: NormalWaveRest,
    observation: ResidentSectionRest,
    receiver: ResidentSectionRest,
    sources: Vec<ResidentSectionRest>,
}
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl CoupledConstitutiveRest {
    pub fn epoch(&self) -> u64 {
        self.header.epoch
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.header.prediction
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        if self.header.sources.len() != self.sources.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut base = Vec::new();
        self.base.write(&mut base)?;
        blob(out, &base)?;
        for packet in std::iter::once(&self.observation)
            .chain(std::iter::once(&self.receiver))
            .chain(self.sources.iter())
        {
            blob(out, &point_bytes(packet)?)?;
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let bytes = read_blob(&mut input)?;
        let base = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if !base.has_coupled_prediction(header.prediction)
            || header.sources.len() as u64 > input.limit() / 8
            || base
                .epoch()
                .checked_add(1)
                .and_then(|v| v.checked_add(header.sources.len() as u64))
                != Some(header.epoch)
        {
            return Err(invalid(
                "dependent continuation chronology or producing cut",
            ));
        }
        let observation = read_point(&read_blob(&mut input)?)?;
        let receiver = read_point(&read_blob(&mut input)?)?;
        let mut sources = Vec::new();
        for _ in &header.sources {
            sources.push(read_point(&read_blob(&mut input)?)?);
        }
        if input.limit() != 0 {
            return Err(invalid("trailing dependent continuation"));
        }
        Ok(Self {
            header,
            base,
            observation,
            receiver,
            sources,
        })
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, ConstitutiveFibreError> {
        let base = self.base.remount_coupled(s, |_| {})?;
        let handle = base.pending_coupled_prediction(self.header.prediction)?;
        let observation = s.mount_section_rest(&self.observation)?;
        let comparison = base.compare_coupled_prediction(
            &handle,
            ResidentConstitutiveCurrent::rational(&observation)?,
        )?;
        let receiver = s.mount_section_rest(&self.receiver)?;
        let mut model = base
            .into_constitutive_continuation(comparison, receiver)
            .map_err(|r| r.reason)?;
        for (meta, source) in self.header.sources.into_iter().zip(self.sources) {
            model
                .actuate_source(meta.member, meta.chart, s.mount_section_rest(&source)?)
                .map_err(|r| r.reason)?;
        }
        if model.epoch() != self.header.epoch {
            return Err(invalid("dependent successor clock"));
        }
        Ok(model)
    }
}
impl<'c> ResidentCoupledConstitutive<'c> {
    pub fn rest(&self) -> Result<CoupledConstitutiveRest, ConstitutiveFibreError> {
        let s = self.base.material.surface;
        let observation = self.comparison.observed();
        Ok(CoupledConstitutiveRest {
            header: Header {
                epoch: self.epoch,
                prediction: self.consumed_prediction(),
                sources: self
                    .sources
                    .iter()
                    .map(|v| SourceHeader {
                        member: v.member,
                        chart: v.chart,
                    })
                    .collect(),
            },
            base: self.base.rest()?,
            observation: s.detach_section(observation.section, 64)?,
            receiver: s.detach_section(&self.receiver, 64)?,
            sources: self
                .sources
                .iter()
                .map(|v| s.detach_section(&v.source, 64).map_err(Into::into))
                .collect::<Result<_, ConstitutiveFibreError>>()?,
        })
    }
}
