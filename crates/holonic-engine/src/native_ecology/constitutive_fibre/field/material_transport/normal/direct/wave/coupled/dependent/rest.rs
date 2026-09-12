//! Exterior encoding of the executable dependent continuation, using existing native frames.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC_V1: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x01";
const MAGIC: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x02";
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceHeader {
    member: usize,
    chart: WaveSourceReceiver,
    #[serde(default)]
    kind: ConstitutivePassageKind,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    prediction: u64,
    #[serde(alias = "sources")]
    operations: Vec<SourceHeader>,
    #[serde(default)]
    pending: BTreeMap<u64, ConstitutiveProducingCut>,
    #[serde(default)]
    released: std::collections::BTreeSet<u64>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct CoupledConstitutiveRest {
    header: Header,
    base: NormalWaveRest,
    observation: ResidentSectionRest,
    receiver: ResidentSectionRest,
    sources: Vec<Option<ResidentSectionRest>>,
}
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl CoupledConstitutiveRest {
    pub fn epoch(&self) -> u64 {
        self.header.epoch
    }
    pub fn roots(&self) -> usize {
        self.base.material().roots()
    }
    pub fn members(&self) -> usize {
        self.base.coupled_members().unwrap_or(0)
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        self.header.pending.contains_key(&id)
            || (id != self.header.prediction
                && !self.header.released.contains(&id)
                && self.base.has_coupled_prediction(id))
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.header.prediction
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        if self.header.operations.len() != self.sources.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut base = Vec::new();
        self.base.write(&mut base)?;
        blob(out, &base)?;
        for packet in std::iter::once(&self.observation)
            .chain(std::iter::once(&self.receiver))
            .chain(self.sources.iter().filter_map(Option::as_ref))
        {
            blob(out, &point_bytes(packet)?)?;
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC && magic != MAGIC_V1 {
            return Err(invalid("dependent continuation magic"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        if magic == MAGIC_V1 && (!header.pending.is_empty() || !header.released.is_empty()) {
            return Err(invalid("pending disposition requires dependent frame v2"));
        }
        let bytes = read_blob(&mut input)?;
        let base = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if !base.has_coupled_prediction(header.prediction)
            || header
                .operations
                .iter()
                .filter(|op| op.kind != ConstitutivePassageKind::Advance)
                .count() as u64
                > input.limit() / 8
            || base
                .epoch()
                .checked_add(1)
                .and_then(|v| v.checked_add(header.operations.len() as u64))
                != Some(header.epoch)
        {
            return Err(invalid(
                "dependent continuation chronology or producing cut",
            ));
        }
        let observation = read_point(&read_blob(&mut input)?)?;
        let receiver = read_point(&read_blob(&mut input)?)?;
        let mut sources = Vec::new();
        for op in &header.operations {
            if magic == MAGIC_V1 && op.kind != ConstitutivePassageKind::Source {
                return Err(invalid("operation requires dependent frame v2"));
            }
            sources.push(if op.kind == ConstitutivePassageKind::Advance {
                None
            } else {
                Some(read_point(&read_blob(&mut input)?)?)
            });
        }
        for (id, cut) in &header.pending {
            let op = header
                .operations
                .get(cut.prefix)
                .ok_or(ConstitutiveFibreError::Shape)?;
            if op.kind != ConstitutivePassageKind::Advance
                || op.member != cut.member
                || op.chart != cut.chart
                || base
                    .epoch()
                    .checked_add(2)
                    .and_then(|v| v.checked_add(cut.prefix as u64))
                    != Some(*id)
            {
                return Err(invalid(
                    "dependent producing cut does not name its actual operation",
                ));
            }
        }
        if header
            .released
            .iter()
            .any(|id| *id == header.prediction || !base.has_coupled_prediction(*id))
        {
            return Err(invalid("released dependent predecessor cut"));
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
        for (meta, source) in self.header.operations.into_iter().zip(self.sources) {
            let source = source
                .map(|v| {
                    s.mount_section_rest(&v)
                        .map_err(ConstitutiveFibreError::from)
                })
                .transpose()?;
            let retain = self.header.pending.contains_key(&(model.epoch() + 1));
            model
                .append_operation(
                    ConstitutiveSourcePassage {
                        member: meta.member,
                        chart: meta.chart,
                        kind: meta.kind,
                        source,
                    },
                    retain,
                )
                .map_err(|(_, e)| e)?;
        }
        for id in self.header.released {
            model.release_prediction(id)?;
        }
        if model.pending != self.header.pending {
            return Err(invalid("dependent pending operations"));
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
                operations: self
                    .operations
                    .iter()
                    .map(|v| SourceHeader {
                        member: v.member,
                        chart: v.chart,
                        kind: v.kind,
                    })
                    .collect(),
                pending: self.pending.clone(),
                released: self.released.clone(),
            },
            base: self.base.rest()?,
            observation: s.detach_section(observation.section, 64)?,
            receiver: s.detach_section(&self.receiver, 64)?,
            sources: self
                .operations
                .iter()
                .map(|v| {
                    v.source
                        .as_ref()
                        .map(|p| {
                            s.detach_section(p, 64)
                                .map_err(ConstitutiveFibreError::from)
                        })
                        .transpose()
                })
                .collect::<Result<_, ConstitutiveFibreError>>()?,
        })
    }
}
