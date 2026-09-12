//! Exterior encoding of the executable dependent continuation, using existing native frames.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC_V1: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x01";
const MAGIC_V2: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x02";
const MAGIC_V3: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x03";
const MAGIC: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x04";
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ReturnedHeader {
    prediction: u64,
    cut: ConstitutiveSourceFrame,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyReturnedHeader {
    prediction: u64,
    cut: ConstitutiveProducingCut,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacySourceHeader {
    member: usize,
    chart: WaveSourceReceiver,
    #[serde(default)]
    kind: ConstitutivePassageKind,
    #[serde(default)]
    returned: Option<LegacyReturnedHeader>,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyHeader {
    epoch: u64,
    prediction: u64,
    #[serde(alias = "sources")]
    operations: Vec<LegacySourceHeader>,
    #[serde(default)]
    pending: BTreeMap<u64, ConstitutiveProducingCut>,
    #[serde(default)]
    released: std::collections::BTreeSet<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceHeader {
    member: usize,
    chart: WaveSourceReceiver,
    #[serde(default)]
    kind: ConstitutivePassageKind,
    #[serde(default)]
    returned: Option<ReturnedHeader>,
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
    return_faces: Vec<Option<ResidentSectionRest>>,
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
        let returned = self
            .header
            .operations
            .iter()
            .any(|op| op.returned.as_ref().is_some_and(|r| r.prediction == id));
        self.header.pending.contains_key(&id)
            || (!returned
                && id != self.header.prediction
                && !self.header.released.contains(&id)
                && self.base.has_coupled_prediction(id))
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.header.prediction
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        if self.header.operations.len() != self.sources.len()
            || self.header.operations.len() != self.return_faces.len()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut base = Vec::new();
        self.base.write(&mut base)?;
        blob(out, &base)?;
        for packet in std::iter::once(Some(&self.observation))
            .chain(std::iter::once(Some(&self.receiver)))
            .chain(
                self.sources
                    .iter()
                    .zip(&self.return_faces)
                    .flat_map(|(source, face)| [source.as_ref(), face.as_ref()]),
            )
            .flatten()
        {
            blob(out, &point_bytes(packet)?)?;
        }
        Ok(())
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC && magic != MAGIC_V3 && magic != MAGIC_V2 && magic != MAGIC_V1 {
            return Err(invalid("dependent continuation magic"));
        }
        let header_bytes = read_blob(&mut input)?;
        let header: Header = if magic == MAGIC {
            serde_json::from_slice(&header_bytes).map_err(invalid)?
        } else {
            let old: LegacyHeader = serde_json::from_slice(&header_bytes).map_err(invalid)?;
            Header {
                epoch: old.epoch,
                prediction: old.prediction,
                operations: old
                    .operations
                    .into_iter()
                    .map(|op| SourceHeader {
                        member: op.member,
                        chart: op.chart,
                        kind: op.kind,
                        returned: op.returned.map(|r| ReturnedHeader {
                            prediction: r.prediction,
                            cut: r.cut.into(),
                        }),
                    })
                    .collect(),
                pending: old.pending,
                released: old.released,
            }
        };
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
        let mut return_faces = Vec::new();
        let mut returned_predictions = std::collections::BTreeSet::new();
        for (operation_index, op) in header.operations.iter().enumerate() {
            if op.kind != ConstitutivePassageKind::Return && op.returned.is_some() {
                return Err(invalid("return metadata on non-return operation"));
            }
            if magic == MAGIC_V1 || magic == MAGIC_V2 {
                if op.kind == ConstitutivePassageKind::Return {
                    return Err(invalid("return operation requires dependent frame v4"));
                }
            }
            if magic == MAGIC_V1 && op.kind != ConstitutivePassageKind::Source {
                return Err(invalid("operation requires dependent frame v2"));
            }
            sources.push(if op.kind == ConstitutivePassageKind::Advance {
                None
            } else {
                Some(read_point(&read_blob(&mut input)?)?)
            });
            if op.kind == ConstitutivePassageKind::Return {
                let returned = op.returned.as_ref().ok_or(ConstitutiveFibreError::Shape)?;
                if !returned_predictions.insert(returned.prediction)
                    || returned.prediction == header.prediction
                {
                    return Err(invalid("dependent return predecessor cut"));
                }
                if op.member != returned.cut.member() || op.chart != returned.cut.chart() {
                    return Err(invalid("dependent return member/chart"));
                }
                if let Some(prefix) = returned.cut.prefix() {
                    if prefix >= operation_index
                        || returned.prediction
                            != base
                                .epoch()
                                .checked_add(2)
                                .and_then(|v| v.checked_add(prefix as u64))
                                .ok_or(ConstitutiveFibreError::Shape)?
                    {
                        return Err(invalid("dependent return predecessor cut"));
                    }
                    let predecessor = header
                        .operations
                        .get(prefix)
                        .ok_or(ConstitutiveFibreError::Shape)?;
                    if predecessor.kind != ConstitutivePassageKind::Advance
                        || predecessor.member != returned.cut.member()
                        || predecessor.chart != returned.cut.chart()
                    {
                        return Err(invalid(
                            "dependent return does not name its actual operation",
                        ));
                    }
                } else if !base.has_coupled_prediction(returned.prediction) {
                    return Err(invalid("dependent base return predecessor"));
                }
                return_faces.push(Some(read_point(&read_blob(&mut input)?)?));
            } else {
                return_faces.push(None);
            }
        }
        for (id, cut) in &header.pending {
            if returned_predictions.contains(id) {
                return Err(invalid("returned predecessor remains pending"));
            }
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
        if header.released.iter().any(|id| {
            *id == header.prediction
                || returned_predictions.contains(id)
                || !base.has_coupled_prediction(*id)
        }) {
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
            return_faces,
        })
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, ConstitutiveFibreError> {
        let CoupledConstitutiveRest {
            header,
            base: base_rest,
            observation: observation_rest,
            receiver: receiver_rest,
            sources,
            return_faces,
        } = self;
        let base_epoch = base_rest.epoch();
        let base = base_rest.remount_coupled(s, |_| {})?;
        let handle = base.pending_coupled_prediction(header.prediction)?;
        let observation = s.mount_section_rest(&observation_rest)?;
        let comparison = base.compare_coupled_prediction(
            &handle,
            ResidentConstitutiveCurrent::rational(&observation)?,
        )?;
        let receiver = s.mount_section_rest(&receiver_rest)?;
        let mut model = base
            .into_constitutive_continuation(comparison, receiver)
            .map_err(|r| r.reason)?;
        let operation_count = header.operations.len();
        let operation_metadata = header.operations.clone();
        for (index, ((meta, source), return_face)) in header
            .operations
            .into_iter()
            .zip(sources)
            .zip(return_faces)
            .enumerate()
        {
            let operation_id = base_epoch
                .checked_add(2)
                .and_then(|v| v.checked_add(index as u64))
                .ok_or(ConstitutiveFibreError::Shape)?;
            let retain = header.pending.contains_key(&operation_id)
                || operation_metadata.iter().skip(index + 1).any(|later| {
                    later.returned.as_ref().and_then(|r| r.cut.prefix()) == Some(index)
                });
            let source = source
                .map(|v| {
                    s.mount_section_rest(&v)
                        .map_err(ConstitutiveFibreError::from)
                })
                .transpose()?;
            let returned = meta
                .returned
                .map(|r| {
                    let receiver = return_face
                        .ok_or(ConstitutiveFibreError::Shape)
                        .and_then(|v| {
                            s.mount_section_rest(&v)
                                .map_err(ConstitutiveFibreError::from)
                        });
                    receiver.map(|receiver| ConstitutiveReturnedSource {
                        prediction: r.prediction,
                        cut: r.cut,
                        receiver,
                    })
                })
                .transpose()?;
            model
                .append_operation(
                    ConstitutiveSourcePassage {
                        member: meta.member,
                        chart: meta.chart,
                        kind: meta.kind,
                        source,
                        returned,
                    },
                    retain,
                )
                .map_err(|(_, e)| e)?;
        }
        for id in header.released {
            model.release_prediction(id)?;
        }
        if model.pending != header.pending {
            return Err(invalid("dependent pending operations"));
        }
        if model.epoch() != header.epoch || operation_count != model.operations.len() {
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
                        returned: v.returned.as_ref().map(|r| ReturnedHeader {
                            prediction: r.prediction,
                            cut: r.cut.clone(),
                        }),
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
            return_faces: self
                .operations
                .iter()
                .map(|v| {
                    v.returned
                        .as_ref()
                        .map(|r| {
                            s.detach_section(&r.receiver, 64)
                                .map_err(ConstitutiveFibreError::from)
                        })
                        .transpose()
                })
                .collect::<Result<_, ConstitutiveFibreError>>()?,
        })
    }
}
