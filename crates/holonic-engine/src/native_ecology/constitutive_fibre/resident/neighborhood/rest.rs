use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, expect, read_blob};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-GENERATOR-NEIGHBORHOOD\x01";
const MAGIC_V2: &[u8] = b"HOLONIC-GENERATOR-NEIGHBORHOOD\x02";
const END: &[u8] = b"HOLONIC-GENERATOR-NEIGHBORHOOD-END\x01";
#[derive(Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    members: usize,
    epoch: u64,
    evidence: Option<EvidenceHeader>,
}
#[derive(Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct HeaderV2 {
    members: usize,
    epoch: u64,
    predictive: Vec<bool>,
    evidence: Option<EvidenceHeader>,
}
#[derive(Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct EvidenceHeader {
    member: usize,
    epoch: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct GeneratorNeighborhoodRest {
    laws: Vec<ConstitutiveFibreRest>,
    predictive: Vec<Option<NormalMaterialRest>>,
    condition: ConditionCurrentRest,
    epoch: u64,
    evidence: Option<NeighborhoodEvidenceRest>,
}
#[derive(Debug, PartialEq, Eq)]
pub struct NeighborhoodEvidenceRest {
    pub member: usize,
    pub epoch: u64,
    pub family: ConditionPreimageRest,
}
impl GeneratorNeighborhoodRest {
    pub fn members(&self) -> usize {
        self.laws.len()
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn laws(&self) -> &[ConstitutiveFibreRest] {
        &self.laws
    }
    /// Metadata of the action actually used for transport. A normal action is constructed
    /// from its real source-axis rows; that count is distinct from empirical observations
    /// and from formation occurrences in the compatibility relation.
    pub(crate) fn action_cut(&self, member: usize) -> Result<u64, ConstitutiveFibreError> {
        match self.predictive_material(member)? {
            Some(material) => match material.source_chart() {
                NormalSourceChart::Features {source_complex} => source_complex.checked_mul(2)
                    .and_then(|v|u64::try_from(v).ok()).ok_or(ConstitutiveFibreError::Shape),
                _ => Err(ConstitutiveFibreError::Shape),
            },
            None => self.laws.get(member).map(|v|v.occurrences()).ok_or(ConstitutiveFibreError::Shape),
        }
    }
    pub fn predictive_material(
        &self,
        member: usize,
    ) -> Result<Option<&NormalMaterialRest>, ConstitutiveFibreError> {
        self.predictive
            .get(member)
            .map(Option::as_ref)
            .ok_or(ConstitutiveFibreError::Shape)
    }
    pub fn condition(&self) -> &ConditionCurrentRest {
        &self.condition
    }
    pub fn last_received_evidence(&self) -> Option<&NeighborhoodEvidenceRest> {
        self.evidence.as_ref()
    }
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        self.condition.validate()?;
        if self.laws.is_empty() || self.condition.contacts() > self.epoch {
            return Err(ConstitutiveFibreError::Shape);
        }
        let chart = self.condition.source_chart();
        if !matches!(chart, ConstitutiveSourceChart::BilinearContact { .. }) {
            return Err(ConstitutiveFibreError::Shape);
        }
        for law in &self.laws {
            law.validate()?;
            if law.source_chart() != chart {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        if self.predictive.len() != self.laws.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        for (law, predictive) in self.laws.iter().zip(&self.predictive) {
            let Some(material) = predictive else { continue };
            material.validate()?;
            let ConstitutiveSourceChart::BilinearContact {
                source_complex: ns,
                condition_complex: nc,
            } = chart
            else {
                return Err(ConstitutiveFibreError::Shape);
            };
            let features = ns
                .checked_mul(nc)
                .and_then(|n| n.checked_add(ns))
                .and_then(|n| n.checked_add(nc))
                .ok_or(ConstitutiveFibreError::Shape)?;
            if material.source_chart()
                != (NormalSourceChart::Features {
                    source_complex: features,
                })
                || law.target_width() % 2 != 0
                || material.targets() != law.target_width() / 2
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        match &self.evidence {
            None if self.condition.contacts() != 0 => return Err(ConstitutiveFibreError::Shape),
            Some(e) => {
                e.family.validate()?;
                let law = self
                    .laws
                    .get(e.member)
                    .ok_or(ConstitutiveFibreError::Shape)?;
                if self.condition.contacts() == 0
                    || e.epoch == 0
                    || e.epoch > self.epoch
                    || e.family.source_chart() != chart
                    || e.family.condition_width() != self.condition.width()
                    || e.family.action_target_width() != law.target_width()
                    || e.family.relation_cut().checked_add(1) != Some(law.occurrences())
                {
                    return Err(ConstitutiveFibreError::Shape);
                }
            }
            None => {}
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        self.validate()?;
        let has_predictive = self.predictive.iter().any(Option::is_some);
        if !has_predictive {
            out.write_all(MAGIC).map_err(error)?;
            blob(out, &serde_json::to_vec(&Header {
                members: self.laws.len(),
                epoch: self.epoch,
                evidence: self.evidence.as_ref().map(|e| EvidenceHeader {
                    member: e.member,
                    epoch: e.epoch,
                }),
            }).map_err(error)?)?;
        } else {
            out.write_all(MAGIC_V2).map_err(error)?;
            blob(out, &serde_json::to_vec(&HeaderV2 {
                members: self.laws.len(),
                epoch: self.epoch,
                predictive: self.predictive.iter().map(Option::is_some).collect(),
                evidence: self.evidence.as_ref().map(|e| EvidenceHeader {
                    member: e.member,
                    epoch: e.epoch,
                }),
            }).map_err(error)?)?;
        }
        let mut bytes = Vec::new();
        self.condition.write(&mut bytes)?;
        blob(out, &bytes)?;
        for law in &self.laws {
            bytes.clear();
            law.write(&mut bytes)?;
            blob(out, &bytes)?;
        }
        if has_predictive {
            for material in &self.predictive {
                if let Some(material) = material {
                    bytes.clear();
                    material.write(&mut bytes)?;
                    blob(out, &bytes)?;
                }
            }
        }
        if let Some(e) = &self.evidence {
            bytes.clear();
            e.family.write(&mut bytes)?;
            blob(out, &bytes)?;
        }
        out.write_all(END).map_err(error)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut wire = Vec::new();
        input.take(octets).read_to_end(&mut wire).map_err(error)?;
        if wire.len() < MAGIC.len() {
            return Err(error("native rest magic or end marker"));
        }
        let v2 = wire.starts_with(MAGIC_V2);
        if v2 && wire.len() < MAGIC_V2.len() {
            return Err(error("native rest magic or end marker"));
        }
        let magic_len = if v2 { MAGIC_V2.len() } else { MAGIC.len() };
        if !v2 && !wire.starts_with(MAGIC) {
            return Err(error("native rest magic or end marker"));
        }
        let cursor = std::io::Cursor::new(&wire[magic_len..]);
        let mut input = cursor.take((wire.len() - magic_len) as u64);
        let (members, epoch, predictive_flags, evidence_header) = if v2 {
            let h: HeaderV2 = serde_json::from_slice(&read_blob(&mut input)?).map_err(error)?;
            if h.predictive.len() != h.members {
                return Err(ConstitutiveFibreError::Shape);
            }
            (h.members, h.epoch, h.predictive, h.evidence)
        } else {
            let h: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(error)?;
            if h.members == 0 || h.members as u64 > input.limit() / 8 {
                return Err(ConstitutiveFibreError::Shape);
            }
            (h.members, h.epoch, vec![false; h.members], h.evidence)
        };
        let condition = ConditionCurrentRest::read(&mut read_blob(&mut input)?.as_slice())?;
        if members == 0 || members as u64 > input.limit() / 8 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut laws = Vec::new();
        laws.try_reserve(members).map_err(error)?;
        for _ in 0..members {
            let bytes = read_blob(&mut input)?;
            laws.push(ConstitutiveFibreRest::read(
                &mut bytes.as_slice(),
                bytes.len() as u64,
            )?);
        }
        let mut predictive = Vec::with_capacity(members);
        for flag in predictive_flags {
            predictive.push(if flag {
                let bytes = read_blob(&mut input)?;
                Some(NormalMaterialRest::read(&mut bytes.as_slice(), bytes.len() as u64)?)
            } else {
                None
            });
        }
        let evidence = match evidence_header {
            Some(e) => {
                let bytes = read_blob(&mut input)?;
                Some(NeighborhoodEvidenceRest {
                    member: e.member,
                    epoch: e.epoch,
                    family: ConditionPreimageRest::read(&mut bytes.as_slice(), bytes.len() as u64)?,
                })
            }
            None => None,
        };
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(error("trailing neighborhood bytes"));
        }
        let result = Self {
            laws,
            predictive,
            condition,
            epoch,
            evidence,
        };
        result.validate()?;
        Ok(result)
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentGeneratorNeighborhood<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let mut laws = Vec::with_capacity(self.laws.len());
        for (law, predictive) in self.laws.into_iter().zip(self.predictive) {
            let law = law.remount(surface)?;
            let predictive = predictive
                .map(|material| {
                    let material = material.remount(surface)?;
                    PredictiveMaterial::new(material, &law)
                })
                .transpose()?;
            laws.push(GeneratorMaterial { law, predictive });
        }
        let condition = self.condition.remount(surface)?;
        let evidence = self
            .evidence
            .map(|e| {
                Ok::<_, ConstitutiveFibreError>(NeighborhoodEvidence {
                    member: e.member,
                    epoch: e.epoch,
                    family: e.family.remount(surface)?,
                })
            })
            .transpose()?;
        Ok(ResidentGeneratorNeighborhood {
            laws,
            condition,
            epoch: self.epoch,
            evidence,
            owner: Rc::new(()),
            usable: true,
        })
    }
}
fn error(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl ResidentGeneratorNeighborhood<'_> {
    pub fn rest(&self) -> Result<GeneratorNeighborhoodRest, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let value = GeneratorNeighborhoodRest {
            laws: self
                .laws
                .iter()
                .map(|material| material.law.rest())
                .collect::<Result<_, _>>()?,
            predictive: self
                .laws
                .iter()
                .map(|material| {
                    material
                        .predictive
                        .as_ref()
                        .map(|p| p.material.rest())
                        .transpose()
                })
                .collect::<Result<_, _>>()?,
            condition: self.condition.rest()?,
            epoch: self.epoch,
            evidence: self
                .evidence
                .as_ref()
                .map(|e| {
                    Ok::<_, ConstitutiveFibreError>(NeighborhoodEvidenceRest {
                        member: e.member,
                        epoch: e.epoch,
                        family: e.family.rest()?,
                    })
                })
                .transpose()?,
        };
        value.validate()?;
        Ok(value)
    }
}
