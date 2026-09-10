use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, expect, read_blob};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-GENERATOR-NEIGHBORHOOD\x01";
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
struct EvidenceHeader {
    member: usize,
    epoch: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct GeneratorNeighborhoodRest {
    laws: Vec<ConstitutiveFibreRest>,
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
        out.write_all(MAGIC).map_err(error)?;
        blob(
            out,
            &serde_json::to_vec(&Header {
                members: self.laws.len(),
                epoch: self.epoch,
                evidence: self.evidence.as_ref().map(|e| EvidenceHeader {
                    member: e.member,
                    epoch: e.epoch,
                }),
            })
            .map_err(error)?,
        )?;
        let mut bytes = Vec::new();
        self.condition.write(&mut bytes)?;
        blob(out, &bytes)?;
        for law in &self.laws {
            bytes.clear();
            law.write(&mut bytes)?;
            blob(out, &bytes)?;
        }
        if let Some(e) = &self.evidence {
            bytes.clear();
            e.family.write(&mut bytes)?;
            blob(out, &bytes)?;
        }
        out.write_all(END).map_err(error)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(error)?;
        let condition = ConditionCurrentRest::read(&mut read_blob(&mut input)?.as_slice())?;
        if header.members == 0 || header.members as u64 > input.limit() / 8 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut laws = Vec::new();
        laws.try_reserve(header.members).map_err(error)?;
        for _ in 0..header.members {
            let bytes = read_blob(&mut input)?;
            laws.push(ConstitutiveFibreRest::read(
                &mut bytes.as_slice(),
                bytes.len() as u64,
            )?);
        }
        let evidence = match header.evidence {
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
            condition,
            epoch: header.epoch,
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
        let laws = self
            .laws
            .into_iter()
            .map(|law| law.remount(surface))
            .collect::<Result<Vec<_>, _>>()?;
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
                .map(ResidentConstitutiveFibre::rest)
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
