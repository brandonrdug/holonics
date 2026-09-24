//! **The current rest of a published constitutive continuation** (frame v7).
//!
//! It retains the contemporary coupled wave, the consumed root address and the two counts.
//! The former v1–v6 programme frames were frozen pre-return cuts and are refused by this reader.

use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, read_blob};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x07";

#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    prediction: u64,
    material_returns: usize,
    source_passages: usize,
}

/// The current rest of a [`ResidentCoupledConstitutive`].
#[derive(Debug, PartialEq, Eq)]
pub struct CoupledConstitutiveRest {
    header: Header,
    wave: NormalWaveRest,
}
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl CoupledConstitutiveRest {
    pub fn epoch(&self) -> u64 {
        self.header.epoch
    }
    fn wave(&self) -> &NormalWaveRest {
        &self.wave
    }
    pub fn roots(&self) -> usize {
        self.wave().material().roots()
    }
    pub fn members(&self) -> usize {
        self.wave().coupled_members().unwrap_or(0)
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        self.wave.has_coupled_prediction(id)
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.header.prediction
    }
    fn validate(header: &Header, wave: &NormalWaveRest) -> Result<(), ConstitutiveFibreError> {
        if !wave.is_coupled()
            || wave.epoch() != header.epoch
            || header.material_returns == 0
            || wave.has_coupled_prediction(header.prediction)
        {
            return Err(invalid("constitutive continuation clock or consumed root"));
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        Self::validate(&self.header, &self.wave)?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut bytes = Vec::new();
        self.wave.write(&mut bytes)?;
        blob(out, &bytes)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC {
            return Err(invalid("dependent continuation magic"));
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let bytes = read_blob(&mut input)?;
        let wave = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if input.limit() != 0 {
            return Err(invalid("trailing constitutive continuation"));
        }
        Self::validate(&header, &wave)?;
        Ok(Self { header, wave })
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, ConstitutiveFibreError> {
        Self::validate(&self.header, &self.wave)?;
        let wave = self.wave.remount_coupled(s, |_| {})?;
        Ok(ResidentCoupledConstitutive {
            wave,
            consumed: self.header.prediction,
            material_returns: self.header.material_returns,
            source_passages: self.header.source_passages,
        })
    }
}
impl<'c> ResidentCoupledConstitutive<'c> {
    pub fn rest(&self) -> Result<CoupledConstitutiveRest, ConstitutiveFibreError> {
        let header = Header {
            epoch: self.epoch(),
            prediction: self.consumed,
            material_returns: self.material_returns,
            source_passages: self.source_passages,
        };
        let wave = self.wave.rest()?;
        CoupledConstitutiveRest::validate(&header, &wave)?;
        Ok(CoupledConstitutiveRest { header, wave })
    }
}

#[cfg(test)]
mod format_tests {
    use super::*;

    #[test]
    fn retired_programme_frames_are_refused() {
        for version in 1u8..=6 {
            let mut bytes = b"HOLONIC-COUPLED-CONSTITUTIVE".to_vec();
            bytes.push(version);
            assert!(
                CoupledConstitutiveRest::read(&mut bytes.as_slice(), bytes.len() as u64).is_err()
            );
        }
    }
}
