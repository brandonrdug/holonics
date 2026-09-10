use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-NORMAL-WAVE\x01";

/// A generator, its exact rational initial conditions and the word to decode. Numerical
/// powers/current faces are caches, not the semantic source of this rest.
#[derive(Debug, PartialEq, Eq)]
pub struct NormalWaveRest {
    material: NormalMaterialRest,
    seed: ResidentSectionRest,
    steps: u64,
}
impl NormalWaveRest {
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn material(&self) -> &NormalMaterialRest {
        &self.material
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        out.write_all(MAGIC).map_err(invalid)?;
        out.write_all(&self.steps.to_le_bytes()).map_err(invalid)?;
        let mut material = Vec::new();
        self.material.write(&mut material)?;
        blob(out, &material)?;
        blob(out, &point_bytes(&self.seed)?)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let mut bytes = [0; 8];
        input.read_exact(&mut bytes).map_err(invalid)?;
        let steps = u64::from_le_bytes(bytes);
        let m = read_blob(&mut input)?;
        let material = NormalMaterialRest::read(&mut m.as_slice(), m.len() as u64)?;
        let seed = read_point(&read_blob(&mut input)?)?;
        let width = 2 * material.roots() + 1;
        if material.roots() != material.targets() || input.limit() != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        point_section(&seed, 2, width)?;
        if [seed.intervals[width - 1].0, seed.intervals[2 * width - 1].0]
            .iter()
            .any(|d| *d <= 0)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            material,
            seed,
            steps,
        })
    }
    /// Recompute the bounded generator word from its definition, never from source records.
    /// Decoder work is explicit and proportional to the stored word; a callback observes
    /// progress but cannot replace its operation, coordinates or precision.
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
        mut progress: impl FnMut(u64),
    ) -> Result<ResidentNormalWave<'c>, ConstitutiveFibreError> {
        let initial = surface.mount_section_rest(&self.seed)?;
        let view = ResidentConstitutiveSection::rationals(&initial)?;
        let material = self.material.remount(surface)?;
        let mut body = material
            .into_difference_wave(view.row(0)?, view.row(1)?)
            .map_err(|r| r.reason)?;
        drop(initial);
        while body.steps() < self.steps {
            body.advance()?;
            progress(body.steps());
        }
        Ok(body)
    }
}
impl ResidentNormalWave<'_> {
    pub fn rest(&self) -> Result<NormalWaveRest, ConstitutiveFibreError> {
        Ok(NormalWaveRest {
            material: self.material.rest()?,
            seed: self
                .material
                .surface
                .detach_section(&self.seed, i64::BITS)?,
            steps: self.steps,
        })
    }
}
