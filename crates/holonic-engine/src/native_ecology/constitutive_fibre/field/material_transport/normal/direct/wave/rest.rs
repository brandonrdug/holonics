use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_bytes, point_section, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC: &[u8] = b"HOLONIC-NORMAL-WAVE";

/// A generator, its typed seed and word. After reception the seed retains an enclosed
/// previous current and exact received point. Powers and emitted faces remain caches.
#[derive(Debug, PartialEq, Eq)]
pub struct NormalWaveRest {
    material: NormalMaterialRest,
    seed: ResidentSectionRest,
    steps: u64,
    epoch: u64,
    seed_kind: NormalWaveSeedKind,
}
impl NormalWaveRest {
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn material(&self) -> &NormalMaterialRest {
        &self.material
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn seed_kind(&self) -> NormalWaveSeedKind {
        self.seed_kind
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        out.write_all(MAGIC).map_err(invalid)?;
        let version = match self.seed_kind {
            NormalWaveSeedKind::ExactPair => 1,
            NormalWaveSeedKind::ReceivedCurrent => 2,
            NormalWaveSeedKind::JointEnclosure => 3,
        };
        out.write_all(&[version]).map_err(invalid)?;
        out.write_all(&self.steps.to_le_bytes()).map_err(invalid)?;
        if version >= 2 {
            out.write_all(&self.epoch.to_le_bytes()).map_err(invalid)?;
        }
        let mut material = Vec::new();
        self.material.write(&mut material)?;
        blob(out, &material)?;
        blob(out, &point_bytes(&self.seed)?)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let mut version = [0];
        input.read_exact(&mut version).map_err(invalid)?;
        if !(1..=3).contains(&version[0]) {
            return Err(invalid("normal wave version"));
        }
        let mut bytes = [0; 8];
        input.read_exact(&mut bytes).map_err(invalid)?;
        let steps = u64::from_le_bytes(bytes);
        let (epoch, seed_kind) = if version[0] == 1 {
            (steps, NormalWaveSeedKind::ExactPair)
        } else {
            input.read_exact(&mut bytes).map_err(invalid)?;
            let epoch = u64::from_le_bytes(bytes);
            if epoch < steps || (version[0] == 2 && epoch == steps) {
                return Err(invalid("received wave chronology"));
            }
            (
                epoch,
                if version[0] == 2 {
                    NormalWaveSeedKind::ReceivedCurrent
                } else {
                    NormalWaveSeedKind::JointEnclosure
                },
            )
        };
        let m = read_blob(&mut input)?;
        let material = NormalMaterialRest::read(&mut m.as_slice(), m.len() as u64)?;
        let seed = read_point(&read_blob(&mut input)?)?;
        let width = 2 * material.roots() + 1;
        if material.roots() != material.targets() || input.limit() != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        match seed_kind {
            NormalWaveSeedKind::ExactPair => {
                point_section(&seed, 2, width)?;
                if seed.intervals[width - 1].0 <= 0 || seed.intervals[2 * width - 1].0 <= 0 {
                    return Err(invalid("wave point denominator"));
                }
            }
            NormalWaveSeedKind::ReceivedCurrent => {
                point_section(&seed, 3, width)?;
                if wides(&seed.intervals[..2 * width])?[width - 1] < 0
                    || seed.intervals[3 * width - 1].0 <= 0
                {
                    return Err(invalid("wave enclosed seed"));
                }
            }
            NormalWaveSeedKind::JointEnclosure => {
                let components = 4 * material.roots();
                point_section(&seed, 1, 2 * (components + 1))?;
                if wides(&seed.intervals)?[components] < 0 {
                    return Err(invalid("negative joint seed radius"));
                }
            }
        }
        Ok(Self {
            material,
            seed,
            steps,
            epoch,
            seed_kind,
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
        let material = self.material.remount(surface)?;
        let base = self.epoch - self.steps;
        let mut body = if self.seed_kind == NormalWaveSeedKind::JointEnclosure {
            material
                .into_joint_wave(Rc::new(initial), base)
                .map_err(|r| r.reason)?
        } else {
            let view = ResidentConstitutiveSection::rationals(&initial)?;
            let (previous, current) = match self.seed_kind {
                NormalWaveSeedKind::ExactPair => (view.row(0)?.into(), view.row(1)?),
                NormalWaveSeedKind::ReceivedCurrent => (
                    ResidentNormalInput::Enclosed(ResidentNormalEnclosureView {
                        surface,
                        section: &initial,
                        offset: 0,
                        width: 2 * material.roots,
                        grain: material.grain,
                    }),
                    view.row(2)?,
                ),
                NormalWaveSeedKind::JointEnclosure => unreachable!("handled enclosed joint"),
            };
            let mut body = material
                .into_difference_wave_source(previous, current)
                .map_err(|r| r.reason)?;
            body.epoch = base;
            Rc::get_mut(&mut body.current.inner)
                .expect("unpublished decoded current")
                .at = Some(base);
            Rc::get_mut(&mut body.previous.inner)
                .expect("unpublished decoded previous")
                .at = base.checked_sub(1);
            drop(initial);
            body
        };
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
            epoch: self.epoch,
            seed_kind: self.seed_kind,
        })
    }
}
