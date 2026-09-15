use super::*;
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HOLONIC-NORMAL-HELD-SECTION\x01";

/// A receiver declaration that retains selected complex coordinates from a given source and
/// receives the remaining coordinates from a generated section. The mask is receiver data and
/// never becomes a native current or a training target.
pub struct ResidentHeldSection<'c> {
    given: ResidentNormalEnclosure<'c>,
    held: Vec<bool>,
    mask: ResidentSection<'c>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentHeldSectionRest {
    grain: ResidentGrain,
    given: ResidentSectionRest,
    held: Vec<bool>,
}

impl<'c> ResidentHeldSection<'c> {
    pub fn found(
        given: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
    ) -> Result<Self, ConstitutiveFibreError> {
        if given.width == 0 || given.width % 2 != 0 || held.len() != given.width / 2 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let given = given.to_owned()?;
        let held = held.to_vec();
        let mask = mount_mask(given.surface, &held)?;
        Ok(Self { given, held, mask })
    }

    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        rest: ResidentHeldSectionRest,
    ) -> Result<Self, ConstitutiveFibreError> {
        let held = rest.held;
        let grain = rest.grain;
        let given = ResidentNormalEnclosure::remount(surface, rest.given, grain)?;
        if given.width == 0 || held.len() != given.width / 2 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mask = mount_mask(surface, &held)?;
        Ok(Self { given, held, mask })
    }

    pub fn receive(
        &self,
        generated: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        if !std::ptr::eq(generated.surface, self.given.surface)
            || generated.width != self.given.width
            || generated.grain != self.given.grain
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let out =
            self.given
                .surface
                .fresh_section(1, 2 * (self.given.width + 1), ResidentGrain(0))?;
        let aliased = std::ptr::eq(generated.section, &self.given.section) && generated.offset == 0;
        let mut passage = self.given.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.given.surface.record_normal_held_section(
                &lane,
                self.given.view(),
                generated,
                &self.mask,
                aliased,
                &out,
            )?;
        }
        passage.close(0, &out, 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal held section: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.given.surface,
            section: out,
            width: self.given.width,
            grain: self.given.grain,
        })
    }

    pub fn given(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.given.view()
    }

    pub fn held(&self) -> &[bool] {
        &self.held
    }

    pub fn all_held(&self) -> bool {
        self.held.iter().all(|v| *v)
    }

    pub(crate) fn mask(&self) -> &ResidentSection<'c> {
        &self.mask
    }

    pub fn rest(&self) -> Result<ResidentHeldSectionRest, ConstitutiveFibreError> {
        Ok(ResidentHeldSectionRest {
            grain: self.given.grain,
            given: self.given.rest()?,
            held: self.held.clone(),
        })
    }
}

fn mount_mask<'c>(
    surface: &'c ResidentSurface<'c>,
    held: &[bool],
) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
    let words = held
        .iter()
        .map(|v| {
            let word = i64::from(*v);
            (word, word)
        })
        .collect();
    let rest = ResidentSectionRest::found(1, held.len(), ResidentGrain(0), 64, words)
        .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
    Ok(surface.mount_section_rest(&rest)?)
}

impl ResidentHeldSectionRest {
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        let given = self
            .given
            .canonical_bytes()
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        out.write_all(MAGIC)
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        out.write_all(&self.grain.0.to_le_bytes())
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        out.write_all(&(given.len() as u64).to_le_bytes())
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        out.write_all(&given)
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        out.write_all(&(self.held.len() as u64).to_le_bytes())
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        for value in &self.held {
            out.write_all(&[u8::from(*value)])
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        }
        Ok(())
    }

    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input
            .read_exact(&mut magic)
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        if magic != MAGIC {
            return Err(ConstitutiveFibreError::Rest(
                "normal held section magic is absent".into(),
            ));
        }
        fn read_u64(input: &mut impl Read) -> Result<u64, ConstitutiveFibreError> {
            let mut bytes = [0; 8];
            input
                .read_exact(&mut bytes)
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
            Ok(u64::from_le_bytes(bytes))
        }
        let mut grain = [0; 4];
        input
            .read_exact(&mut grain)
            .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
        let grain = ResidentGrain(u32::from_le_bytes(grain));
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let given_len = usize::try_from(read_u64(&mut input)?)
            .map_err(|_| ConstitutiveFibreError::Rest("normal held given extent".into()))?;
        if given_len as u64 > input.limit() {
            return Err(ConstitutiveFibreError::Rest(
                "truncated normal held given".into(),
            ));
        }
        let mut given_bytes = vec![0; given_len];
        input
            .read_exact(&mut given_bytes)
            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
        let given =
            ResidentSectionRest::read(&given_bytes).map_err(ConstitutiveFibreError::Arithmetic)?;
        let held_len = usize::try_from(read_u64(&mut input)?)
            .map_err(|_| ConstitutiveFibreError::Rest("normal held mask extent".into()))?;
        if held_len as u64 > input.limit() {
            return Err(ConstitutiveFibreError::Rest(
                "truncated normal held mask".into(),
            ));
        }
        let mut held = Vec::with_capacity(held_len);
        for _ in 0..held_len {
            let mut byte = [0];
            input
                .read_exact(&mut byte)
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?;
            match byte[0] {
                0 => held.push(false),
                1 => held.push(true),
                _ => {
                    return Err(ConstitutiveFibreError::Rest(
                        "normal held mask value".into(),
                    ))
                }
            }
        }
        if input.limit() != 0 {
            return Err(ConstitutiveFibreError::Rest(
                "trailing normal held section bytes".into(),
            ));
        }
        if given.rows != 1
            || given.width < 6
            || given.width % 2 != 0
            || given.width % 4 != 2
            || held.len() != (given.width - 2) / 4
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self { grain, given, held })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    fn words(values: &[i128]) -> Vec<(i64, i64)> {
        values
            .iter()
            .flat_map(|v| {
                let bytes = v.to_le_bytes();
                [
                    i64::from_le_bytes(bytes[..8].try_into().unwrap()),
                    i64::from_le_bytes(bytes[8..].try_into().unwrap()),
                ]
            })
            .map(|v| (v, v))
            .collect()
    }

    #[test]
    #[ignore = "requires CUDA; malformed receiver shape is refused"]
    fn malformed_mask_shape_is_refused_before_mount() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, 10, ResidentGrain(0), 64, words(&[1, 2, 3, 4, 0]))
                    .unwrap(),
            )
            .unwrap();
        let given = ResidentNormalEnclosureView {
            surface: &surface,
            section: &section,
            offset: 0,
            width: 4,
            grain: ResidentGrain(32),
        };
        assert!(ResidentHeldSection::found(given, &[true]).is_err());
    }

    #[test]
    #[ignore = "requires CUDA; held receiver preserves exact known coordinates and only free uncertainty"]
    fn mixed_held_receiver_keeps_given_and_generated_faces() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(32);
        let scale = 1i128 << grain.0;
        let given_section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    10,
                    ResidentGrain(0),
                    64,
                    words(&[0, 0, 3 * scale, 4 * scale, 2 * scale]),
                )
                .unwrap(),
            )
            .unwrap();
        let generated_section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    10,
                    ResidentGrain(0),
                    64,
                    words(&[10 * scale, 20 * scale, 30 * scale, 40 * scale, 5 * scale]),
                )
                .unwrap(),
            )
            .unwrap();
        let given = ResidentNormalEnclosureView {
            surface: &surface,
            section: &given_section,
            offset: 0,
            width: 4,
            grain,
        };
        let generated = ResidentNormalEnclosureView {
            surface: &surface,
            section: &generated_section,
            offset: 0,
            width: 4,
            grain,
        };
        let held = ResidentHeldSection::found(given, &[true, false]).unwrap();
        let received = held.receive(generated).unwrap().inspect().unwrap();
        assert_eq!(received.center[0].real, Rat::new(0.into(), 1.into()));
        assert_eq!(received.center[1].real, Rat::new(30.into(), 1.into()));
        assert_eq!(received.radius, Rat::new(7.into(), 1.into()));
        assert_eq!(
            held.receive(held.given())
                .unwrap()
                .inspect()
                .unwrap()
                .radius,
            Rat::new(2.into(), 1.into())
        );
        let free = ResidentHeldSection::found(given, &[false, false]).unwrap();
        assert_eq!(
            free.receive(generated).unwrap().inspect().unwrap().center[0].real,
            Rat::new(10.into(), 1.into())
        );
        let rest = held.rest().unwrap();
        let mut bytes = Vec::new();
        rest.write(&mut bytes).unwrap();
        let restored =
            ResidentHeldSectionRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
        assert_eq!(restored.held, vec![true, false]);
        let remounted = ResidentHeldSection::remount(&surface, restored).unwrap();
        assert_eq!(remounted.held(), &[true, false]);
        assert_eq!(
            remounted.receive(generated).unwrap().inspect().unwrap(),
            received
        );
    }
}
