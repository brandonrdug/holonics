use super::*;

impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// Add two same-shape enclosures on the same resident surface. Radii are added in the
    /// wide carrier and every source error or overflow is returned as an obstruction.
    pub fn sum_same_shape(
        self,
        other: Self,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        if self.width == 0
            || self.width % 2 != 0
            || self.grain != other.grain
            || other.width != self.width
            || !std::ptr::eq(self.surface, other.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = self
            .width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.surface.fresh_section(1, words, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_normal_enclosure_sum(&lane, self, other, &section)?;
        }
        passage.close(0, &section, 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "enclosure sum: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width: self.width,
            grain: self.grain,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use num_bigint::BigInt;
    use relational_geometry::Rat;

    fn words(values: &[i128]) -> Vec<(i64, i64)> {
        values
            .iter()
            .flat_map(|value| {
                let bytes = value.to_le_bytes();
                [
                    i64::from_le_bytes(bytes[..8].try_into().unwrap()),
                    i64::from_le_bytes(bytes[8..].try_into().unwrap()),
                ]
            })
            .map(|word| (word, word))
            .collect()
    }

    #[test]
    #[ignore = "requires CUDA; the enclosure sum is a resident GPU operation"]
    fn sum_same_shape_adds_nonzero_radius_without_host_readout() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(8);
        let scale = 1i128 << grain.0;
        let left = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    6,
                    ResidentGrain(0),
                    i64::BITS,
                    words(&[scale, -2 * scale, scale]),
                )
                .unwrap(),
            )
            .unwrap();
        let right = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    6,
                    ResidentGrain(0),
                    i64::BITS,
                    words(&[2 * scale, scale, 2 * scale]),
                )
                .unwrap(),
            )
            .unwrap();
        let left = ResidentNormalEnclosureView {
            surface: &surface,
            section: &left,
            offset: 0,
            width: 2,
            grain,
        };
        let right = ResidentNormalEnclosureView {
            surface: &surface,
            section: &right,
            offset: 0,
            width: 2,
            grain,
        };
        let reads = surface.census().section_read_outs;
        let result = left.sum_same_shape(right).unwrap();
        assert_eq!(surface.census().section_read_outs, reads);
        let ball = result.inspect().unwrap();
        assert_eq!(ball.radius, Rat::from_integer(BigInt::from(3)));
        assert_eq!(ball.center.len(), 1);
        assert_eq!(ball.center[0].real, Rat::from_integer(BigInt::from(3)));
        assert_eq!(ball.center[0].imaginary, Rat::from_integer(BigInt::from(-1)));
    }

    #[test]
    #[ignore = "requires CUDA; shape refusals are checked before resident launch"]
    fn sum_same_shape_refuses_mismatched_width_and_grain() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    10,
                    ResidentGrain(0),
                    i64::BITS,
                    words(&[0, 0, 0, 0, 1]),
                )
                .unwrap(),
            )
            .unwrap();
        let a = ResidentNormalEnclosureView {
            surface: &surface,
            section: &section,
            offset: 0,
            width: 2,
            grain: ResidentGrain(8),
        };
        let b = ResidentNormalEnclosureView {
            surface: &surface,
            section: &section,
            offset: 0,
            width: 4,
            grain: ResidentGrain(8),
        };
        assert!(a.sum_same_shape(b).is_err());
        let c = ResidentNormalEnclosureView {
            grain: ResidentGrain(9),
            ..a
        };
        assert!(a.sum_same_shape(c).is_err());
    }
}
