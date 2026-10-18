//! Exact operand charts for independently scaled receiving blocks.
//! These charts change coordinates, not the physical source or receiving logits.
//!
//! [definition; agent-inferred, October 17] The founded scale σ is the dyadic cell of the first
//! nonzero arrival's exact mean square: `(Σf²)/len ∈ (σ²/4, σ²]`, computed in exact rationals.
//! This is a partition, not an estimate. Under a dyadic rescaling of the founding arrival it is
//! a gauge: founding at 8 times or 1/4 of the same arrival deposits the same block laws and the
//! same applied output, as checked by
//! `arrival_context_receiving_deposit_is_dyadically_covariant_and_restores`.
use super::*;
use crate::ratio::integer;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceivingLayout {
    Single,
    ArrivalContext { source_width: usize },
}

/// The exact positive power-of-two scale of an admitted receiving operand block.
/// Its physical feature f is represented by f/scale and its map by scale*W.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingOperandChart {
    width: usize,
    scale: Rat,
}

impl ReceivingOperandChart {
    /// Found from one actual nonzero feature, with no target, covector or weight input.
    /// The least power of two sigma whose square covers mean squared coordinate magnitude
    /// gives mean(f/sigma)^2 in (1/4,1]. A zero feature supplies no founding scale.
    pub fn from_feature(feature: &[Rat]) -> Result<Option<Self>, HnnError> {
        if feature.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a receiving operand chart has positive width",
            });
        }
        let power: Rat = feature.iter().map(|x| x * x).sum::<Rat>()
            / Rat::from_integer(BigInt::from(feature.len()));
        if power.is_zero() {
            return Ok(None);
        }
        let mut scale = Rat::one();
        while &scale * &scale < power {
            scale *= integer(2);
        }
        while (&scale * &scale) / integer(4) >= power {
            scale /= integer(2);
        }
        Ok(Some(Self {
            width: feature.len(),
            scale,
        }))
    }
    /// Restore a frozen operand chart. Only positive exact powers of two are admitted.
    pub fn from_parts(width: usize, scale: Rat) -> Result<Self, HnnError> {
        let power_of_two = |value: &BigInt| {
            value.is_positive()
                && value
                    .trailing_zeros()
                    .is_some_and(|zeros| zeros.checked_add(1) == Some(value.bits()))
        };
        if width == 0 || !power_of_two(scale.numer()) || !power_of_two(scale.denom()) {
            return Err(HnnError::Unadmitted {
                reason: "a receiving operand chart has positive width and a power-of-two scale",
            });
        }
        Ok(Self { width, scale })
    }

    pub fn width(&self) -> usize {
        self.width
    }
    pub fn scale(&self) -> &Rat {
        &self.scale
    }
    pub fn feature(&self, physical: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        if physical.len() != self.width {
            return Err(HnnError::Shape {
                what: "a receiving operand chart's physical feature",
                expected: self.width,
                found: physical.len(),
            });
        }
        Ok(physical.iter().map(|x| x / &self.scale).collect())
    }
    pub fn physical_map(&self, charted: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
        if charted.columns() != self.width {
            return Err(HnnError::Shape {
                what: "a receiving operand chart's map",
                expected: self.width,
                found: charted.columns(),
            });
        }
        rate_matrix(&(Rat::one() / &self.scale), charted)
    }
    pub fn charted_map(&self, physical: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
        if physical.columns() != self.width {
            return Err(HnnError::Shape {
                what: "a receiving operand chart's map",
                expected: self.width,
                found: physical.columns(),
            });
        }
        rate_matrix(&self.scale, physical)
    }
    /// Physical ridge corresponding to the internal power-of-two ridge; internal Gram and
    /// carry bounds retain their original units and positivity margin.
    pub fn physical_ridge(&self, internal: &Rat) -> Rat {
        internal * &self.scale * &self.scale
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn receiving_operand_chart_preserves_complex_read_and_full_adjoint() {
        let f = vec![
            Rat::new(1.into(), 128.into()),
            Rat::new((-1).into(), 64.into()),
        ];
        let chart = ReceivingOperandChart::from_feature(&f).unwrap().unwrap();
        assert_eq!(chart.scale(), &Rat::new(1.into(), 64.into()));
        let w = rows_matrix(&[vec![integer(2), integer(3)], vec![integer(-4), integer(1)]]);
        let u = chart.charted_map(&w).unwrap();
        let z = chart.feature(&f).unwrap();
        assert_eq!(u.apply(&z).unwrap(), w.apply(&f).unwrap());
        assert_eq!(chart.physical_map(&u).unwrap(), w);
        let g = vec![integer(5), integer(-7)];
        let internal = u.transpose().unwrap().apply(&g).unwrap();
        let physical: Vec<Rat> = internal.iter().map(|x| x / chart.scale()).collect();
        assert_eq!(physical, w.transpose().unwrap().apply(&g).unwrap());
        assert_eq!(
            chart.physical_ridge(&integer(2)),
            Rat::new(1.into(), 2048.into())
        );
    }
    #[test]
    fn receiving_operand_chart_restores_exactly_and_rejects_non_dyadic_unit() {
        let chart = ReceivingOperandChart::from_feature(&[Rat::new(1.into(), 128.into())])
            .unwrap()
            .unwrap();
        let text = format!("{} {}", chart.width(), chart.scale());
        let parts: Vec<&str> = text.split_whitespace().collect();
        let restored =
            ReceivingOperandChart::from_parts(parts[0].parse().unwrap(), parts[1].parse().unwrap())
                .unwrap();
        assert_eq!(chart, restored);
        assert!(ReceivingOperandChart::from_parts(1, Rat::new(3.into(), 8.into())).is_err());
        assert!(ReceivingOperandChart::from_parts(0, Rat::one()).is_err());
        assert!(ReceivingOperandChart::from_parts(1, Rat::zero()).is_err());
    }

    #[test]
    fn receiving_operand_chart_scales_with_operand_and_refuses_zero_founding() {
        let f = vec![integer(1), integer(2), integer(0)];
        let scaled: Vec<Rat> = f.iter().map(|x| x / integer(1024)).collect();
        let a = ReceivingOperandChart::from_feature(&f).unwrap().unwrap();
        let b = ReceivingOperandChart::from_feature(&scaled)
            .unwrap()
            .unwrap();
        assert_eq!(a.feature(&f).unwrap(), b.feature(&scaled).unwrap());
        assert_eq!(b.scale(), &(a.scale() / integer(1024)));
        assert_eq!(
            ReceivingOperandChart::from_feature(&[Rat::zero()]).unwrap(),
            None
        );
    }
}
