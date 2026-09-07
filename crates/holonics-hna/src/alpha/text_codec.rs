//! Exterior octet/end-of-part chart and differential-current presentation. Learned current is
//! supplied by the native junction. This chart supplies no English grammar or response selector.
use super::material::{with_matched_field_profile, AlphaMaterialError};
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldDifferentialReading, NativeFieldJunctionSolver,
    NativePhaseCurrent,
};
use serde::Serialize;

pub const TEXT_BIT_PAIRS: usize = 9;
pub const TEXT_INPUT_CHANNELS: usize = 2 * TEXT_BIT_PAIRS;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "kebab-case")]
pub enum TextSymbol {
    Octet(u8),
    EndPart,
}

impl TextSymbol {
    pub fn codeword(self) -> u16 {
        match self {
            Self::Octet(value) => u16::from(value),
            Self::EndPart => 256,
        }
    }
    pub fn from_codeword(value: u16) -> Option<Self> {
        match value {
            0..=255 => Some(Self::Octet(value as u8)),
            256 => Some(Self::EndPart),
            _ => None,
        }
    }
    /// Exactly nine identical unit impulses: one in each addressed pair. The ninth bit carries
    /// a real application part boundary; it is not a native thought-completion measurement.
    pub fn inputs(self) -> Vec<NativePhaseCurrent> {
        let mut inputs = vec![NativePhaseCurrent::zero(); TEXT_INPUT_CHANNELS];
        for bit in 0..TEXT_BIT_PAIRS {
            inputs[2 * bit + usize::from((self.codeword() >> bit) & 1)] =
                NativePhaseCurrent::unit();
        }
        inputs
    }
    pub fn from_inputs(inputs: &[NativePhaseCurrent]) -> Option<Self> {
        if inputs.len() != TEXT_INPUT_CHANNELS {
            return None;
        }
        let mut codeword = 0u16;
        for (bit, pair) in inputs.chunks_exact(2).enumerate() {
            if pair[0] == NativePhaseCurrent::zero() && pair[1] == NativePhaseCurrent::unit() {
                codeword |= 1 << bit;
            } else if pair[0] != NativePhaseCurrent::unit() || pair[1] != NativePhaseCurrent::zero()
            {
                return None;
            }
        }
        Self::from_codeword(codeword)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum TextCodeDisposition {
    Symbol {
        symbol: TextSymbol,
    },
    Open,
    /// All differential signs were certain, but the codeword is outside the declared chart.
    Reserved {
        codeword: u16,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TextCodeReading {
    pub native: NativeFieldDifferentialReading,
    pub disposition: TextCodeDisposition,
}

pub fn read_text_symbol(
    field: &NativeConstitutiveField<'_>,
    occurrence: usize,
) -> Result<TextCodeReading, AlphaMaterialError> {
    if field.nodes() != TEXT_INPUT_CHANNELS {
        return Err(AlphaMaterialError::Apparatus(
            "text codec requires its declared 18-channel chart".into(),
        ));
    }
    let native = field
        .read_differential_pairs(occurrence, 2 * field.nodes(), TEXT_BIT_PAIRS)?
        .ok_or_else(|| {
            AlphaMaterialError::Apparatus("text codec requires a junction outgoing current".into())
        })?;
    let disposition = if native.unresolved != 0 {
        TextCodeDisposition::Open
    } else {
        let codeword = native.positive as u16;
        match TextSymbol::from_codeword(codeword) {
            Some(symbol) => TextCodeDisposition::Symbol { symbol },
            None => TextCodeDisposition::Reserved { codeword },
        }
    };
    Ok(TextCodeReading {
        native,
        disposition,
    })
}

pub fn with_text_field<R>(
    fractional_bits: u32,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_matched_field_profile(TEXT_INPUT_CHANNELS, true, Some(fractional_bits), |field| {
        field.set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)?;
        operation(field)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_octets_and_part_end_share_a_reversible_constant_energy_chart() {
        for codeword in 0..=256 {
            let symbol = TextSymbol::from_codeword(codeword).unwrap();
            let inputs = symbol.inputs();
            assert_eq!(TextSymbol::from_inputs(&inputs), Some(symbol));
            assert_eq!(
                inputs
                    .iter()
                    .filter(|v| **v == NativePhaseCurrent::unit())
                    .count(),
                TEXT_BIT_PAIRS
            );
        }
        for reserved in 257..=511 {
            assert!(TextSymbol::from_codeword(reserved).is_none());
        }
        let mut malformed = TextSymbol::Octet(65).inputs();
        malformed[0] = NativePhaseCurrent::unit();
        malformed[1] = NativePhaseCurrent::unit();
        assert!(TextSymbol::from_inputs(&malformed).is_none());
    }
}
