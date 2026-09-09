//! Exterior octet/end-of-part chart and differential-current presentation. Learned current is
//! supplied by the native junction. This chart supplies no English grammar or response selector.
use super::material::{AlphaMaterialError, with_matched_field_profile};
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeConstitutiveField, NativeFieldDifferentialReading, NativeFieldJunctionSolver,
    NativeFieldSourceAnchor, NativeMaterialPacketReading, NativeMaterialTarget,
    NativeMaterialTransportSource, NativePacketQuadrature, NativePhaseCurrent,
    ResidentConstitutiveReturn,
};
use serde::Serialize;

pub const TEXT_BIT_PAIRS: usize = 9;
pub const TEXT_INPUT_CHANNELS: usize = 2 * TEXT_BIT_PAIRS;

/// Application boundary direction. The duplex realization uses independent I/Q ports;
/// this is not a semantic identity for a speaker or an additional learning rule.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextDirection {
    #[default]
    Incoming,
    Outgoing,
}
impl TextDirection {
    pub fn is_incoming(&self) -> bool {
        *self == Self::Incoming
    }
    pub fn quadrature(self) -> NativePacketQuadrature {
        if self == Self::Incoming {
            NativePacketQuadrature::Real
        } else {
            NativePacketQuadrature::Imaginary
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
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
    /// Exactly nine identical unit impulses: one in each addressed pair. Every application,
    /// including self-actuation, supplies that fixed exterior norm again. This does not decode
    /// the amplitude of a prior material current. The ninth bit carries a real application part
    /// boundary; it is not a native thought-completion measurement.
    pub fn inputs(self) -> Vec<NativePhaseCurrent> {
        self.inputs_on(TextDirection::Incoming)
    }
    pub fn inputs_on(self, direction: TextDirection) -> Vec<NativePhaseCurrent> {
        let unit = if direction == TextDirection::Incoming {
            NativePhaseCurrent::unit()
        } else {
            NativePhaseCurrent::new(0, 1, 1).expect("unit quadrature")
        };
        let mut inputs = vec![NativePhaseCurrent::zero(); TEXT_INPUT_CHANNELS];
        for bit in 0..TEXT_BIT_PAIRS {
            inputs[2 * bit + usize::from((self.codeword() >> bit) & 1)] = unit.clone();
        }
        inputs
    }
    pub fn from_inputs(inputs: &[NativePhaseCurrent]) -> Option<Self> {
        Self::from_inputs_on(inputs, TextDirection::Incoming)
    }
    pub fn from_inputs_on(inputs: &[NativePhaseCurrent], direction: TextDirection) -> Option<Self> {
        let unit = if direction == TextDirection::Incoming {
            NativePhaseCurrent::unit()
        } else {
            NativePhaseCurrent::new(0, 1, 1).ok()?
        };
        if inputs.len() != TEXT_INPUT_CHANNELS {
            return None;
        }
        let mut codeword = 0u16;
        for (bit, pair) in inputs.chunks_exact(2).enumerate() {
            if pair[0] == NativePhaseCurrent::zero() && pair[1] == unit {
                codeword |= 1 << bit;
            } else if pair[0] != unit || pair[1] != NativePhaseCurrent::zero() {
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
#[serde(untagged)]
pub enum TextNativeReading {
    Differential(NativeFieldDifferentialReading),
    Packet(NativeMaterialPacketReading),
}
impl TextNativeReading {
    pub fn constitutive_status(
        &self,
    ) -> Option<holonic_engine::native_ecology::constitutive_fibre::NativeFieldReceiverStatus> {
        match self {
            Self::Differential(r) => r.constitutive_status,
            Self::Packet(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TextCodeReading {
    pub native: TextNativeReading,
    pub disposition: TextCodeDisposition,
}

pub fn read_text_symbol(
    field: &NativeConstitutiveField<'_>,
    occurrence: usize,
) -> Result<TextCodeReading, AlphaMaterialError> {
    read_text_symbol_on(field, occurrence, TextDirection::Incoming)
}
pub fn read_text_symbol_on(
    field: &NativeConstitutiveField<'_>,
    occurrence: usize,
    direction: TextDirection,
) -> Result<TextCodeReading, AlphaMaterialError> {
    if field.nodes() != TEXT_INPUT_CHANNELS {
        return Err(AlphaMaterialError::Apparatus(
            "text codec requires its declared 18-channel chart".into(),
        ));
    }
    if matches!(field.material_target(),Some(NativeMaterialTarget::TensorProduct{factor_width}) if factor_width!=2)
    {
        return Err(AlphaMaterialError::Apparatus(
            "text receiver requires the declared binary packet chart".into(),
        ));
    }
    if field.material_target() == Some(NativeMaterialTarget::TensorProduct { factor_width: 2 }) {
        let reading = field
            .read_material_packet_quadrature(occurrence, direction.quadrature())?
            .ok_or_else(|| AlphaMaterialError::Apparatus("missing material packet".into()))?;
        return present_material_packet(reading);
    }
    if direction != TextDirection::Incoming {
        return Err(AlphaMaterialError::Apparatus(
            "duplex text requires the joint packet receiver".into(),
        ));
    }
    let native = (if field.has_material_transport() {
        field.read_material_transport_pairs(occurrence, TEXT_BIT_PAIRS)?
    } else {
        field.read_differential_pairs(occurrence, 2 * field.nodes(), TEXT_BIT_PAIRS)?
    })
    .ok_or_else(|| {
        AlphaMaterialError::Apparatus("text codec requires a junction outgoing current".into())
    })?;
    Ok(from_differential(native))
}

pub(crate) fn present_material_packet(reading:NativeMaterialPacketReading)->Result<TextCodeReading,AlphaMaterialError>{
    let disposition=match reading.selected {
        Some(code)=>match TextSymbol::from_codeword(u16::try_from(code).map_err(|_|AlphaMaterialError::Apparatus("packet coordinate outside text chart".into()))?){
            Some(symbol)=>TextCodeDisposition::Symbol{symbol},None=>TextCodeDisposition::Reserved{codeword:code as u16},
        },
        None=>TextCodeDisposition::Open,
    };
    Ok(TextCodeReading{native:TextNativeReading::Packet(reading),disposition})
}

/// Present the whole local constitutive fibre at an actual source. Differential signs can be
/// fixed even when absolute target currents vary within that fibre. This remains an exterior
/// codeword receiver; it supplies no grammar, candidate selector or replacement learning law.
pub fn read_constitutive_text_symbol(
    field: &mut NativeConstitutiveField<'_>,
    source: &NativeFieldSourceAnchor,
) -> Result<TextCodeReading, AlphaMaterialError> {
    if field.nodes() != TEXT_INPUT_CHANNELS {
        return Err(AlphaMaterialError::Apparatus(
            "text codec requires its declared 18-channel chart".into(),
        ));
    }
    let returned = field.read_constitutive_source(source)?;
    present_constitutive_text_return(&returned)
}

pub(super) fn present_constitutive_text_return(
    returned: &ResidentConstitutiveReturn<'_>,
) -> Result<TextCodeReading, AlphaMaterialError> {
    Ok(from_differential(
        returned
            .read_differential_pairs(0, TEXT_BIT_PAIRS)?
            .into_field_reading()?,
    ))
}

fn from_differential(native: NativeFieldDifferentialReading) -> TextCodeReading {
    let disposition = if native.unresolved != 0 {
        TextCodeDisposition::Open
    } else {
        let codeword = native.positive as u16;
        match TextSymbol::from_codeword(codeword) {
            Some(symbol) => TextCodeDisposition::Symbol { symbol },
            None => TextCodeDisposition::Reserved { codeword },
        }
    };
    TextCodeReading {
        native: TextNativeReading::Differential(native),
        disposition,
    }
}

pub fn with_text_field<R>(
    fractional_bits: u32,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_text_field_source(
        fractional_bits,
        NativeMaterialTransportSource::CoupledOutgoing,
        operation,
    )
}

pub fn with_text_field_source<R>(
    fractional_bits: u32,
    source: NativeMaterialTransportSource,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_text_field_chart(
        fractional_bits,
        source,
        NativeMaterialTarget::DirectCurrent,
        operation,
    )
}
pub fn with_text_field_chart<R>(
    fractional_bits: u32,
    source: NativeMaterialTransportSource,
    target: NativeMaterialTarget,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_matched_field_profile(TEXT_INPUT_CHANNELS, true, Some(fractional_bits), |field| {
        field.set_junction_solver(NativeFieldJunctionSolver::BalancedPairs)?;
        field.enable_material_transport_chart(source, target)?;
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

    #[test]
    #[ignore = "requires CUDA; the text receiver factors through a plural native current"]
    fn a_fixed_codeword_does_not_require_a_unique_absolute_current() {
        use holonic_engine::native_ecology::constitutive_fibre::NativeFieldOccurrence;
        with_text_field(72, |field| {
            let first=field.advance_resident(&mut NativeFieldOccurrence::entering(TextSymbol::Octet(b'A').inputs()))?;
            let source=field.retain_source(&first.source)?;
            let arrived=TextSymbol::Octet(b'B').inputs();
            field.advance_resident(&mut NativeFieldOccurrence::through_anchor(&source,arrived.clone()))?;
            // Actual native receiving variation adds the same real/imaginary current to both
            // sides of each pair. The exterior bit receiver is constant over the resulting fibre.
            let varied=arrived.iter().map(|v| {
                let real=if *v==NativePhaseCurrent::unit() { 2 } else { 1 };
                NativePhaseCurrent::new(real,2,1).unwrap()
            }).collect();
            field.advance_resident(&mut NativeFieldOccurrence::through_anchor(&source,varied))?;
            let full=field.read_constitutive_source(&source)?;
            assert!(matches!(full.inspect()?.predecessor_reading,
                holonic_engine::native_ecology::constitutive_fibre::ConstitutiveReading::Plural{..}));
            let before=field.occurrence_count();
            let face=read_constitutive_text_symbol(field,&source)?;
            assert!(matches!(face.disposition,TextCodeDisposition::Symbol { symbol: TextSymbol::Octet(b'B') }));
            assert_eq!(field.occurrence_count(),before);
            Ok(())
        }).unwrap();
    }
}

#[test]
fn duplex_codec_preserves_the_word_and_distinguishes_the_two_ports() {
    for code in 0..=256 {
        let symbol = TextSymbol::from_codeword(code).unwrap();
        for direction in [TextDirection::Incoming, TextDirection::Outgoing] {
            let input = symbol.inputs_on(direction);
            assert_eq!(TextSymbol::from_inputs_on(&input, direction), Some(symbol));
            let other = if direction == TextDirection::Incoming {
                TextDirection::Outgoing
            } else {
                TextDirection::Incoming
            };
            assert_eq!(TextSymbol::from_inputs_on(&input, other), None);
            let energy = input
                .iter()
                .map(|v| v.current().norm_square())
                .sum::<num_rational::BigRational>();
            assert_eq!(energy, num_rational::BigRational::from_integer(9.into()));
        }
    }
}
