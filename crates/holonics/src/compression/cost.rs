//! **The cost of a compression: description plus work against the literal, counted in the bits of
//! an actual code.**
//!
//! [definition] A compression is a codec pivot carrying its decoder
//! ([tablet](../../../../docs/canon/TABLET_THE_COMPRESSION.md)). Here the pivot is a navigator
//! codec: a navigator step with its initial configuration (the key) and the decoder's receiver face
//! read at every tick of the navigator's clock, so the material is regenerated causally. Its cost
//! is Levin's (Lean `Compression/Core/Cost`):
//!
//! ```text
//! Kt = |p| + ⌈log₂ t⌉        |p| the bits of the code the decoder reads, t the navigator's ticks
//! ℓ  = ⌈log₂ |A|⌉ · n         the literal code of n symbols over the alphabet A
//! pays off  ⇔  Kt < ℓ         an integer comparison
//! ```
//!
//! [definition] **Every bit counted is a bit written** (Lean `Compression/Core/Cost`). A
//! [`CodecFamily`] declares finite families of navigator steps, initial configurations and receiver
//! reads, the reference machine both coder and decoder share (Lean `CodecFamily`). A codec's
//! description is the concatenation of its three indices in fixed width,
//! `⌈log₂ #steps⌉ + ⌈log₂ #configurations⌉ + ⌈log₂ #reads⌉` bits ([`NavigatorCodec::description`];
//! `CodecFamily.describe`, `describe_length`); [`CodecFamily::codec_of`] reads it back and refuses
//! truncated and trailing bits (`readIndex_describe`, `ofDescription_describe`,
//! `ofDescription_length`), so distinct codecs have distinct descriptions (`describe_injective`).
//! The literal is the fixed-width index code over a declared [`Alphabet`], read back by [`Alphabet::read_literal`] (`literalCode`, `literalCode_length`,
//! `readLiteral_literalCode`). `⌈log₂ t⌉` is the least `k` with `t ≤ 2^k` (Lean `Nat.clog 2`), a bit
//! length, and `t` counts the navigator's ticks, one reading per tick. The material's length is the
//! receiver's request, declared to both presentations and written by neither. A pivot pays off
//! exactly when `Kt` is below the literal's code length (`CodecPivot.PaysOff`), which is the
//! comparison of the two actual codes (`CodecPivot.paysOff_iff_code_shorter`).
//!
//! [definition] **RIDE and FOUND in bits.** A [`CodecPivot`] is either whole (Lean `CodecPivot`: the
//! codec regenerates the material, and its code alone releases it, `CodecPivot.release_code`) or
//! partial (Lean `CodecFamily.partialCode`): the codec plus the residual on the faces it does not
//! regenerate (`foundedFaces`), written as a count and fixed-width `(position, symbol)` patches. The
//! faces the navigator regenerates ride on its description at no further bits; each founded face
//! adds exactly one patch (`CodecFamily.partialCode_length`), and no face is founded exactly when
//! the codec regenerates the material (`foundedFaces_eq_nil_iff`). Both are actual codes, and
//! [`CodecFamily::release`] regenerates the material from them
//! (`CodecFamily.partialRelease_partialCode`). This prices the codec's residual only: no exchange
//! rate between the [`crate::compression::resonance`] work form and bits is asserted, and an exact
//! rational residual of a linear face map has no fixed bit price, so the face-map cokernel is not
//! priced here.
//!
//! [definition] `Kt` is one limit reading of the receipt `(description, residual, work)`;
//! [`CompressionCost`] keeps every axis, and no single scalar of progress is asserted.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::One;

use crate::compression::CompressionError;

/// `⌈log₂ value⌉`: the least `k` with `value ≤ 2^k`, and `0` for `0` and `1` (Lean `Nat.clog 2`).
pub fn ceil_log2(value: &BigUint) -> u64 {
    if value <= &BigUint::one() {
        0
    } else {
        (value - BigUint::one()).bits()
    }
}

/// The fixed width of an index below a population: `⌈log₂ population⌉` bits.
fn width(population: usize) -> u64 {
    ceil_log2(&BigUint::from(population))
}

/// Write `index` in `bits` bits, most significant first.
fn write_index(code: &mut Vec<bool>, index: usize, bits: u64) {
    for place in (0..bits).rev() {
        let bit = u32::try_from(place)
            .ok()
            .and_then(|place| index.checked_shr(place))
            .is_some_and(|shifted| shifted & 1 == 1);
        code.push(bit);
    }
}

/// Read a `bits`-bit index below `population`, most significant first.
fn read_index(
    code: &mut impl Iterator<Item = bool>,
    bits: u64,
    population: usize,
) -> Result<usize, CompressionError> {
    let mut index = 0usize;
    for _ in 0..bits {
        let bit = code.next().ok_or(CompressionError::TruncatedCode)?;
        index = index
            .checked_mul(2)
            .and_then(|shifted| shifted.checked_add(usize::from(bit)))
            .ok_or(CompressionError::TruncatedCode)?;
    }
    if index >= population {
        return Err(CompressionError::IndexOutside { index, population });
    }
    Ok(index)
}

/// [definition] **A declared alphabet**: distinct symbols, each coded by its index in fixed width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alphabet<Symbol> {
    symbols: Vec<Symbol>,
}

impl<Symbol: PartialEq + Clone> Alphabet<Symbol> {
    /// An alphabet of distinct symbols; an empty or repeating one is refused.
    pub fn new(symbols: Vec<Symbol>) -> Result<Self, CompressionError> {
        if symbols.is_empty() {
            return Err(CompressionError::EmptyFamily { what: "alphabet" });
        }
        for (index, symbol) in symbols.iter().enumerate() {
            if symbols[..index].contains(symbol) {
                return Err(CompressionError::RepeatedSymbol { index });
            }
        }
        Ok(Self { symbols })
    }

    /// `|A|`.
    pub fn size(&self) -> usize {
        self.symbols.len()
    }

    /// The bits of one literal symbol, `⌈log₂ |A|⌉`.
    pub fn symbol_bits(&self) -> u64 {
        width(self.symbols.len())
    }

    fn index_of(&self, symbol: &Symbol) -> Result<usize, CompressionError> {
        self.symbols
            .iter()
            .position(|known| known == symbol)
            .ok_or(CompressionError::SymbolOutside)
    }

    /// **The literal code** of a material: every symbol's index in fixed width (Lean
    /// `literalCode`; `literalBits` is its length, `literalCode_length`).
    pub fn literal(&self, material: &[Symbol]) -> Result<Vec<bool>, CompressionError> {
        let mut code = Vec::new();
        for symbol in material {
            write_index(&mut code, self.index_of(symbol)?, self.symbol_bits());
        }
        Ok(code)
    }

    /// **The literal decoder**: read `length` fixed-width symbol indices, refusing a truncated code,
    /// an index outside the alphabet and trailing bits (Lean `readLiteral`,
    /// `readLiteral_literalCode`).
    pub fn read_literal(
        &self,
        code: &[bool],
        length: usize,
    ) -> Result<Vec<Symbol>, CompressionError> {
        let mut bits = code.iter().copied();
        let mut material = Vec::with_capacity(length);
        for _ in 0..length {
            let index = read_index(&mut bits, self.symbol_bits(), self.symbols.len())?;
            material.push(self.symbols[index].clone());
        }
        if bits.next().is_some() {
            return Err(CompressionError::TrailingCode);
        }
        Ok(material)
    }
}

/// [definition] **A codec family**: the declared finite families of navigator steps, initial
/// configurations and receiver reads that coder and decoder share.
pub struct CodecFamily<Configuration, Symbol> {
    steps: Vec<Box<dyn Fn(&Configuration) -> Configuration>>,
    configurations: Vec<Configuration>,
    reads: Vec<Box<dyn Fn(&Configuration) -> Symbol>>,
}

impl<Configuration: fmt::Debug, Symbol> fmt::Debug for CodecFamily<Configuration, Symbol> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CodecFamily")
            .field("steps", &self.steps.len())
            .field("configurations", &self.configurations)
            .field("reads", &self.reads.len())
            .finish()
    }
}

impl<Configuration: Clone, Symbol: PartialEq + Clone> CodecFamily<Configuration, Symbol> {
    /// A family from its declared steps, configurations and reads; each must be nonempty.
    pub fn new(
        steps: Vec<Box<dyn Fn(&Configuration) -> Configuration>>,
        configurations: Vec<Configuration>,
        reads: Vec<Box<dyn Fn(&Configuration) -> Symbol>>,
    ) -> Result<Self, CompressionError> {
        if steps.is_empty() {
            return Err(CompressionError::EmptyFamily { what: "steps" });
        }
        if configurations.is_empty() {
            return Err(CompressionError::EmptyFamily {
                what: "configurations",
            });
        }
        if reads.is_empty() {
            return Err(CompressionError::EmptyFamily { what: "reads" });
        }
        Ok(Self {
            steps,
            configurations,
            reads,
        })
    }

    /// `(#steps, #configurations, #reads)`.
    pub fn populations(&self) -> (usize, usize, usize) {
        (
            self.steps.len(),
            self.configurations.len(),
            self.reads.len(),
        )
    }

    /// The codec naming step `step`, initial configuration `initial` and read `read`.
    pub fn codec(
        &self,
        step: usize,
        initial: usize,
        read: usize,
    ) -> Result<NavigatorCodec<'_, Configuration, Symbol>, CompressionError> {
        for (index, population) in [
            (step, self.steps.len()),
            (initial, self.configurations.len()),
            (read, self.reads.len()),
        ] {
            if index >= population {
                return Err(CompressionError::IndexOutside { index, population });
            }
        }
        Ok(NavigatorCodec {
            family: self,
            step,
            initial,
            read,
        })
    }

    /// **The decoder of a description**: the codec whose three fixed-width indices the bits carry.
    pub fn codec_of(
        &self,
        description: &[bool],
    ) -> Result<NavigatorCodec<'_, Configuration, Symbol>, CompressionError> {
        let mut bits = description.iter().copied();
        let codec = self.read_codec(&mut bits)?;
        if bits.next().is_some() {
            return Err(CompressionError::TrailingCode);
        }
        Ok(codec)
    }

    fn read_codec(
        &self,
        bits: &mut impl Iterator<Item = bool>,
    ) -> Result<NavigatorCodec<'_, Configuration, Symbol>, CompressionError> {
        let (steps, configurations, reads) = self.populations();
        let step = read_index(bits, width(steps), steps)?;
        let initial = read_index(bits, width(configurations), configurations)?;
        let read = read_index(bits, width(reads), reads)?;
        self.codec(step, initial, read)
    }

    /// **The decompression carried by a pivot**: read the codec's description and, for a partial
    /// pivot, its residual, then release `length` faces over the navigator's ticks and patch the
    /// residual faces.
    pub fn release(
        &self,
        alphabet: &Alphabet<Symbol>,
        code: &[bool],
        length: usize,
        form: PivotForm,
    ) -> Result<Vec<Symbol>, CompressionError> {
        let mut bits = code.iter().copied();
        let codec = self.read_codec(&mut bits)?;
        let mut material = codec.decode(length);
        if form == PivotForm::Partial {
            let count = read_index(&mut bits, width(length + 1), length + 1)?;
            for _ in 0..count {
                let position = read_index(&mut bits, width(length), length)?;
                let symbol = read_index(&mut bits, alphabet.symbol_bits(), alphabet.size())?;
                material[position] = alphabet.symbols[symbol].clone();
            }
        }
        if bits.next().is_some() {
            return Err(CompressionError::TrailingCode);
        }
        Ok(material)
    }
}

/// [definition] **A navigator codec** (Lean `NavigatorCodec`): one step, one initial configuration
/// and one read of a declared family, named by their indices.
pub struct NavigatorCodec<'family, Configuration, Symbol> {
    family: &'family CodecFamily<Configuration, Symbol>,
    step: usize,
    initial: usize,
    read: usize,
}

impl<Configuration, Symbol> fmt::Debug for NavigatorCodec<'_, Configuration, Symbol> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NavigatorCodec")
            .field("step", &self.step)
            .field("initial", &self.initial)
            .field("read", &self.read)
            .finish()
    }
}

impl<Configuration: Clone, Symbol: PartialEq + Clone> NavigatorCodec<'_, Configuration, Symbol> {
    /// The initial configuration: the key.
    pub fn initial(&self) -> &Configuration {
        &self.family.configurations[self.initial]
    }

    /// **The description**: the step, initial configuration and read indices in fixed width.
    pub fn description(&self) -> Vec<bool> {
        let (steps, configurations, reads) = self.family.populations();
        let mut code = Vec::new();
        write_index(&mut code, self.step, width(steps));
        write_index(&mut code, self.initial, width(configurations));
        write_index(&mut code, self.read, width(reads));
        code
    }

    /// **The causal release of `n` faces over `n` ticks** (Lean `NavigatorCodec.decode`): the face
    /// at tick `k` is the reading of the configuration after `k` steps; each face depends only on
    /// earlier ticks (`decode_succ`, `decode_take`).
    pub fn decode(&self, length: usize) -> Vec<Symbol> {
        let step = &self.family.steps[self.step];
        let read = &self.family.reads[self.read];
        let mut released = Vec::with_capacity(length);
        let mut configuration = self.initial().clone();
        for tick in 0..length {
            released.push(read(&configuration));
            if tick + 1 < length {
                configuration = step(&configuration);
            }
        }
        released
    }

    /// Whether the causal release is exactly the material (Lean `Regenerates`).
    pub fn regenerates(&self, material: &[Symbol]) -> bool {
        self.decode(material.len()) == material
    }

    /// **The whole pivot** (Lean `CodecPivot`), refused when the codec does not regenerate the
    /// material.
    pub fn pivot(
        &self,
        alphabet: &Alphabet<Symbol>,
        material: &[Symbol],
    ) -> Result<CodecPivot, CompressionError> {
        alphabet.literal(material)?;
        if !self.regenerates(material) {
            return Err(CompressionError::NotRegenerated {
                length: material.len(),
            });
        }
        Ok(CodecPivot {
            form: PivotForm::Whole,
            code: self.description(),
            description: self.description().len(),
            length: material.len(),
            literal: literal_bits(alphabet, material.len()),
        })
    }

    /// **The partial pivot**: the codec plus the residual on every face it does not regenerate,
    /// written as a count in `⌈log₂(n + 1)⌉` bits and `(position, symbol)` patches in
    /// `⌈log₂ n⌉ + ⌈log₂ |A|⌉` bits each.
    pub fn partial_pivot(
        &self,
        alphabet: &Alphabet<Symbol>,
        material: &[Symbol],
    ) -> Result<CodecPivot, CompressionError> {
        alphabet.literal(material)?;
        let length = material.len();
        let released = self.decode(length);
        let patches: Vec<(usize, usize)> = released
            .iter()
            .zip(material)
            .enumerate()
            .filter(|(_, (released, wanted))| released != wanted)
            .map(|(position, (_, wanted))| Ok((position, alphabet.index_of(wanted)?)))
            .collect::<Result<_, CompressionError>>()?;
        let mut code = self.description();
        let description = code.len();
        write_index(&mut code, patches.len(), width(length + 1));
        for (position, symbol) in &patches {
            write_index(&mut code, *position, width(length));
            write_index(&mut code, *symbol, alphabet.symbol_bits());
        }
        Ok(CodecPivot {
            form: PivotForm::Partial,
            code,
            description,
            length,
            literal: literal_bits(alphabet, length),
        })
    }
}

/// **The literal's code length**: `⌈log₂ |A|⌉` bits per symbol (Lean `literalBits`).
pub fn literal_bits<Symbol: PartialEq + Clone>(
    alphabet: &Alphabet<Symbol>,
    length: usize,
) -> BigUint {
    BigUint::from(alphabet.symbol_bits()) * BigUint::from(length)
}

/// Which presentation a pivot's code is: the codec alone, or the codec with its residual.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PivotForm {
    /// The codec regenerates the material (Lean `CodecPivot`).
    Whole,
    /// The codec and the residual patches on the faces it does not regenerate.
    Partial,
}

/// [definition] **A codec pivot**: the code the decoder reads, with the material length it
/// releases. Its constructors are [`NavigatorCodec::pivot`] and [`NavigatorCodec::partial_pivot`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodecPivot {
    form: PivotForm,
    code: Vec<bool>,
    description: usize,
    length: usize,
    literal: BigUint,
}

impl CodecPivot {
    /// Whole or partial.
    pub fn form(&self) -> PivotForm {
        self.form
    }

    /// The code: the description, then the residual for a partial pivot.
    pub fn code(&self) -> &[bool] {
        &self.code
    }

    /// The material length the pivot releases.
    pub fn length(&self) -> usize {
        self.length
    }

    /// **The pivot's receipt against the literal**: `Kt = |code| + ⌈log₂ t⌉` (Lean `CodecPivot.kt`,
    /// `kt_eq`; for a partial pivot `|code|` is `CodecFamily.partialCode_length`).
    pub fn cost(&self) -> CompressionCost {
        let work = BigUint::from(self.length);
        let program = BigUint::from(self.code.len());
        CompressionCost {
            description: BigUint::from(self.description),
            residual: BigUint::from(self.code.len() - self.description),
            kt: &program + BigUint::from(ceil_log2(&work)),
            work,
            literal: self.literal.clone(),
        }
    }
}

/// [definition] **The receipt of a compression against the literal**, in exact bits: the
/// description, the residual (zero for a whole pivot), the work in ticks, `Kt` and the literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompressionCost {
    /// The description bits of the codec.
    pub description: BigUint,
    /// The residual bits: the faces founded outside the navigator's image.
    pub residual: BigUint,
    /// `t`, the navigator's ticks.
    pub work: BigUint,
    /// `Kt = description + residual + ⌈log₂ t⌉`.
    pub kt: BigUint,
    /// `ℓ`, the literal's code length.
    pub literal: BigUint,
}

impl CompressionCost {
    /// **A compression pays off exactly when its description plus work is below the literal**:
    /// the integer comparison `Kt < ℓ` (Lean `CodecPivot.PaysOff`).
    pub fn pays_off(&self) -> bool {
        self.kt < self.literal
    }

    /// **The saved bits** `ℓ − Kt`, signed.
    pub fn saved_bits(&self) -> BigInt {
        BigInt::from(self.literal.clone()) - BigInt::from(self.kt.clone())
    }
}

#[cfg(test)]
mod tests;
