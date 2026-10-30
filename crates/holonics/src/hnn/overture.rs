//! **The overture's intake** (#146; records `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §§2
//! and 5): the exterior boundary where an inherited model's coefficients arrive, and the only place
//! they are ever floats.
//!
//! [definition] **A stored word decodes exactly to its dyadic ratio.** An IEEE-754 word of a format
//! with `p` stored significand bits and `e` exponent bits is read as three integer fields, and its
//! value is `± significand · 2^ulp`, with the hidden leading one restored on a normal word and the
//! exponent `ulp = max(E, 1) − bias − p`, `bias = 2^(e−1) − 1`. An all-ones exponent field is an
//! infinity or a NaN and is refused: nothing is invented for it. `bfloat16` is the format
//! `(p, e) = (7, 8)`, the upper half of a `binary32` word, so it decodes as that word does.
//! Lean owns the law (`HolonicsResearch/Foundation/ExteriorIntake`): [`FloatFormat::decode`] is
//! `decode`, its `Ok` arm `decode_exact_on_finite` and its refusal `decode_refuses_nonfinite`;
//! [`FloatFormat`] is `FloatFormat` and [`Dyadic`] the codeword's `value` in lowest terms.
//!
//! [definition; agent-inferred, October 30] **The file is exterior codec information.** A
//! `safetensors` file is an eight-byte little-endian header length, a JSON header naming each
//! tensor's dtype, shape and byte range, and the tensors' bytes. [`Safetensors::read`] admits the
//! three float formats a released model is stored in, checks that each tensor's range holds its
//! shape and that the ranges tile the data exactly, and keeps the names and shapes only as the
//! codec's account of where the coefficients came from: they are never native identities. The
//! header reader admits only what the format's header uses (objects, arrays, strings and
//! non-negative integers) and refuses the rest.
//!
//! The coefficients enter once, here, as the initial configuration of native navigators and the
//! opening constitution of native owners (the record's §3 table); the engine is never graded by
//! agreement with the source model, and the source model is never run.
use std::collections::BTreeMap;
use std::ops::Range;

use num_bigint::BigInt;
use num_traits::One;
use thiserror::Error;

use crate::ratio::Rat;

/// An IEEE-754 binary interchange format, as its two field widths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FloatFormat {
    /// Stored significand bits: 10, 7 and 23 for `binary16`, `bfloat16` and `binary32`.
    pub significand_bits: u32,
    /// Exponent field bits: 5, 8 and 8.
    pub exponent_bits: u32,
}

impl FloatFormat {
    pub const BINARY16: FloatFormat = FloatFormat { significand_bits: 10, exponent_bits: 5 };
    pub const BFLOAT16: FloatFormat = FloatFormat { significand_bits: 7, exponent_bits: 8 };
    pub const BINARY32: FloatFormat = FloatFormat { significand_bits: 23, exponent_bits: 8 };

    /// The stored word's width in bits.
    pub fn width(self) -> u32 {
        1 + self.exponent_bits + self.significand_bits
    }

    /// The exponent bias, `2^(e−1) − 1`.
    pub fn bias(self) -> i32 {
        (1i32 << (self.exponent_bits - 1)) - 1
    }

    /// The word's exact value, or the refusal of a nonfinite word. Bits above the format's width
    /// are refused as a malformed word, never masked.
    pub fn decode(self, word: u32) -> Result<Dyadic, IntakeRefusal> {
        let (p, e) = (self.significand_bits, self.exponent_bits);
        if self.width() < 32 && word >> self.width() != 0 {
            return Err(IntakeRefusal::WiderThanFormat { word, format: self });
        }
        let fraction = i64::from(word & ((1u32 << p) - 1));
        let raw = (word >> p) & ((1u32 << e) - 1);
        if raw == (1u32 << e) - 1 {
            return Err(IntakeRefusal::NonFinite { word, format: self });
        }
        let negative = word >> (p + e) & 1 == 1;
        let significand = if raw == 0 { fraction } else { (1i64 << p) + fraction };
        let ulp = raw.max(1) as i32 - self.bias() - p as i32;
        Ok(Dyadic::reduced(if negative { -significand } else { significand }, ulp))
    }
}

/// An exact dyadic ratio `numerator · 2^exponent` in lowest terms: the numerator odd, or zero with
/// exponent zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dyadic {
    pub numerator: i64,
    pub exponent: i32,
}

impl Dyadic {
    /// `numerator · 2^exponent` with the numerator's factors of two moved into the exponent.
    pub fn reduced(numerator: i64, exponent: i32) -> Dyadic {
        if numerator == 0 {
            return Dyadic { numerator: 0, exponent: 0 };
        }
        let shift = numerator.trailing_zeros();
        Dyadic { numerator: numerator >> shift, exponent: exponent + shift as i32 }
    }

    /// The exact value as a ratio.
    pub fn value(self) -> Rat {
        let n = BigInt::from(self.numerator);
        let power = BigInt::one() << self.exponent.unsigned_abs();
        if self.exponent >= 0 { Rat::from_integer(n * power) } else { Rat::new(n, power) }
    }
}

/// A refusal at the intake. Every arm names what was refused; nothing is rounded, masked or
/// skipped in its place.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum IntakeRefusal {
    #[error("a nonfinite word {word:#x} of {format:?}: an infinity or a NaN has no value")]
    NonFinite { word: u32, format: FloatFormat },
    #[error("a word {word:#x} wider than {format:?}")]
    WiderThanFormat { word: u32, format: FloatFormat },
    #[error("the file ends before its header does")]
    Truncated,
    #[error("the header is malformed at its byte {at}")]
    MalformedHeader { at: usize },
    #[error("the header entry {name} is not a tensor: {what}")]
    MalformedEntry { name: String, what: &'static str },
    #[error("the tensor {name} is stored as {dtype}, which is not a float format the intake admits")]
    UnadmittedDtype { name: String, dtype: String },
    #[error("the tensor {name}'s byte range does not hold its shape")]
    Extent { name: String },
    #[error("the tensors' byte ranges do not tile the data exactly")]
    Tiling,
    #[error("the tensor {name} is named twice")]
    Duplicate { name: String },
}

/// One tensor's account in the file: its name and shape as exterior codec information, its
/// format, and its byte range within the data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorEntry {
    pub name: String,
    pub format: FloatFormat,
    pub shape: Vec<usize>,
    pub range: Range<usize>,
}

impl TensorEntry {
    /// The number of coefficients, the product of the shape (one for a scalar).
    pub fn count(&self) -> usize {
        self.shape.iter().product()
    }
}

/// A `safetensors` file read at the boundary: its tensors in the order of their byte ranges.
#[derive(Clone, Debug)]
pub struct Safetensors<'a> {
    data: &'a [u8],
    pub entries: Vec<TensorEntry>,
}

impl<'a> Safetensors<'a> {
    /// Reads the header and checks every tensor's range against its shape and the data's extent.
    pub fn read(bytes: &'a [u8]) -> Result<Safetensors<'a>, IntakeRefusal> {
        let length = bytes.get(..8).ok_or(IntakeRefusal::Truncated)?;
        let length = usize::try_from(u64::from_le_bytes(length.try_into().expect("eight bytes"))).map_err(|_| IntakeRefusal::Truncated)?;
        let end = length.checked_add(8).filter(|&end| end <= bytes.len()).ok_or(IntakeRefusal::Truncated)?;
        let (header, data) = (&bytes[8..end], &bytes[end..]);
        let Json::Object(fields) = Header { text: header, at: 0 }.document()? else {
            return Err(IntakeRefusal::MalformedHeader { at: 0 });
        };
        let mut entries = Vec::new();
        for (name, field) in fields {
            if name == "__metadata__" {
                continue;
            }
            entries.push(entry(name, field)?);
        }
        entries.sort_by_key(|t| (t.range.start, t.range.end));
        let mut next = 0;
        for t in &entries {
            if t.range.start != next {
                return Err(IntakeRefusal::Tiling);
            }
            next = t.range.end;
        }
        if next != data.len() {
            return Err(IntakeRefusal::Tiling);
        }
        Ok(Safetensors { data, entries })
    }

    /// The tensor's coefficients, each decoded exactly, in its stored (row-major) order.
    pub fn decoded(&self, entry: &TensorEntry) -> Result<Vec<Dyadic>, IntakeRefusal> {
        let bytes = (entry.format.width() / 8) as usize;
        self.data[entry.range.clone()]
            .chunks_exact(bytes)
            .map(|w| entry.format.decode(w.iter().rev().fold(0u32, |acc, &b| acc << 8 | u32::from(b))))
            .collect()
    }
}

/// One header entry checked as a tensor.
fn entry(name: String, field: Json) -> Result<TensorEntry, IntakeRefusal> {
    let malformed = |what| IntakeRefusal::MalformedEntry { name: name.clone(), what };
    let Json::Object(mut fields) = field else { return Err(malformed("not an object")) };
    let Some(Json::String(dtype)) = fields.remove("dtype") else { return Err(malformed("no dtype")) };
    let format = match dtype.as_str() {
        "F16" => FloatFormat::BINARY16,
        "BF16" => FloatFormat::BFLOAT16,
        "F32" => FloatFormat::BINARY32,
        _ => return Err(IntakeRefusal::UnadmittedDtype { name, dtype }),
    };
    let integers = |value: Option<Json>, what| -> Result<Vec<usize>, IntakeRefusal> {
        let Some(Json::Array(items)) = value else { return Err(malformed(what)) };
        items.into_iter().map(|v| if let Json::Integer(n) = v { usize::try_from(n).map_err(|_| malformed(what)) } else { Err(malformed(what)) }).collect()
    };
    let shape = integers(fields.remove("shape"), "no shape of integers")?;
    let offsets = integers(fields.remove("data_offsets"), "no data offsets of integers")?;
    let [start, end] = offsets[..] else { return Err(malformed("data offsets are not a pair")) };
    let held = shape.iter().try_fold(1usize, |n, &d| n.checked_mul(d)).and_then(|n| n.checked_mul((format.width() / 8) as usize));
    if start > end || held != Some(end - start) {
        return Err(IntakeRefusal::Extent { name });
    }
    Ok(TensorEntry { name, format, shape, range: start..end })
}

/// The header values the format uses.
enum Json {
    Object(BTreeMap<String, Json>),
    Array(Vec<Json>),
    String(String),
    Integer(u64),
}

/// The header's reader: a cursor over its bytes.
struct Header<'a> {
    text: &'a [u8],
    at: usize,
}

impl Header<'_> {
    fn refuse<T>(&self) -> Result<T, IntakeRefusal> {
        Err(IntakeRefusal::MalformedHeader { at: self.at })
    }

    /// The one value the header is, with only padding (the format pads with spaces) after it.
    fn document(mut self) -> Result<Json, IntakeRefusal> {
        let value = self.value()?;
        self.space();
        if self.at != self.text.len() {
            return self.refuse();
        }
        Ok(value)
    }

    fn space(&mut self) {
        while matches!(self.text.get(self.at), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }

    fn take(&mut self, byte: u8) -> Result<(), IntakeRefusal> {
        self.space();
        if self.text.get(self.at) != Some(&byte) {
            return self.refuse();
        }
        self.at += 1;
        Ok(())
    }

    fn value(&mut self) -> Result<Json, IntakeRefusal> {
        self.space();
        match self.text.get(self.at) {
            Some(b'{') => {
                self.at += 1;
                let mut fields = BTreeMap::new();
                self.space();
                if self.text.get(self.at) == Some(&b'}') {
                    self.at += 1;
                    return Ok(Json::Object(fields));
                }
                loop {
                    self.space();
                    let key = self.string()?;
                    self.take(b':')?;
                    let value = self.value()?;
                    if fields.insert(key.clone(), value).is_some() {
                        return Err(IntakeRefusal::Duplicate { name: key });
                    }
                    self.space();
                    match self.text.get(self.at) {
                        Some(b',') => self.at += 1,
                        Some(b'}') => {
                            self.at += 1;
                            return Ok(Json::Object(fields));
                        }
                        _ => return self.refuse(),
                    }
                }
            }
            Some(b'[') => {
                self.at += 1;
                let mut items = Vec::new();
                self.space();
                if self.text.get(self.at) == Some(&b']') {
                    self.at += 1;
                    return Ok(Json::Array(items));
                }
                loop {
                    items.push(self.value()?);
                    self.space();
                    match self.text.get(self.at) {
                        Some(b',') => self.at += 1,
                        Some(b']') => {
                            self.at += 1;
                            return Ok(Json::Array(items));
                        }
                        _ => return self.refuse(),
                    }
                }
            }
            Some(b'"') => Ok(Json::String(self.string()?)),
            Some(b'0'..=b'9') => {
                let from = self.at;
                while matches!(self.text.get(self.at), Some(b'0'..=b'9')) {
                    self.at += 1;
                }
                let digits = &self.text[from..self.at];
                if (digits.len() > 1 && digits[0] == b'0') || matches!(self.text.get(self.at), Some(b'.' | b'e' | b'E')) {
                    return self.refuse();
                }
                digits.iter().try_fold(0u64, |n, &d| n.checked_mul(10)?.checked_add(u64::from(d - b'0'))).map(Json::Integer).ok_or(IntakeRefusal::MalformedHeader { at: from })
            }
            _ => self.refuse(),
        }
    }

    fn string(&mut self) -> Result<String, IntakeRefusal> {
        if self.text.get(self.at) != Some(&b'"') {
            return self.refuse();
        }
        self.at += 1;
        let mut out = Vec::new();
        loop {
            let Some(&b) = self.text.get(self.at) else { return self.refuse() };
            self.at += 1;
            match b {
                b'"' => return String::from_utf8(out).or_else(|_| self.refuse()),
                b'\\' => {
                    let Some(&escape) = self.text.get(self.at) else { return self.refuse() };
                    self.at += 1;
                    let unit = match escape {
                        b'"' | b'\\' | b'/' => escape,
                        b'b' => 8,
                        b'f' => 12,
                        b'n' => b'\n',
                        b'r' => b'\r',
                        b't' => b'\t',
                        b'u' => {
                            let high = self.hex()?;
                            let code = if (0xD800..0xDC00).contains(&high) {
                                self.take(b'\\')?;
                                if self.text.get(self.at) != Some(&b'u') {
                                    return self.refuse();
                                }
                                self.at += 1;
                                let low = self.hex()?;
                                if !(0xDC00..0xE000).contains(&low) {
                                    return self.refuse();
                                }
                                0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00)
                            } else {
                                high
                            };
                            let Some(c) = char::from_u32(code) else { return self.refuse() };
                            out.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
                            continue;
                        }
                        _ => return self.refuse(),
                    };
                    out.push(unit);
                }
                0..=0x1f => return self.refuse(),
                _ => out.push(b),
            }
        }
    }

    fn hex(&mut self) -> Result<u32, IntakeRefusal> {
        let digits = self.text.get(self.at..self.at + 4).ok_or(IntakeRefusal::MalformedHeader { at: self.at })?;
        let code = std::str::from_utf8(digits).ok().and_then(|d| u32::from_str_radix(d, 16).ok()).ok_or(IntakeRefusal::MalformedHeader { at: self.at })?;
        self.at += 4;
        Ok(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Lean `Codeword.value`, computed independently over big ratios from the three fields.
    fn lean_value(format: FloatFormat, word: u32) -> Rat {
        let (p, e) = (format.significand_bits, format.exponent_bits);
        let fraction = BigInt::from(word & ((1 << p) - 1));
        let raw = (word >> p) & ((1 << e) - 1);
        let significand = if raw == 0 { fraction } else { (BigInt::one() << p) + fraction };
        let ulp = i64::from(if raw == 0 { 1 } else { raw }) - i64::from(format.bias()) - i64::from(p);
        let sign = if word >> (p + e) & 1 == 1 { -Rat::one() } else { Rat::one() };
        let power = Rat::from_integer(BigInt::one() << ulp.unsigned_abs());
        sign * Rat::from_integer(significand) * if ulp >= 0 { power } else { power.recip() }
    }

    /// The exact encoder of a value onto a format's grid, where the value is on it: the inverse
    /// the refinement statements read.
    fn encode(format: FloatFormat, d: Dyadic) -> Option<u32> {
        let (p, e) = (format.significand_bits, format.exponent_bits);
        let sign = u32::from(d.numerator < 0) << (p + e);
        if d.numerator == 0 {
            return Some(0);
        }
        let magnitude = d.numerator.unsigned_abs();
        // The leading one's place, as an exponent of the value.
        let top = 63 - magnitude.leading_zeros() as i32 + d.exponent;
        let min_normal = 1 - format.bias();
        let (raw, ulp) = if top >= min_normal { (top + format.bias(), top - p as i32) } else { (0, min_normal - p as i32) };
        if raw >= (1 << e) - 1 || d.exponent < ulp {
            return None;
        }
        let significand = magnitude << (d.exponent - ulp) as u32;
        let fraction = if raw == 0 { significand } else { significand - (1 << p) };
        (fraction < 1 << p).then(|| sign | (raw as u32) << p | fraction as u32)
    }

    /// Every `bfloat16` and `binary16` word decodes to Lean's value or is refused exactly when its
    /// exponent field is all ones; each decoded value is in lowest terms and is carried exactly by
    /// `binary32` (`binary32_strictly_refines_binary16`, and `bfloat16` as `binary32`'s upper half).
    #[test]
    fn every_half_width_word_decodes_to_its_own_value() {
        for format in [FloatFormat::BFLOAT16, FloatFormat::BINARY16] {
            let mut refused = 0;
            for word in 0..1u32 << 16 {
                match format.decode(word) {
                    Ok(d) => {
                        assert_eq!(d.value(), lean_value(format, word), "{format:?} {word:#x}");
                        assert!(d.numerator % 2 != 0 || d == Dyadic { numerator: 0, exponent: 0 });
                        let wide = encode(FloatFormat::BINARY32, d).expect("binary32 carries every narrower value");
                        assert_eq!(FloatFormat::BINARY32.decode(wide), Ok(d));
                        let back = if d.numerator == 0 { 0 } else { word };
                        assert_eq!(encode(format, d), Some(back), "the round trip, up to the sign of zero");
                        if format == FloatFormat::BFLOAT16 {
                            assert_eq!(FloatFormat::BINARY32.decode(word << 16), Ok(d), "bfloat16 is binary32's upper half");
                        }
                    }
                    Err(IntakeRefusal::NonFinite { .. }) => refused += 1,
                    Err(other) => panic!("{other:?}"),
                }
            }
            assert_eq!(refused, 2 << format.significand_bits, "{format:?}: the all-ones exponent field, both signs");
        }
        // binary16 holds 1 + 2^(−10), which bfloat16 does not, and bfloat16 holds 2^100, which
        // binary16 does not: neither half-width format refines the other.
        assert!(encode(FloatFormat::BFLOAT16, Dyadic::reduced(1025, -10)).is_none());
        assert!(encode(FloatFormat::BINARY16, Dyadic::reduced(1, 100)).is_none());
    }

    /// The boundary words of `binary32`: zeros, the smallest and largest subnormal, the smallest
    /// normal, one, the largest finite, and the refused infinity and NaN; and a word wider than its
    /// format is refused, never masked.
    #[test]
    fn the_boundary_words_decode_exactly() {
        let f = FloatFormat::BINARY32;
        let at = |w: u32| f.decode(w).map(|d| (d.numerator, d.exponent));
        assert_eq!(at(0x0000_0000), Ok((0, 0)));
        assert_eq!(at(0x8000_0000), Ok((0, 0)));
        assert_eq!(at(0x0000_0001), Ok((1, -149)));
        assert_eq!(at(0x007f_ffff), Ok(((1 << 23) - 1, -149)));
        assert_eq!(at(0x0080_0000), Ok((1, -126)));
        assert_eq!(at(0x3f80_0000), Ok((1, 0)));
        assert_eq!(at(0xc000_0000), Ok((-1, 1)));
        assert_eq!(at(0x7f7f_ffff), Ok(((1 << 24) - 1, 104)));
        assert!(matches!(f.decode(0x7f80_0000), Err(IntakeRefusal::NonFinite { .. })));
        assert!(matches!(f.decode(0xffc0_0001), Err(IntakeRefusal::NonFinite { .. })));
        assert!(matches!(FloatFormat::BFLOAT16.decode(0x1_3f80), Err(IntakeRefusal::WiderThanFormat { .. })));
    }

    /// A file of the format's own shape: the header's length, its JSON padded with spaces, and the
    /// tensors' bytes little-endian.
    fn file(header: &str, data: &[u8]) -> Vec<u8> {
        let mut header = header.as_bytes().to_vec();
        header.resize(header.len().next_multiple_of(8), b' ');
        let mut out = (header.len() as u64).to_le_bytes().to_vec();
        out.extend(header);
        out.extend(data);
        out
    }

    /// A two-tensor file reads, its metadata passes untouched, and each tensor decodes to its
    /// words' values in stored order; each malformed file is refused by name.
    #[test]
    fn a_file_reads_its_tensors_and_refuses_what_it_does_not_hold() {
        // bf16 [1, −2, 0.5, 3] as a 2×2 matrix, then f32 [0.25].
        let data: Vec<u8> = [0x3f80u16, 0xc000, 0x3f00, 0x4040].iter().flat_map(|w| w.to_le_bytes()).chain(0x3e80_0000u32.to_le_bytes()).collect();
        let header = r#"{"__metadata__":{"format":"pt"},"w.bias":{"dtype":"F32","shape":[1],"data_offsets":[8,12]},"w":{"dtype":"BF16","shape":[2,2],"data_offsets":[0,8]}}"#;
        let bytes = file(header, &data);
        let read = Safetensors::read(&bytes).expect("read");
        assert_eq!(read.entries.iter().map(|t| (t.name.as_str(), t.count())).collect::<Vec<_>>(), [("w", 4), ("w.bias", 1)]);
        let values: Vec<Rat> = read.decoded(&read.entries[0]).expect("w").into_iter().map(Dyadic::value).collect();
        let r = |n: i64, d: i64| Rat::new(n.into(), d.into());
        assert_eq!(values, [r(1, 1), r(-2, 1), r(1, 2), r(3, 1)]);
        assert_eq!(read.decoded(&read.entries[1]).expect("bias"), [Dyadic { numerator: 1, exponent: -2 }]);

        let refused = |header: &str, data: &[u8]| Safetensors::read(&file(header, data)).err();
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[2,2],"data_offsets":[0,8]}}"#, &data), Some(IntakeRefusal::Tiling), "four bytes held by no tensor");
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[3],"data_offsets":[0,8]}}"#, &data[..8]), Some(IntakeRefusal::Extent { name: "w".into() }));
        assert_eq!(refused(r#"{"w":{"dtype":"I32","shape":[2],"data_offsets":[0,8]}}"#, &data[..8]), Some(IntakeRefusal::UnadmittedDtype { name: "w".into(), dtype: "I32".into() }));
        assert_eq!(
            refused(r#"{"a":{"dtype":"BF16","shape":[4],"data_offsets":[0,8]},"b":{"dtype":"BF16","shape":[2],"data_offsets":[4,8]}}"#, &data[..8]),
            Some(IntakeRefusal::Tiling),
            "overlapping ranges"
        );
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[2],"data_offsets":[0,4]},"w":{"dtype":"BF16","shape":[2],"data_offsets":[4,8]}}"#, &data[..8]), Some(IntakeRefusal::Duplicate { name: "w".into() }));
        assert!(matches!(refused(r#"{"w":{"dtype":"BF16","shape":[2.0],"data_offsets":[0,4]}}"#, &data[..4]), Some(IntakeRefusal::MalformedHeader { .. })));
        assert_eq!(Safetensors::read(&bytes[..12]).err(), Some(IntakeRefusal::Truncated));
        // A tensor holding a NaN is read, and its decoding is refused at the word.
        let nan = file(r#"{"w":{"dtype":"BF16","shape":[1],"data_offsets":[0,2]}}"#, &0x7fc0u16.to_le_bytes());
        let read = Safetensors::read(&nan).expect("read");
        assert!(matches!(read.decoded(&read.entries[0]), Err(IntakeRefusal::NonFinite { .. })));
    }
}
