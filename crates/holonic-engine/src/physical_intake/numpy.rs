//! The NumPy wire: `.npy` members, the `.npz` container they arrive in, and the **one lawful
//! place an IEEE bit pattern appears**.
//!
//! [definition] A stored `<f2`, `<f4` or `<f8` word is an *exterior codeword*. It is read as an
//! unsigned integer, handed to [`holonics::exact_value::ieee754`], and leaves as an exact dyadic
//! `relational_geometry::Rat`. No arithmetic is ever performed on it as a float: this module
//! contains no `f32`, no `f64` and no cast between an integer and a float. A non-finite word is
//! not a value of any format this intake admits and is refused by name, with its index and its
//! bit pattern.
//!
//! [definition] A `.npy` header is **exterior text an exterior writer chose**. Its `shape` and its
//! `descr` width are declarations, never measurements: every product taken over them is
//! `checked_mul` and an overflow is [`IntakeRefusal::DeclaredExtentOverflows`], and no declared
//! count may size a collection until it has been checked against `self.data.len()`. The zero-width
//! `<U0` case is the one where that check has no force — a zero-width array carries no payload, so
//! its declared element count is unconstrained — and it is therefore refused rather than
//! materialized.
//!
//! [proved-derived; formal-checked] The decoding is *exact and total on finite words*, which is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ExteriorIntake.lean::
//! {decode_total_on_finite, decode_exact_on_finite}`. Widening the format cannot lose a value:
//! every `binary16` codeword's exact value is a `binary32` codeword's exact value
//! (`wider_format_carries_every_value`), so admitting `<f4` beside `<f2` strictly improves what
//! intake can represent and never degrades it.

use std::collections::BTreeMap;
use std::path::Path;

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use holonics::exact_value::ExactInterval;
use holonics::exact_value::ieee754::{
    BinaryFloatDatum, BinaryFloatSpecies, FloatReading, decode_binary16_bits, decode_binary32_bits,
    decode_binary64_bits,
};

use super::IntakeRefusal;
use super::deflate::read_zip_members;

/// The IEEE-754 binary interchange formats this intake admits for an uncertainty array.
///
/// [definition] `binary16` is what the M5 release stores; `binary32` is what Boltz-2 stores;
/// `binary64` completes the interchange family. All three decode through the same exact owner, so
/// the admitted set is a statement about which *exterior* wires exist, never about precision the
/// intake itself carries.
///
/// Lean counterpart: `Foundation/ExteriorIntake.lean::FloatFormat`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum UncertaintyWordFormat {
    /// `<f2`, IEEE-754 `binary16`.
    Binary16,
    /// `<f4`, IEEE-754 `binary32`.
    Binary32,
    /// `<f8`, IEEE-754 `binary64`.
    Binary64,
}

impl UncertaintyWordFormat {
    /// Every admitted format, narrowest first.
    pub const ADMITTED: [UncertaintyWordFormat; 3] = [
        UncertaintyWordFormat::Binary16,
        UncertaintyWordFormat::Binary32,
        UncertaintyWordFormat::Binary64,
    ];

    /// The NumPy `descr` this format is stored under.
    pub const fn descr(self) -> &'static str {
        match self {
            Self::Binary16 => "<f2",
            Self::Binary32 => "<f4",
            Self::Binary64 => "<f8",
        }
    }

    /// The exact owner's species.
    pub const fn species(self) -> BinaryFloatSpecies {
        match self {
            Self::Binary16 => BinaryFloatSpecies::Binary16,
            Self::Binary32 => BinaryFloatSpecies::Binary32,
            Self::Binary64 => BinaryFloatSpecies::Binary64,
        }
    }

    /// How many octets one word occupies.
    pub const fn octets(self) -> usize {
        match self {
            Self::Binary16 => 2,
            Self::Binary32 => 4,
            Self::Binary64 => 8,
        }
    }

    /// How many bits of stored significand the format carries. `binary32` strictly exceeds
    /// `binary16`, which is why admitting the wider wire improves exactness.
    pub const fn stored_significand_bits(self) -> u32 {
        match self {
            Self::Binary16 => 10,
            Self::Binary32 => 23,
            Self::Binary64 => 52,
        }
    }

    /// The format a `descr` names, or `None` when the array is not an admitted float wire.
    pub fn from_descr(descr: &str) -> Option<Self> {
        Self::ADMITTED
            .into_iter()
            .find(|format| format.descr() == descr)
    }

    /// Decode one codeword, zero-extended to 64 bits, to its exact dyadic datum.
    ///
    /// **This is the mouth.** A finite word returns its exact value; every non-finite word returns
    /// the exact owner's refusal naming the species and the pattern.
    pub fn decode(
        self,
        word: u64,
    ) -> Result<BinaryFloatDatum, holonics::exact_value::ExactValueError> {
        match self {
            Self::Binary16 => decode_binary16_bits(word as u16),
            Self::Binary32 => decode_binary32_bits(word as u32),
            Self::Binary64 => decode_binary64_bits(word),
        }
    }
}

/// One `.npy` member: its declared type, its shape and its payload octets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NpyArray {
    /// Exterior lineage of this member, retained as testimony.
    pub lineage: String,
    /// The NumPy `descr` string, exactly as stored.
    pub descr: String,
    /// The declared shape. A zero-length shape is a NumPy scalar and carries one element.
    pub shape: Vec<usize>,
    /// The payload, after the header.
    pub data: Vec<u8>,
}

impl NpyArray {
    /// Parse one `.npy` occurrence from its complete octets.
    pub fn parse(lineage: impl Into<String>, bytes: &[u8]) -> Result<Self, IntakeRefusal> {
        let lineage = lineage.into();
        let refusal = |detail: String| IntakeRefusal::MalformedNumpyMember {
            member: lineage.clone(),
            detail,
        };
        if bytes.len() < 10 || &bytes[..6] != b"\x93NUMPY" {
            return Err(refusal("no \\x93NUMPY magic".to_owned()));
        }
        let major = bytes[6];
        let (header_start, header_octets) = match major {
            1 => (10_usize, u16::from_le_bytes([bytes[8], bytes[9]]) as usize),
            2 | 3 => {
                if bytes.len() < 12 {
                    return Err(refusal("a version 2 header is truncated".to_owned()));
                }
                (
                    12_usize,
                    u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]) as usize,
                )
            }
            other => return Err(refusal(format!("NPY major version {other} is not admitted"))),
        };
        let data_start = header_start
            .checked_add(header_octets)
            .ok_or_else(|| refusal("the header extent overflows".to_owned()))?;
        if data_start > bytes.len() {
            return Err(refusal("the header leaves the member".to_owned()));
        }
        let header = std::str::from_utf8(&bytes[header_start..data_start])
            .map_err(|error| refusal(format!("the header is not UTF-8: {error}")))?;
        if !header.contains("'fortran_order': False") {
            return Err(refusal("the member is not row-major".to_owned()));
        }
        let descr = between(header, "'descr': '", "'")
            .ok_or_else(|| refusal("the header carries no descr".to_owned()))?
            .to_owned();
        let shape_text = between(header, "'shape': (", ")")
            .ok_or_else(|| refusal("the header carries no shape".to_owned()))?;
        let shape = shape_text
            .split(',')
            .map(str::trim)
            .filter(|field| !field.is_empty())
            .map(|field| {
                field
                    .parse::<usize>()
                    .map_err(|error| refusal(format!("shape field {field:?}: {error}")))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            lineage,
            descr,
            shape,
            data: bytes[data_start..].to_vec(),
        })
    }

    /// Read one `.npy` occurrence from the filesystem.
    pub fn read(path: &Path) -> Result<Self, IntakeRefusal> {
        let bytes = std::fs::read(path).map_err(|error| IntakeRefusal::SourceUnreadable {
            origin: path.display().to_string(),
            detail: error.to_string(),
        })?;
        Self::parse(path.display().to_string(), &bytes)
    }

    /// How many elements the declared shape carries. A scalar carries one.
    ///
    /// [definition] The shape is **attacker-declared header text**, so the product is taken with
    /// `checked_mul` and an overflow is a typed refusal. A plain `product()` panics here under
    /// `overflow-checks` and wraps silently without them, and a wrapped extent can make the
    /// length-consistency check below pass for a payload it does not describe. The count this
    /// returns is still only a *declaration*: every caller must check it against `data.len()`
    /// before it is allowed to size anything.
    pub fn elements(&self) -> Result<usize, IntakeRefusal> {
        self.shape
            .iter()
            .try_fold(1_usize, |extent, axis| extent.checked_mul(*axis))
            .ok_or_else(|| IntakeRefusal::DeclaredExtentOverflows {
                member: self.lineage.clone(),
                detail: format!("the shape {:?}, whose element count", self.shape),
            })
    }

    /// `elements() · octets`, the payload extent the declaration describes, with the same
    /// discipline: an overflow is a refusal, never a wrap and never a panic.
    fn declared_octets(&self, octets: usize) -> Result<usize, IntakeRefusal> {
        self.elements()?.checked_mul(octets).ok_or_else(|| {
            IntakeRefusal::DeclaredExtentOverflows {
                member: self.lineage.clone(),
                detail: format!("the shape {:?} at {octets} octets, whose payload extent", self.shape),
            }
        })
    }

    /// The admitted float format of this member, or a refusal naming the `descr` that was found.
    pub fn word_format(&self) -> Result<UncertaintyWordFormat, IntakeRefusal> {
        UncertaintyWordFormat::from_descr(&self.descr).ok_or_else(|| {
            IntakeRefusal::UnadmittedWordFormat {
                member: self.lineage.clone(),
                descr: self.descr.clone(),
                admitted: UncertaintyWordFormat::ADMITTED
                    .iter()
                    .map(|format| format.descr())
                    .collect::<Vec<_>>()
                    .join(", "),
            }
        })
    }

    /// Every stored codeword of an admitted float member, zero-extended to 64 bits.
    ///
    /// The words are **not** decoded here: the container's job ends at the integer. Decoding is
    /// [`UncertaintyWordFormat::decode`], and the population scan that refuses non-finite words is
    /// [`super::UncertaintyArray::found`].
    pub fn float_words(&self) -> Result<(UncertaintyWordFormat, Vec<u64>), IntakeRefusal> {
        let format = self.word_format()?;
        let octets = format.octets();
        if self.data.len() != self.declared_octets(octets)? {
            return Err(IntakeRefusal::MalformedNumpyMember {
                member: self.lineage.clone(),
                detail: format!(
                    "{} payload octets under {} elements of {} is not a complete {} array",
                    self.data.len(),
                    self.elements()?,
                    octets,
                    format.descr()
                ),
            });
        }
        let words = self
            .data
            .chunks_exact(octets)
            .map(|word| {
                let mut value = 0_u64;
                for (at, octet) in word.iter().enumerate() {
                    value |= u64::from(*octet) << (8 * at);
                }
                value
            })
            .collect();
        Ok((format, words))
    }

    /// Every stored `<i4` value.
    pub fn i32_words(&self) -> Result<Vec<i32>, IntakeRefusal> {
        if self.descr != "<i4" || self.data.len() != self.declared_octets(4)? {
            return Err(IntakeRefusal::MalformedNumpyMember {
                member: self.lineage.clone(),
                detail: format!("{:?} is not a complete <i4 array", self.descr),
            });
        }
        Ok(self
            .data
            .chunks_exact(4)
            .map(|word| i32::from_le_bytes([word[0], word[1], word[2], word[3]]))
            .collect())
    }

    /// Every stored `<U*` string.
    pub fn unicode_words(&self) -> Result<Vec<String>, IntakeRefusal> {
        let refusal = |detail: String| IntakeRefusal::MalformedNumpyMember {
            member: self.lineage.clone(),
            detail,
        };
        let width = self
            .descr
            .strip_prefix("<U")
            .ok_or_else(|| refusal(format!("{:?} is not a little-endian Unicode array", self.descr)))?
            .parse::<usize>()
            .map_err(|error| refusal(format!("{:?}: {error}", self.descr)))?;
        let octets_per = width.checked_mul(4).ok_or_else(|| {
            IntakeRefusal::DeclaredExtentOverflows {
                member: self.lineage.clone(),
                detail: format!("the Unicode width {width}, whose octets per element"),
            }
        })?;
        // The length-consistency check comes **before** the zero-width shortcut. A `<U0` member
        // carries no payload at all, so `data.len()` constrains nothing about its declared element
        // count; pre-sizing a collection from that count is an allocation an exterior header chose.
        // A zero-width array that declares elements is therefore refused, not materialized.
        let declared = self.declared_octets(octets_per)?;
        if self.data.len() != declared {
            return Err(refusal("the Unicode payload is truncated".to_owned()));
        }
        if octets_per == 0 {
            let elements = self.elements()?;
            if elements != 0 {
                return Err(refusal(format!(
                    "{:?} declares {elements} elements of zero width; a zero-width array carries \
                     no payload, so nothing authenticates that count and it may not size a \
                     collection",
                    self.descr
                )));
            }
            return Ok(Vec::new());
        }
        self.data
            .chunks_exact(octets_per)
            .map(|item| {
                item.chunks_exact(4)
                    .map(|word| u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
                    .take_while(|code| *code != 0)
                    .map(|code| {
                        char::from_u32(code)
                            .ok_or_else(|| refusal(format!("invalid Unicode scalar {code}")))
                    })
                    .collect()
            })
            .collect()
    }

    /// The single string of a `<U*` scalar member.
    pub fn unicode_scalar(&self) -> Result<String, IntakeRefusal> {
        match self.unicode_words()?.as_slice() {
            [value] => Ok(value.clone()),
            other => Err(IntakeRefusal::MalformedNumpyMember {
                member: self.lineage.clone(),
                detail: format!("{} strings where one scalar was addressed", other.len()),
            }),
        }
    }
}

/// Every `.npy` member of one source, addressed by member name.
///
/// Both wires an external predictor actually emits are admitted: a `.npz` container (Boltz-2 and
/// the M5 release both write one) and a directory of extracted `.npy` members.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumpySource {
    /// Exterior lineage of the source, retained as testimony.
    pub lineage: String,
    /// The members, by name exactly as stored.
    pub members: BTreeMap<String, NpyArray>,
}

impl NumpySource {
    /// Read a `.npz` container. Every member is inflated and CRC-checked by
    /// [`super::deflate::read_zip_members`] before it is parsed.
    pub fn read_archive(path: &Path) -> Result<Self, IntakeRefusal> {
        let lineage = path.display().to_string();
        let bytes = std::fs::read(path).map_err(|error| IntakeRefusal::SourceUnreadable {
            origin: lineage.clone(),
            detail: error.to_string(),
        })?;
        let mut members = BTreeMap::new();
        for member in read_zip_members(&lineage, &bytes)? {
            let array = NpyArray::parse(format!("{lineage}::{}", member.name), &member.bytes)?;
            members.insert(member.name, array);
        }
        Ok(Self { lineage, members })
    }

    /// Read a directory of extracted `.npy` members.
    pub fn read_directory(path: &Path) -> Result<Self, IntakeRefusal> {
        let lineage = path.display().to_string();
        let entries = std::fs::read_dir(path).map_err(|error| IntakeRefusal::SourceUnreadable {
            origin: lineage.clone(),
            detail: error.to_string(),
        })?;
        let mut members = BTreeMap::new();
        for entry in entries {
            let entry = entry.map_err(|error| IntakeRefusal::SourceUnreadable {
                origin: lineage.clone(),
                detail: error.to_string(),
            })?;
            let entry_path = entry.path();
            if entry_path.extension().and_then(|value| value.to_str()) != Some("npy") {
                continue;
            }
            let name = entry_path
                .file_name()
                .and_then(|value| value.to_str())
                .ok_or_else(|| IntakeRefusal::SourceUnreadable {
                    origin: lineage.clone(),
                    detail: "a member name is not UTF-8".to_owned(),
                })?
                .to_owned();
            members.insert(name, NpyArray::read(&entry_path)?);
        }
        Ok(Self { lineage, members })
    }

    /// Read either wire, chosen by whether the path is a directory.
    pub fn read(path: &Path) -> Result<Self, IntakeRefusal> {
        if path.is_dir() {
            Self::read_directory(path)
        } else {
            Self::read_archive(path)
        }
    }

    /// One member by name, or a refusal naming the member and what the source does carry.
    pub fn member(&self, name: &str) -> Result<&NpyArray, IntakeRefusal> {
        self.members
            .get(name)
            .ok_or_else(|| IntakeRefusal::ArrayAbsent {
                origin: self.lineage.clone(),
                absent: name.to_owned(),
                present: self.member_names(),
            })
    }

    /// Every member name this source carries, in order.
    pub fn member_names(&self) -> Vec<String> {
        self.members.keys().cloned().collect()
    }
}

/// The exact reading of one decoded codeword: the value as a point, the format's own last-place
/// width, and the pattern it came from.
///
/// [definition] The value is retained as a **point**, not as a rounding enclosure. A predictor's
/// stored uncertainty word is testimony about a prediction, not a measurement whose error the
/// format's ulp describes, so widening it by half an ulp would invent an enclosure the source
/// never claimed. The ulp travels separately as [`Self::unit_in_last_place`], where a consumer
/// that does want the rounded reading can apply it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactWord {
    /// The exterior codeword, zero-extended to 64 bits.
    pub bits: u64,
    /// The format it was decoded under.
    pub format: UncertaintyWordFormat,
    /// The exact value. This is not an approximation of the word; it **is** the word.
    pub value: Rat,
    /// One unit in the last place of the format at this value, exactly `2^ulp_exponent`.
    pub unit_in_last_place: Rat,
}

impl ExactWord {
    /// Decode one codeword. A non-finite word is a typed refusal naming the format, the index and
    /// the pattern.
    pub fn decode(
        format: UncertaintyWordFormat,
        index: usize,
        bits: u64,
    ) -> Result<Self, IntakeRefusal> {
        let datum =
            format
                .decode(bits)
                .map_err(|error| IntakeRefusal::NonFiniteUncertaintyWord {
                    format: format.descr().to_owned(),
                    index,
                    bits,
                    detail: error.to_string(),
                })?;
        Ok(Self {
            bits,
            format,
            value: datum.enclosure(FloatReading::ExactBitPattern).lower,
            unit_in_last_place: datum.unit_in_last_place(),
        })
    }

    /// The value as a degenerate exact interval, for a consumer that wants an enclosure type.
    pub fn as_point(&self) -> ExactInterval {
        ExactInterval::point(self.value.clone())
    }

    /// The bit pattern as a 16-bit word where the format admits one, for the wire fields of
    /// [`crate::physical_constraint_complex::PairUncertainty`]. A wider word is truncated to its
    /// low sixteen bits **only** in that testimony field; the exact value never passes through it.
    pub fn low_sixteen_bits(&self) -> u16 {
        self.bits as u16
    }
}

fn between<'a>(text: &'a str, prefix: &str, suffix: &str) -> Option<&'a str> {
    let start = text.find(prefix)? + prefix.len();
    let end = text[start..].find(suffix)? + start;
    Some(&text[start..end])
}
