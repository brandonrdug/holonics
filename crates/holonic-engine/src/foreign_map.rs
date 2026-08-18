//! **A foreign rested map, admitted as material through one architecture-neutral mouth.**
//!
//! Plan: [`blueprint/THE_PHOENIX_REBIRTH_LIFTS_INHERITED_HEXIS_AND_RETURNS_A_NATIVE_EXECUTABLE_ECOLOGY.md`],
//! first instance
//! [`blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`].
//!
//! # What this replaces, and the defect that occasioned it
//!
//! `embedding_fiber::safetensors` was lifted out of four private driver copies on 2026-08-17 and
//! fixed the defect those copies shared — a reader that never consulted `dtype`. It kept two of its
//! own:
//!
//! 1. **A rank-0 tensor is silently dropped.** Its guard is `if !shape.is_empty()`, and a scalar
//!    declares `"shape":[]`. Measured 2026-08-18 on the local Gemma map: **928 of 2,130 entries are
//!    rank 0** — every clipped-linear bound the audio tower stores — and none of them reached the
//!    map at all. A population that is not enumerated cannot even be refused, which is a strictly
//!    worse condition than `unread`.
//! 2. **A tensor whose name carries no `.` is skipped** by `!name.contains('.')`. That predicate was
//!    aimed at `__metadata__` and it is an authored naming rule standing where a structural one
//!    belongs.
//!
//! This module keeps `dtype` checked, enumerates **every** declared entry including rank 0, refuses
//! by name rather than by omission, and admits any element width the container declares — reporting
//! what it cannot decode exactly rather than approximating it.
//!
//! # Enumeration is not admission
//!
//! The master contract's sentence is load-bearing and it is implemented here as a type: a
//! [`ForeignTensor`] in the container is **manifested**; [`AdmissionClass`] and [`TransportClass`]
//! separately say what the mouth decoded and whether a typed transport was posed or stimulated.
//! An adjacent readable matrix lends no standing to an unread vector, and a decoded vector lends no
//! standing to an unposed transport.
//!
//! # The three axes, because two of them disagree by a factor of three hundred
//!
//! Measured 2026-08-18 on the Gemma map: rank-2 entries are `630 / 2130 = 29.6%` of the population
//! and `99.793%` of the octets. **Neither count answers the question.** The `557` rank-1 entries are
//! every normalization gain in the tower and no layer conducts without them. So a coverage ledger
//! carries a third axis — [`CoverageLedger::declare_load_bearing`] — and a population's standing is
//! read on all three.
//!
//! # The path is an address and the hash declares a frame
//!
//! `CLAUDE.md`: *"A deposit's identity is its path plus its lineage."* The source path here is an
//! apparatus address and never folds into a tensor, transport, or model identity. The source-byte
//! digest is the second lawful use of a hash this project admits — **declaring an apparatus
//! frame**: it says which byte occurrence was read, so a later reader can tell that the frame moved.
//! It is not an identity and nothing is keyed by it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::ExactValueError;
use crate::exact_value::ieee754::{
    BinaryFloatDatum, BinaryFloatSpecies, decode_bfloat16_bits, decode_binary32_bits,
    decode_binary64_bits,
};

/// What a foreign container declares an element to be.
///
/// The variants are the safetensors dtype vocabulary. `Other` is not a failure — it is the honest
/// return for a container that declares something this mouth has never met, and it carries the
/// declared string so a refusal can name it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ForeignDtype {
    Bf16,
    F16,
    F32,
    F64,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Bool,
    Other(String),
}

impl ForeignDtype {
    pub fn parse(declared: &str) -> Self {
        match declared {
            "BF16" => Self::Bf16,
            "F16" => Self::F16,
            "F32" => Self::F32,
            "F64" => Self::F64,
            "I8" => Self::I8,
            "I16" => Self::I16,
            "I32" => Self::I32,
            "I64" => Self::I64,
            "U8" => Self::U8,
            "U16" => Self::U16,
            "U32" => Self::U32,
            "U64" => Self::U64,
            "BOOL" => Self::Bool,
            other => Self::Other(other.to_owned()),
        }
    }

    pub fn declared(&self) -> &str {
        match self {
            Self::Bf16 => "BF16",
            Self::F16 => "F16",
            Self::F32 => "F32",
            Self::F64 => "F64",
            Self::I8 => "I8",
            Self::I16 => "I16",
            Self::I32 => "I32",
            Self::I64 => "I64",
            Self::U8 => "U8",
            Self::U16 => "U16",
            Self::U32 => "U32",
            Self::U64 => "U64",
            Self::Bool => "BOOL",
            Self::Other(name) => name,
        }
    }

    /// Octets one element occupies, or `None` where the width is not known to this mouth.
    pub fn octets(&self) -> Option<u64> {
        Some(match self {
            Self::Bool | Self::I8 | Self::U8 => 1,
            Self::Bf16 | Self::F16 | Self::I16 | Self::U16 => 2,
            Self::F32 | Self::I32 | Self::U32 => 4,
            Self::F64 | Self::I64 | Self::U64 => 8,
            Self::Other(_) => return None,
        })
    }

    /// Whether this mouth can turn one stored codeword into an exact value with no remainder.
    ///
    /// `true` here is a claim about the **stored** codeword. It says nothing about whether that
    /// codeword is the value some earlier body held before quantizing it — that preimage stays an
    /// unresolved fibre, and the master contract refuses to let the two be conflated.
    pub fn exactly_decodable(&self) -> bool {
        matches!(
            self,
            Self::Bf16
                | Self::F32
                | Self::F64
                | Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::Bool
        )
    }
}

/// One declared tensor. **Manifested, which is not admitted.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForeignTensor {
    pub name: String,
    pub dtype: ForeignDtype,
    pub shape: Vec<usize>,
    /// Payload-relative, exactly as the container declares it.
    pub start: u64,
    pub end: u64,
}

impl ForeignTensor {
    pub fn rank(&self) -> usize {
        self.shape.len()
    }

    /// A rank-0 tensor holds exactly one element. That is the arithmetic of an empty product and it
    /// is the reason the previous reader lost 928 entries by testing `shape.is_empty()`.
    pub fn elements(&self) -> Option<u64> {
        self.shape.iter().try_fold(1u64, |product, extent| {
            product.checked_mul(u64::try_from(*extent).ok()?)
        })
    }

    pub fn declared_octets(&self) -> u64 {
        self.end.saturating_sub(self.start)
    }

    /// Whether the declared byte extent equals `elements x element width`.
    pub fn extent_agrees(&self) -> Option<bool> {
        self.dtype
            .octets()
            .and_then(|width| self.elements()?.checked_mul(width))
            .map(|implied| implied == self.declared_octets())
    }
}

/// The species of container, with the decoder version that read it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContainerSpecies {
    Safetensors {
        header_octets: u64,
        /// File offset at which element zero of a payload-relative offset lives.
        base: u64,
    },
}

/// What a declared entry was refused for. **A refusal is a return, not a gap.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ManifestRefusal {
    /// The declared byte extent does not equal `elements x element width`.
    ExtentDisagrees {
        declared_octets: u64,
        implied_octets: u64,
    },
    /// The shape's element population does not fit the source mouth's exact extent carrier.
    ElementExtentOverflow,
    /// The dtype string is not one this mouth knows a width for.
    WidthUnknown { dtype: String },
    /// The span reaches past the file.
    PastPayload { end: u64, payload: u64 },
    /// The header row is missing a field the container format requires.
    MalformedRow { missing: String },
}

/// How far the source mouth itself carried one declared population.
///
/// This is deliberately separate from [`TransportClass`]. Decoding a stored codeword does not
/// recover a transport, and manifesting a matrix does not make it a potential pathway.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AdmissionClass {
    /// The container declared the population and the mouth has not decoded it.
    ManifestedOnly,
    /// Decoded at its own codeword grain with no remainder. This is source admission, not a lift.
    DecodedExact,
    /// Decoded into a certified enclosure carrying its remainder.
    DecodedBounded,
    /// The mouth refused it by name.
    UnreadRefused,
}

impl AdmissionClass {
    pub fn name(self) -> &'static str {
        match self {
            Self::ManifestedOnly => "manifested only",
            Self::DecodedExact => "decoded exactly",
            Self::DecodedBounded => "decoded boundedly",
            Self::UnreadRefused => "unread/refused",
        }
    }
}

/// How far an admitted population has participated in a recovered transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TransportClass {
    /// No typed predecessor, successor, constitutive law, or receiver has yet been posed.
    Unposed,
    /// A transport candidate exists and no caused material has crossed it.
    PotentialOnly,
    /// Caused material crossed it and current, successor and residual returned.
    StimulatedActively,
    /// Reachable, and the declared material never excited it.
    Unexcited,
}

impl TransportClass {
    pub fn name(self) -> &'static str {
        match self {
            Self::Unposed => "unposed",
            Self::PotentialOnly => "potential-only",
            Self::StimulatedActively => "stimulated actively",
            Self::Unexcited => "unexcited",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageState {
    pub admission: AdmissionClass,
    pub transport: TransportClass,
}

/// The coverage ledger, on three axes because two of them disagree.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CoverageLedger {
    state: BTreeMap<String, CoverageState>,
    load_bearing: BTreeSet<String>,
}

impl CoverageLedger {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn manifest(
        &mut self,
        name: impl Into<String>,
        admission: AdmissionClass,
    ) -> Option<CoverageState> {
        self.state.insert(
            name.into(),
            CoverageState {
                admission,
                transport: TransportClass::Unposed,
            },
        )
    }

    /// Move only the mouth/admission axis and return its prior class.
    pub fn place_admission(
        &mut self,
        name: &str,
        admission: AdmissionClass,
    ) -> Option<AdmissionClass> {
        let state = self.state.get_mut(name)?;
        Some(std::mem::replace(&mut state.admission, admission))
    }

    /// Move only the transport/excitation axis and return its prior class.
    pub fn place_transport(
        &mut self,
        name: &str,
        transport: TransportClass,
    ) -> Option<TransportClass> {
        let state = self.state.get_mut(name)?;
        Some(std::mem::replace(&mut state.transport, transport))
    }

    /// Declare that the transport cannot be enacted without this population.
    ///
    /// This is the axis neither a rank census nor a byte census carries. A `1,856`-octet population
    /// of clip bounds and a `5.64` GB table are the same size on this axis if the pathway needs
    /// both.
    pub fn declare_load_bearing(&mut self, name: &str) -> bool {
        self.state.contains_key(name) && self.load_bearing.insert(name.to_owned())
    }

    pub fn state_of(&self, name: &str) -> Option<CoverageState> {
        self.state.get(name).copied()
    }

    pub fn is_load_bearing(&self, name: &str) -> bool {
        self.load_bearing.contains(name)
    }

    pub fn admission_census(&self) -> BTreeMap<AdmissionClass, usize> {
        let mut census = BTreeMap::new();
        for state in self.state.values() {
            *census.entry(state.admission).or_insert(0) += 1;
        }
        census
    }

    pub fn transport_census(&self) -> BTreeMap<TransportClass, usize> {
        let mut census = BTreeMap::new();
        for state in self.state.values() {
            *census.entry(state.transport).or_insert(0) += 1;
        }
        census
    }

    /// Load-bearing populations that are not yet actively stimulated, by name.
    ///
    /// **This is the station's own falsifier and it returns a list rather than a count.** A pathway
    /// claiming to have executed while this is non-empty has not executed.
    pub fn load_bearing_not_stimulated(&self) -> Vec<&str> {
        self.load_bearing
            .iter()
            .filter(|name| {
                !matches!(
                    self.state.get(name.as_str()).map(|state| state.transport),
                    Some(TransportClass::StimulatedActively)
                )
            })
            .map(String::as_str)
            .collect()
    }

    pub fn declared(&self) -> usize {
        self.state.len()
    }
}

/// A foreign rested map as this mouth read it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ForeignContainer {
    /// **An apparatus address.** It never enters any identity.
    pub address: String,
    pub species: ContainerSpecies,
    pub file_octets: u64,
    pub payload_octets: u64,
    /// Whatever the container carried in its own metadata slot, verbatim.
    pub container_metadata: BTreeMap<String, String>,
    pub tensors: BTreeMap<String, ForeignTensor>,
    /// Every entry the mouth declined, with why. Never dropped.
    pub refused: Vec<(String, ManifestRefusal)>,
}

#[derive(Debug, Error)]
pub enum ForeignMapError {
    #[error("open {address}: {reason}")]
    Open { address: String, reason: String },
    #[error("{address}: the declared header length {declared} exceeds this machine's extent")]
    HeaderTooLong { address: String, declared: u64 },
    #[error("{address}: the header is not valid UTF-8: {reason}")]
    HeaderNotText { address: String, reason: String },
    #[error("{address}: the header is not a well-formed object: {reason}")]
    HeaderMalformed { address: String, reason: String },
    #[error("the container declares no tensor named {name:?}")]
    NoSuchTensor { name: String },
    #[error("{name}: the declared shape's element population exceeds the source mouth")]
    ElementExtentOverflow { name: String },
    #[error("{name}: this reader admits {admitted} and the container declares {declared}")]
    DtypeRefused {
        name: String,
        admitted: &'static str,
        declared: String,
    },
    #[error("{name}: element span {from}..{to} reaches past the declared {elements} elements")]
    SpanPastTensor {
        name: String,
        from: u64,
        to: u64,
        elements: u64,
    },
    #[error("{name}: read: {reason}")]
    Read { name: String, reason: String },
    #[error("the float mouth refused: {0:?}")]
    MouthRefused(ExactValueError),
    #[error("the container declares overlapping tensor regions: {pairs:?}")]
    OverlappingEntries { pairs: Vec<(String, String)> },
}

// ---------------------------------------------------------------------------------------------
// The header, parsed structurally
// ---------------------------------------------------------------------------------------------

use crate::exact_json as header_scan;

/// Open a safetensors container and manifest every declared entry.
///
/// **Every** entry: rank 0 included, unknown dtypes included as refusals, and the metadata slot
/// retained verbatim rather than skipped by a name predicate.
pub fn manifest_safetensors(address: &str) -> Result<(File, ForeignContainer), ForeignMapError> {
    let mut file = File::open(address).map_err(|error| ForeignMapError::Open {
        address: address.to_owned(),
        reason: error.to_string(),
    })?;
    let file_octets = file
        .metadata()
        .map_err(|error| ForeignMapError::Open {
            address: address.to_owned(),
            reason: error.to_string(),
        })?
        .len();

    let mut length = [0u8; 8];
    file.read_exact(&mut length)
        .map_err(|error| ForeignMapError::Open {
            address: address.to_owned(),
            reason: error.to_string(),
        })?;
    let header_octets = u64::from_le_bytes(length);
    let extent = usize::try_from(header_octets).map_err(|_| ForeignMapError::HeaderTooLong {
        address: address.to_owned(),
        declared: header_octets,
    })?;
    if header_octets
        .checked_add(8)
        .is_none_or(|end| end > file_octets)
    {
        return Err(ForeignMapError::HeaderTooLong {
            address: address.to_owned(),
            declared: header_octets,
        });
    }
    let mut raw = vec![0u8; extent];
    file.read_exact(&mut raw)
        .map_err(|error| ForeignMapError::Open {
            address: address.to_owned(),
            reason: error.to_string(),
        })?;
    let text = String::from_utf8(raw).map_err(|error| ForeignMapError::HeaderNotText {
        address: address.to_owned(),
        reason: error.to_string(),
    })?;

    let pairs =
        header_scan::top_level_pairs(&text).map_err(|reason| ForeignMapError::HeaderMalformed {
            address: address.to_owned(),
            reason,
        })?;

    let base = 8 + header_octets;
    let payload_octets = file_octets.saturating_sub(base);

    let mut tensors: BTreeMap<String, ForeignTensor> = BTreeMap::new();
    let mut refused: Vec<(String, ManifestRefusal)> = Vec::new();
    let mut container_metadata = BTreeMap::new();

    for (name, span) in pairs {
        if name == "__metadata__" {
            if let Ok(inner) = header_scan::top_level_pairs(span) {
                for (key, value) in inner {
                    let text =
                        header_scan::as_string(value).unwrap_or_else(|| value.trim().to_owned());
                    container_metadata.insert(key, text);
                }
            }
            continue;
        }
        let Some(dtype_span) = header_scan::field(span, "dtype") else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "dtype".to_owned(),
                },
            ));
            continue;
        };
        let Some(shape_span) = header_scan::field(span, "shape") else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "shape".to_owned(),
                },
            ));
            continue;
        };
        let Some(offsets_span) = header_scan::field(span, "data_offsets") else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "data_offsets".to_owned(),
                },
            ));
            continue;
        };
        let Some(declared_dtype) = header_scan::as_string(dtype_span) else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "dtype".to_owned(),
                },
            ));
            continue;
        };
        let Some(shape_raw) = header_scan::as_u64_array(shape_span) else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "shape".to_owned(),
                },
            ));
            continue;
        };
        let Some(offsets) = header_scan::as_u64_array(offsets_span) else {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "data_offsets".to_owned(),
                },
            ));
            continue;
        };
        if offsets.len() != 2 {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "data_offsets".to_owned(),
                },
            ));
            continue;
        }
        let shape: Vec<usize> = shape_raw
            .iter()
            .filter_map(|extent| usize::try_from(*extent).ok())
            .collect();
        if shape.len() != shape_raw.len() {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "shape".to_owned(),
                },
            ));
            continue;
        }
        let dtype = ForeignDtype::parse(&declared_dtype);
        let tensor = ForeignTensor {
            name: name.clone(),
            dtype: dtype.clone(),
            shape,
            start: offsets[0],
            end: offsets[1],
        };
        let Some(width) = dtype.octets() else {
            refused.push((
                name,
                ManifestRefusal::WidthUnknown {
                    dtype: declared_dtype,
                },
            ));
            continue;
        };
        if tensor.end < tensor.start {
            refused.push((
                name,
                ManifestRefusal::MalformedRow {
                    missing: "ordered data_offsets".to_owned(),
                },
            ));
            continue;
        }
        let Some(implied) = tensor
            .elements()
            .and_then(|elements| elements.checked_mul(width))
        else {
            refused.push((name, ManifestRefusal::ElementExtentOverflow));
            continue;
        };
        if implied != tensor.declared_octets() {
            refused.push((
                name,
                ManifestRefusal::ExtentDisagrees {
                    declared_octets: tensor.declared_octets(),
                    implied_octets: implied,
                },
            ));
            continue;
        }
        if base
            .checked_add(tensor.end)
            .is_none_or(|end| end > file_octets)
        {
            refused.push((
                name,
                ManifestRefusal::PastPayload {
                    end: tensor.end,
                    payload: payload_octets,
                },
            ));
            continue;
        }
        tensors.insert(name, tensor);
    }

    Ok((
        file,
        ForeignContainer {
            address: address.to_owned(),
            species: ContainerSpecies::Safetensors {
                header_octets,
                base,
            },
            file_octets,
            payload_octets,
            container_metadata,
            tensors,
            refused,
        },
    ))
}

impl ForeignContainer {
    fn base(&self) -> u64 {
        match self.species {
            ContainerSpecies::Safetensors { base, .. } => base,
        }
    }

    pub fn tensor(&self, name: &str) -> Result<&ForeignTensor, ForeignMapError> {
        self.tensors
            .get(name)
            .ok_or_else(|| ForeignMapError::NoSuchTensor {
                name: name.to_owned(),
            })
    }

    /// Every manifested entry, by rank.
    pub fn rank_census(&self) -> BTreeMap<usize, (usize, u64)> {
        let mut census: BTreeMap<usize, (usize, u64)> = BTreeMap::new();
        for tensor in self.tensors.values() {
            let slot = census.entry(tensor.rank()).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += tensor.declared_octets();
        }
        census
    }

    /// The population every entry is declared over, so the ledger can be founded exhaustively.
    pub fn names(&self) -> Vec<&str> {
        self.tensors.keys().map(String::as_str).collect()
    }

    /// **Two entries claiming the same octets is a container defect and it is checked, not assumed.**
    pub fn overlaps(&self) -> Vec<(String, String)> {
        let mut ordered: Vec<&ForeignTensor> = self.tensors.values().collect();
        ordered.sort_by_key(|tensor| (tensor.start, tensor.end));
        let mut found = Vec::new();
        for (left_at, left) in ordered.iter().enumerate() {
            for right in &ordered[left_at + 1..] {
                if right.start >= left.end {
                    break;
                }
                if left.start < right.end {
                    found.push((left.name.clone(), right.name.clone()));
                }
            }
        }
        found
    }

    pub fn validate_no_overlaps(&self) -> Result<(), ForeignMapError> {
        let pairs = self.overlaps();
        if pairs.is_empty() {
            Ok(())
        } else {
            Err(ForeignMapError::OverlappingEntries { pairs })
        }
    }

    /// A contiguous span of the flat element array, as raw octets. Rank is irrelevant here — a
    /// tensor's elements are laid out row-major and a caller who wants a row asks for the span a
    /// row occupies.
    pub fn read_elements(
        &self,
        file: &mut File,
        name: &str,
        from: u64,
        count: u64,
    ) -> Result<Vec<u8>, ForeignMapError> {
        let tensor = self.tensor(name)?;
        let elements = tensor
            .elements()
            .ok_or_else(|| ForeignMapError::ElementExtentOverflow {
                name: name.to_owned(),
            })?;
        let to = from
            .checked_add(count)
            .ok_or_else(|| ForeignMapError::SpanPastTensor {
                name: name.to_owned(),
                from,
                to: u64::MAX,
                elements,
            })?;
        if to > elements {
            return Err(ForeignMapError::SpanPastTensor {
                name: name.to_owned(),
                from,
                to,
                elements,
            });
        }
        let width = tensor
            .dtype
            .octets()
            .ok_or_else(|| ForeignMapError::DtypeRefused {
                name: name.to_owned(),
                admitted: "a dtype with a known width",
                declared: tensor.dtype.declared().to_owned(),
            })?;
        let offset = self
            .base()
            .checked_add(tensor.start)
            .and_then(|base| {
                from.checked_mul(width)
                    .and_then(|span| base.checked_add(span))
            })
            .ok_or_else(|| ForeignMapError::Read {
                name: name.to_owned(),
                reason: "the requested byte offset overflowed".to_owned(),
            })?;
        let octets = count
            .checked_mul(width)
            .ok_or_else(|| ForeignMapError::Read {
                name: name.to_owned(),
                reason: "the requested byte extent overflowed".to_owned(),
            })?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|error| ForeignMapError::Read {
                name: name.to_owned(),
                reason: error.to_string(),
            })?;
        let mut raw = vec![
            0u8;
            usize::try_from(octets).map_err(|_| ForeignMapError::Read {
                name: name.to_owned(),
                reason: "the span exceeds this machine's extent".to_owned(),
            })?
        ];
        file.read_exact(&mut raw)
            .map_err(|error| ForeignMapError::Read {
                name: name.to_owned(),
                reason: error.to_string(),
            })?;
        Ok(raw)
    }

    /// A span of a `BF16` tensor as raw codewords, at any rank.
    pub fn read_bf16(
        &self,
        file: &mut File,
        name: &str,
        from: u64,
        count: u64,
    ) -> Result<Vec<u16>, ForeignMapError> {
        let tensor = self.tensor(name)?;
        if tensor.dtype != ForeignDtype::Bf16 {
            return Err(ForeignMapError::DtypeRefused {
                name: name.to_owned(),
                admitted: "BF16",
                declared: tensor.dtype.declared().to_owned(),
            });
        }
        let raw = self.read_elements(file, name, from, count)?;
        Ok(raw
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect())
    }

    /// The whole of a `BF16` tensor as raw codewords. For a rank-0 tensor this is one word, which
    /// is the case the previous reader could not express at all.
    pub fn read_bf16_whole(
        &self,
        file: &mut File,
        name: &str,
    ) -> Result<Vec<u16>, ForeignMapError> {
        let elements = self.tensor(name)?.elements().ok_or_else(|| {
            ForeignMapError::ElementExtentOverflow {
                name: name.to_owned(),
            }
        })?;
        self.read_bf16(file, name, 0, elements)
    }

    /// One row of a rank-2 tensor, named for the reader that wants exactly that.
    pub fn read_rows_bf16(
        &self,
        file: &mut File,
        name: &str,
        from_row: usize,
        rows: usize,
    ) -> Result<(Vec<u16>, usize), ForeignMapError> {
        let tensor = self.tensor(name)?;
        if tensor.rank() != 2 {
            return Err(ForeignMapError::DtypeRefused {
                name: name.to_owned(),
                admitted: "a rank-2 tensor",
                declared: format!("rank {}", tensor.rank()),
            });
        }
        let width = tensor.shape[1] as u64;
        let from = u64::try_from(from_row)
            .ok()
            .and_then(|row| row.checked_mul(width))
            .ok_or_else(|| ForeignMapError::Read {
                name: name.to_owned(),
                reason: "the requested row offset overflowed".to_owned(),
            })?;
        let count = u64::try_from(rows)
            .ok()
            .and_then(|rows| rows.checked_mul(width))
            .ok_or_else(|| ForeignMapError::Read {
                name: name.to_owned(),
                reason: "the requested row extent overflowed".to_owned(),
            })?;
        let words = self.read_bf16(file, name, from, count)?;
        Ok((words, tensor.shape[1]))
    }

    /// Decode a `BF16` span to exact float data. **The declared float mouth is the only door.**
    pub fn decode_bf16(
        &self,
        file: &mut File,
        name: &str,
        from: u64,
        count: u64,
    ) -> Result<Vec<BinaryFloatDatum>, ForeignMapError> {
        let words = self.read_bf16(file, name, from, count)?;
        words
            .into_iter()
            .map(|word| decode_bfloat16_bits(word).map_err(ForeignMapError::MouthRefused))
            .collect()
    }

    /// Decode an exactly supported binary floating species without executing a machine float.
    pub fn decode_binary_float(
        &self,
        file: &mut File,
        name: &str,
        from: u64,
        count: u64,
    ) -> Result<Vec<BinaryFloatDatum>, ForeignMapError> {
        let tensor = self.tensor(name)?;
        let raw = self.read_elements(file, name, from, count)?;
        match tensor.dtype {
            ForeignDtype::Bf16 => raw
                .chunks_exact(2)
                .map(|word| {
                    decode_bfloat16_bits(u16::from_le_bytes([word[0], word[1]]))
                        .map_err(ForeignMapError::MouthRefused)
                })
                .collect(),
            ForeignDtype::F32 => raw
                .chunks_exact(4)
                .map(|word| {
                    decode_binary32_bits(u32::from_le_bytes([word[0], word[1], word[2], word[3]]))
                        .map_err(ForeignMapError::MouthRefused)
                })
                .collect(),
            ForeignDtype::F64 => raw
                .chunks_exact(8)
                .map(|word| {
                    decode_binary64_bits(u64::from_le_bytes([
                        word[0], word[1], word[2], word[3], word[4], word[5], word[6], word[7],
                    ]))
                    .map_err(ForeignMapError::MouthRefused)
                })
                .collect(),
            _ => Err(ForeignMapError::DtypeRefused {
                name: name.to_owned(),
                admitted: "BF16, F32, or F64",
                declared: tensor.dtype.declared().to_owned(),
            }),
        }
    }

    /// The species every decoded `BF16` datum belongs to, stated rather than assumed by a caller.
    pub const STORED_SPECIES: BinaryFloatSpecies = BinaryFloatSpecies::Bfloat16;

    /// **A frame declaration, never an identity.** Streams the whole file and returns the digest of
    /// the byte occurrence that was read, so a later reader can tell that the frame moved.
    pub fn declare_source_frame(&self, file: &mut File) -> Result<String, ForeignMapError> {
        use sha2::{Digest, Sha256};
        file.seek(SeekFrom::Start(0))
            .map_err(|error| ForeignMapError::Read {
                name: self.address.clone(),
                reason: error.to_string(),
            })?;
        let mut hasher = Sha256::new();
        let mut buffer = vec![0u8; 1 << 22];
        loop {
            let read = file
                .read(&mut buffer)
                .map_err(|error| ForeignMapError::Read {
                    name: self.address.clone(),
                    reason: error.to_string(),
                })?;
            if read == 0 {
                break;
            }
            hasher.update(&buffer[..read]);
        }
        Ok(hasher
            .finalize()
            .iter()
            .map(|octet| format!("{octet:02x}"))
            .collect())
    }

    /// Found a ledger over the whole manifested population, with every refusal already placed.
    ///
    /// Nothing is promoted here. Every readable entry starts manifested and **transport-unposed**;
    /// only a source mouth may move admission, and only an actual typed composition/stimulation may
    /// move transport.
    pub fn found_ledger(&self) -> CoverageLedger {
        let mut ledger = CoverageLedger::new();
        for name in self.tensors.keys() {
            ledger.manifest(name.clone(), AdmissionClass::ManifestedOnly);
        }
        for (name, _) in &self.refused {
            ledger.manifest(name.clone(), AdmissionClass::UnreadRefused);
        }
        ledger
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_container(path: &std::path::Path, header: &str, payload: &[u8]) {
        let mut file = File::create(path).expect("create");
        let bytes = header.as_bytes();
        file.write_all(&(bytes.len() as u64).to_le_bytes())
            .expect("length");
        file.write_all(bytes).expect("header");
        file.write_all(payload).expect("payload");
    }

    fn scratch(name: &str) -> std::path::PathBuf {
        let mut path = std::env::temp_dir();
        path.push(format!("foreign_map_{name}.safetensors"));
        path
    }

    /// **The defect this module was built for.** A rank-0 tensor declares `"shape":[]`, and the
    /// prior reader's `!shape.is_empty()` guard dropped it without a refusal.
    #[test]
    fn a_rank_zero_tensor_is_manifested_and_read() {
        let path = scratch("rank_zero");
        // 1.0 and 2.0 as BF16 codewords.
        let payload = [0x80u8, 0x3f, 0x00, 0x40];
        write_container(
            &path,
            r#"{"a.scalar":{"dtype":"BF16","shape":[],"data_offsets":[0,2]},"b.vector":{"dtype":"BF16","shape":[1],"data_offsets":[2,4]}}"#,
            &payload,
        );
        let (mut file, container) =
            manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        assert_eq!(container.tensors.len(), 2, "both entries manifested");
        assert!(container.refused.is_empty(), "{:?}", container.refused);
        let scalar = container.tensor("a.scalar").expect("present");
        assert_eq!(scalar.rank(), 0);
        assert_eq!(scalar.elements(), Some(1), "an empty product is one");
        let words = container
            .read_bf16_whole(&mut file, "a.scalar")
            .expect("read");
        assert_eq!(words, vec![0x3f80]);
        let _ = std::fs::remove_file(&path);
    }

    /// The metadata slot is retained rather than skipped by a name predicate, and it does not
    /// become a tensor.
    #[test]
    fn the_metadata_slot_is_retained_and_is_not_a_tensor() {
        let path = scratch("metadata");
        write_container(
            &path,
            r#"{"__metadata__":{"format":"pt"},"w":{"dtype":"BF16","shape":[1],"data_offsets":[0,2]}}"#,
            &[0x80, 0x3f],
        );
        let (_, container) = manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        assert_eq!(container.tensors.len(), 1);
        assert_eq!(
            container
                .container_metadata
                .get("format")
                .map(String::as_str),
            Some("pt")
        );
        // And a name with no dot is a tensor, because a structural test decides that, not a naming
        // rule.
        assert!(container.tensors.contains_key("w"));
        let _ = std::fs::remove_file(&path);
    }

    /// A malformed extent refuses **by name** rather than by omission, which is the difference
    /// between an unread population and an invisible one.
    #[test]
    fn a_disagreeing_extent_refuses_by_name() {
        let path = scratch("extent");
        write_container(
            &path,
            r#"{"good":{"dtype":"BF16","shape":[2],"data_offsets":[0,4]},"bad":{"dtype":"BF16","shape":[4],"data_offsets":[4,6]},"wide":{"dtype":"Q4_K","shape":[8],"data_offsets":[6,10]}}"#,
            &[0u8; 10],
        );
        let (_, container) = manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        assert_eq!(container.tensors.len(), 1);
        let named: BTreeMap<_, _> = container.refused.iter().cloned().collect();
        assert!(matches!(
            named.get("bad"),
            Some(ManifestRefusal::ExtentDisagrees {
                declared_octets: 2,
                implied_octets: 8
            })
        ));
        assert!(matches!(
            named.get("wide"),
            Some(ManifestRefusal::WidthUnknown { .. })
        ));
        // And the ledger places both refusals without any station having run.
        let ledger = container.found_ledger();
        assert_eq!(
            ledger.state_of("bad").map(|state| state.admission),
            Some(AdmissionClass::UnreadRefused)
        );
        assert_eq!(
            ledger.state_of("good"),
            Some(CoverageState {
                admission: AdmissionClass::ManifestedOnly,
                transport: TransportClass::Unposed,
            })
        );
        let _ = std::fs::remove_file(&path);
    }

    /// **Enumeration is not admission, as a type.** A manifested tensor carries no coverage until a
    /// station places one, and a load-bearing population that never conducted is returned by name.
    #[test]
    fn the_ledger_returns_load_bearing_populations_that_never_conducted() {
        let mut ledger = CoverageLedger::new();
        ledger.manifest("norm.weight", AdmissionClass::DecodedExact);
        ledger.manifest("mlp.up", AdmissionClass::DecodedExact);
        ledger.place_transport("mlp.up", TransportClass::StimulatedActively);
        assert!(ledger.declare_load_bearing("norm.weight"));
        assert!(ledger.declare_load_bearing("mlp.up"));
        assert!(!ledger.declare_load_bearing("absent"));
        assert_eq!(ledger.load_bearing_not_stimulated(), vec!["norm.weight"]);
        let prior = ledger.place_transport("norm.weight", TransportClass::StimulatedActively);
        assert_eq!(prior, Some(TransportClass::Unposed), "a move is visible");
        assert!(ledger.load_bearing_not_stimulated().is_empty());
    }

    /// A span past the tensor refuses rather than returning octets from its neighbour.
    #[test]
    fn a_span_past_the_tensor_refuses() {
        let path = scratch("span");
        write_container(
            &path,
            r#"{"a":{"dtype":"BF16","shape":[2,2],"data_offsets":[0,8]},"b":{"dtype":"BF16","shape":[2],"data_offsets":[8,12]}}"#,
            &[0u8; 12],
        );
        let (mut file, container) =
            manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        assert!(matches!(
            container.read_bf16(&mut file, "a", 3, 2),
            Err(ForeignMapError::SpanPastTensor { .. })
        ));
        assert!(container.overlaps().is_empty());
        let (row, width) = container.read_rows_bf16(&mut file, "a", 1, 1).expect("row");
        assert_eq!(width, 2);
        assert_eq!(row.len(), 2);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn nested_nonadjacent_overlaps_are_all_exhibited() {
        let path = scratch("nested_overlaps");
        write_container(
            &path,
            r#"{"outer":{"dtype":"BF16","shape":[4],"data_offsets":[0,8]},"left":{"dtype":"BF16","shape":[1],"data_offsets":[2,4]},"right":{"dtype":"BF16","shape":[1],"data_offsets":[6,8]}}"#,
            &[0u8; 8],
        );
        let (_, container) = manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        assert_eq!(
            container.overlaps(),
            vec![
                ("outer".to_owned(), "left".to_owned()),
                ("outer".to_owned(), "right".to_owned()),
            ]
        );
        assert!(matches!(
            container.validate_no_overlaps(),
            Err(ForeignMapError::OverlappingEntries { pairs }) if pairs.len() == 2
        ));
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn binary32_and_binary64_codewords_enter_through_the_exact_ieee_mouth() {
        let path = scratch("binary_float");
        let mut payload = Vec::new();
        payload.extend_from_slice(&0x3f80_0000u32.to_le_bytes());
        payload.extend_from_slice(&0x3ff0_0000_0000_0000u64.to_le_bytes());
        write_container(
            &path,
            r#"{"single":{"dtype":"F32","shape":[],"data_offsets":[0,4]},"double":{"dtype":"F64","shape":[],"data_offsets":[4,12]}}"#,
            &payload,
        );
        let (mut file, container) =
            manifest_safetensors(path.to_str().expect("utf-8")).expect("manifest");
        let single = container
            .decode_binary_float(&mut file, "single", 0, 1)
            .expect("binary32");
        let double = container
            .decode_binary_float(&mut file, "double", 0, 1)
            .expect("binary64");
        assert_eq!(
            single[0].value(),
            relational_geometry::Rat::from_integer(1.into())
        );
        assert_eq!(
            double[0].value(),
            relational_geometry::Rat::from_integer(1.into())
        );
        assert!(ForeignDtype::F32.exactly_decodable());
        assert!(ForeignDtype::F64.exactly_decodable());
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn a_shape_past_the_element_extent_refuses_instead_of_wrapping() {
        let tensor = ForeignTensor {
            name: "too-wide".to_owned(),
            dtype: ForeignDtype::Bf16,
            shape: vec![usize::MAX, 2],
            start: 0,
            end: 0,
        };
        assert_eq!(tensor.elements(), None);
        assert_eq!(tensor.extent_agrees(), None);
    }
}
