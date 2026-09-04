use std::path::Path;

use serde::{Deserialize, Serialize};

use super::{digest, valid_digest};
use crate::native_rest::ContentIdentity;

/// The only predecessor testimony retained by a cultivated product.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PredecessorProductIdentity {
    pub sha256: String,
    pub extent: u64,
}

impl PredecessorProductIdentity {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            sha256: digest(bytes),
            extent: bytes.len() as u64,
        }
    }

    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, CultivatedRestRefusal> {
        ContentIdentity::from_path(path)
            .map(|identity| Self {
                sha256: identity.sha256,
                extent: identity.extent,
            })
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
    }

    pub(crate) fn validate(&self) -> Result<(), CultivatedRestRefusal> {
        if !valid_digest(&self.sha256) || self.extent == 0 {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "predecessor".to_owned(),
            ));
        }
        Ok(())
    }
}

/// Content identities of the W1 codebook and the graph registry it addresses.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CodebookGraphIdentity {
    pub codebook_sha256: String,
    pub graph_identity: String,
}

impl CodebookGraphIdentity {
    /// Construct identities from the canonical bytes of the two addressed registries.
    pub fn from_canonical(codebook: &[u8], graph: &[u8]) -> Self {
        Self {
            codebook_sha256: digest(codebook),
            graph_identity: digest(graph),
        }
    }

    pub(crate) fn validate(&self) -> Result<(), CultivatedRestRefusal> {
        if !valid_digest(&self.codebook_sha256) || !valid_digest(&self.graph_identity) {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "codebook/graph".to_owned(),
            ));
        }
        Ok(())
    }
}

/// A typed boundary port.  `carrier` is lineage and law testimony, not a semantic .local/data/program
/// distinction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PortDirection {
    Input,
    Output,
}

/// Row extent provenance. W3 keeps rows runtime-varying; a fixed training length is never
/// smuggled into the rested product.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExtentOrigin {
    Runtime,
    Declared(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum OctaveBoundOrigin {
    Rested(u64),
    RuntimeDerived,
}

/// A law may identify one extent axis without silently identifying the others.
///
/// In particular, W3 can carry row lineage while width remains an independently varying
/// receiver extent.  The axis is part of the canonical law digest and the wire representation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum PortExtentAgreement {
    Rows { left: String, right: String },
    Width { left: String, right: String },
    OctaveBound { left: String, right: String },
}

impl PortExtentAgreement {
    pub(crate) fn endpoints(&self) -> (&str, &str) {
        match self {
            Self::Rows { left, right }
            | Self::Width { left, right }
            | Self::OctaveBound { left, right } => (left, right),
        }
    }

    pub(crate) fn axis_tag(&self) -> u8 {
        match self {
            Self::Rows { .. } => 1,
            Self::Width { .. } => 2,
            Self::OctaveBound { .. } => 3,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypedPort {
    pub name: String,
    pub direction: PortDirection,
    pub carrier: String,
    pub rows: ExtentOrigin,
    pub width: u64,
    pub octave_bound: OctaveBoundOrigin,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypedLaw {
    pub name: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub constitutive_digest: String,
    pub extent_agreements: Vec<PortExtentAgreement>,
}

/// Exact integer morphology.  Floating point is intentionally not representable here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MorphologyPayload {
    AlignedFactor(AlignedFactor),
    SparseDelta(SparseDelta),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlignedFactor {
    pub rows: u32,
    pub columns: u32,
    pub rank: u32,
    pub resident_grain: u32,
    pub left_exponent: i32,
    pub right_exponent: i32,
    pub entry_octets: u8,
    pub left: Vec<i64>,
    pub right: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseDelta {
    pub rows: u32,
    pub columns: u32,
    pub entries: Vec<SparseDeltaEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseDeltaEntry {
    pub index: u64,
    pub value: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PayloadDescriptor {
    kind: String,
    rows: u32,
    columns: u32,
    rank: Option<u32>,
    resident_grain: Option<u32>,
    entries: u64,
    left_exponent: Option<i32>,
    right_exponent: Option<i32>,
    entry_octets: u8,
    negative_entries: u64,
}

impl MorphologyPayload {
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, CultivatedRestRefusal> {
        self.descriptor_and_bytes().map(|(_, bytes)| bytes)
    }

    pub fn canonical_digest(&self) -> Result<String, CultivatedRestRefusal> {
        self.canonical_bytes().map(|bytes| super::digest(&bytes))
    }

    pub(crate) fn descriptor_and_bytes(
        &self,
    ) -> Result<(PayloadDescriptor, Vec<u8>), CultivatedRestRefusal> {
        let mut bytes = Vec::new();
        match self {
            Self::AlignedFactor(factor) => {
                if factor.rows == 0
                    || factor.columns == 0
                    || factor.rank == 0
                    || factor.entry_octets != 8
                    || factor.resident_grain == 0
                    || factor.left.len() != factor.rows as usize * factor.rank as usize
                    || factor.right.len() != factor.rank as usize * factor.columns as usize
                {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                bytes.push(1);
                bytes.extend_from_slice(&factor.resident_grain.to_le_bytes());
                bytes.extend_from_slice(&factor.left_exponent.to_le_bytes());
                bytes.extend_from_slice(&factor.right_exponent.to_le_bytes());
                bytes.push(factor.entry_octets);
                for value in [
                    factor.rows as u64,
                    factor.columns as u64,
                    factor.rank as u64,
                ] {
                    bytes.extend_from_slice(&value.to_le_bytes());
                }
                for value in factor.left.iter().chain(factor.right.iter()) {
                    bytes.extend_from_slice(&value.to_le_bytes());
                }
                Ok((
                    PayloadDescriptor {
                        kind: "aligned-factor".to_owned(),
                        rows: factor.rows,
                        columns: factor.columns,
                        rank: Some(factor.rank),
                        resident_grain: Some(factor.resident_grain),
                        entries: (factor.left.len() + factor.right.len()) as u64,
                        left_exponent: Some(factor.left_exponent),
                        right_exponent: Some(factor.right_exponent),
                        entry_octets: factor.entry_octets,
                        negative_entries: factor
                            .left
                            .iter()
                            .chain(factor.right.iter())
                            .filter(|value| **value < 0)
                            .count() as u64,
                    },
                    bytes,
                ))
            }
            Self::SparseDelta(delta) => {
                if delta.rows == 0
                    || delta.columns == 0
                    || delta
                        .entries
                        .iter()
                        .any(|entry| entry.index >= delta.rows as u64 * delta.columns as u64)
                    || delta
                        .entries
                        .windows(2)
                        .any(|pair| pair[0].index >= pair[1].index)
                {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                bytes.push(2);
                bytes.extend_from_slice(&(delta.rows as u64).to_le_bytes());
                bytes.extend_from_slice(&(delta.columns as u64).to_le_bytes());
                bytes.extend_from_slice(&(delta.entries.len() as u64).to_le_bytes());
                for entry in &delta.entries {
                    bytes.extend_from_slice(&entry.index.to_le_bytes());
                    bytes.extend_from_slice(&entry.value.to_le_bytes());
                }
                Ok((
                    PayloadDescriptor {
                        kind: "sparse-delta".to_owned(),
                        rows: delta.rows,
                        columns: delta.columns,
                        rank: None,
                        resident_grain: None,
                        entries: delta.entries.len() as u64,
                        left_exponent: None,
                        right_exponent: None,
                        entry_octets: 8,
                        negative_entries: delta
                            .entries
                            .iter()
                            .filter(|entry| entry.value < 0)
                            .count() as u64,
                    },
                    bytes,
                ))
            }
        }
    }

    pub(crate) fn from_wire(
        descriptor: &PayloadDescriptor,
        bytes: &[u8],
    ) -> Result<Self, CultivatedRestRefusal> {
        match descriptor.kind.as_str() {
            "aligned-factor" => {
                let rank = descriptor.rank.ok_or(CultivatedRestRefusal::PayloadShape)?;
                let mut cursor = 38usize;
                let left_exponent = descriptor
                    .left_exponent
                    .ok_or(CultivatedRestRefusal::PayloadShape)?;
                let right_exponent = descriptor
                    .right_exponent
                    .ok_or(CultivatedRestRefusal::PayloadShape)?;
                let resident_grain = descriptor
                    .resident_grain
                    .ok_or(CultivatedRestRefusal::PayloadShape)?;
                if descriptor.rows == 0
                    || descriptor.columns == 0
                    || rank == 0
                    || bytes.first() != Some(&1)
                    || bytes.len() < cursor
                    || descriptor.entry_octets != 8
                    || resident_grain == 0
                    || u32::from_le_bytes(bytes[1..5].try_into().unwrap()) != resident_grain
                    || i32::from_le_bytes(bytes[5..9].try_into().unwrap()) != left_exponent
                    || i32::from_le_bytes(bytes[9..13].try_into().unwrap()) != right_exponent
                    || bytes[13] != 8
                    || u64::from_le_bytes(bytes[14..22].try_into().unwrap())
                        != descriptor.rows as u64
                    || u64::from_le_bytes(bytes[22..30].try_into().unwrap())
                        != descriptor.columns as u64
                    || u64::from_le_bytes(bytes[30..38].try_into().unwrap()) != rank as u64
                {
                    return Err(CultivatedRestRefusal::PayloadDigestMismatch);
                }
                let count = descriptor.entries as usize;
                let expected = (descriptor.rows as usize)
                    .checked_mul(rank as usize)
                    .and_then(|left| {
                        (rank as usize)
                            .checked_mul(descriptor.columns as usize)
                            .and_then(|right| left.checked_add(right))
                    })
                    .ok_or(CultivatedRestRefusal::PayloadShape)?;
                let expected_octets = count
                    .checked_mul(8)
                    .and_then(|payload| cursor.checked_add(payload))
                    .ok_or(CultivatedRestRefusal::PayloadShape)?;
                if count != expected || bytes.len() != expected_octets {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                let mut values = Vec::with_capacity(count);
                while cursor < bytes.len() {
                    values.push(i64::from_le_bytes(
                        bytes[cursor..cursor + 8].try_into().unwrap(),
                    ));
                    cursor += 8;
                }
                let split = descriptor.rows as usize * rank as usize;
                if values.iter().filter(|value| **value < 0).count() as u64
                    != descriptor.negative_entries
                {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                Ok(Self::AlignedFactor(AlignedFactor {
                    rows: descriptor.rows,
                    columns: descriptor.columns,
                    rank,
                    resident_grain,
                    left_exponent,
                    right_exponent,
                    entry_octets: 8,
                    left: values[..split].to_vec(),
                    right: values[split..].to_vec(),
                }))
            }
            "sparse-delta" => {
                if descriptor.rank.is_some()
                    || descriptor.resident_grain.is_some()
                    || descriptor.left_exponent.is_some()
                    || descriptor.right_exponent.is_some()
                    || descriptor.entry_octets != 8
                    || bytes.len() < 25
                    || bytes.first() != Some(&2)
                    || u64::from_le_bytes(bytes[1..9].try_into().unwrap()) != descriptor.rows as u64
                    || u64::from_le_bytes(bytes[9..17].try_into().unwrap())
                        != descriptor.columns as u64
                    || u64::from_le_bytes(bytes[17..25].try_into().unwrap()) != descriptor.entries
                    || bytes.len() != 25 + descriptor.entries as usize * 16
                {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                let mut entries = Vec::with_capacity(descriptor.entries as usize);
                let mut cursor = 25;
                for _ in 0..descriptor.entries {
                    entries.push(SparseDeltaEntry {
                        index: u64::from_le_bytes(bytes[cursor..cursor + 8].try_into().unwrap()),
                        value: i64::from_le_bytes(
                            bytes[cursor + 8..cursor + 16].try_into().unwrap(),
                        ),
                    });
                    cursor += 16;
                }
                let payload = Self::SparseDelta(SparseDelta {
                    rows: descriptor.rows,
                    columns: descriptor.columns,
                    entries,
                });
                let (descriptor_again, _) = payload.descriptor_and_bytes()?;
                if descriptor_again.negative_entries != descriptor.negative_entries {
                    return Err(CultivatedRestRefusal::PayloadShape);
                }
                Ok(payload)
            }
            _ => Err(CultivatedRestRefusal::PayloadShape),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReconstructionCandidate {
    pub identity: String,
    pub payload_sha256: String,
    pub support: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReconstructionFibre {
    pub candidates: Vec<ReconstructionCandidate>,
    pub omitted_sha256: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactCertificate {
    pub bytes: Vec<u8>,
    pub sha256: String,
}

impl ExactCertificate {
    pub fn from_canonical_bytes(bytes: impl AsRef<[u8]>) -> Self {
        let bytes = bytes.as_ref().to_vec();
        let sha256 = super::digest(&bytes);
        Self { bytes, sha256 }
    }

    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self::from_canonical_bytes(bytes)
    }
    pub fn canonical_bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DerivationAdjointRankReceipt {
    pub derivation: ExactCertificate,
    pub adjoint: ExactCertificate,
    pub rank: ExactCertificate,
}

impl DerivationAdjointRankReceipt {
    pub fn from_derivation(
        derivation: &crate::cultivation_derivation::CultivationDerivation,
        rank_canonical_bytes: impl AsRef<[u8]>,
    ) -> Result<Self, serde_json::Error> {
        Ok(Self {
            derivation: ExactCertificate::from_canonical_bytes(
                derivation.canonical_receipt_bytes()?,
            ),
            adjoint: ExactCertificate::from_canonical_bytes(derivation.canonical_adjoint_bytes()?),
            rank: ExactCertificate::from_canonical_bytes(rank_canonical_bytes),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TargetedAblation {
    pub target: String,
    pub removed_payload_sha256: String,
    pub predecessor: PredecessorProductIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CultivatedRestInput {
    pub predecessor: PredecessorProductIdentity,
    pub codebook_graph: CodebookGraphIdentity,
    pub material_lineage_sha256: String,
    pub ports: Vec<TypedPort>,
    pub laws: Vec<TypedLaw>,
    pub payload: MorphologyPayload,
    pub receipt: DerivationAdjointRankReceipt,
    pub reconstruction_fibre: ReconstructionFibre,
    pub ablation: TargetedAblation,
    /// Authenticated resident runtime choices; the product schema requires this receipt.
    pub runtime_law: RuntimeLawReceipt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RuntimeChart {
    Interval,
    Midpoint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuntimeLawReceipt {
    pub schema: String,
    pub grain: u32,
    pub series_aperture: u32,
    pub band_terms: u32,
    pub vocabulary_extent: u32,
    pub hidden_extent: u32,
    pub rank: u32,
    pub left_population: String,
    pub right_population: String,
    pub chart: RuntimeChart,
    pub fuse: bool,
    pub add_special_tokens: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CultivatedRestRefusal {
    InvalidIdentity(String),
    InvalidDigest(String),
    DuplicatePort(String),
    UnknownPort(String),
    DuplicateLaw(String),
    PayloadShape,
    PayloadDigestMismatch,
    ManifestDigestMismatch,
    WireDecode(String),
    WireSchema(String),
    PredecessorDrift { expected: String, actual: String },
    PredecessorExtent { expected: u64, actual: u64 },
    TrailingOctets,
    DirectoryEscape(String),
    NativeMorphologyUnsupported(String),
}

impl std::fmt::Display for CultivatedRestRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for CultivatedRestRefusal {}
