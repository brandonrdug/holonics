use std::collections::BTreeSet;
use std::io::{Read, Write};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::types::*;
use super::{MANIFEST_DIGEST_OCTETS, NATIVE_REST_PREFIX};
use crate::ported_operation::{PortedOperationComplex, SourceTestimony};
use crate::source_occurrence::{RegionIdentity, SourceOccurrence};

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct NativeRestWire {
    pub(super) schema: String,
    pub(super) source: NativeSourceIdentity,
    pub(super) topology: Vec<NativeTopology>,
    pub(super) populations: Vec<NativePopulationDescriptor>,
    pub(super) laws: Vec<NativeLawIdentity>,
    pub(super) tilings: Vec<NativeOwnerIdentity>,
    pub(super) reductions: Vec<NativeOwnerIdentity>,
    pub(super) correspondence: crate::operation_correspondence::OperationCorrespondenceSeal,
    pub(super) codebook: crate::foreign_codec_rest::ExteriorCodebookRest,
    pub(super) payload_octets: u64,
    pub(super) payload_sha256: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativePopulationDescriptor {
    pub native_name: String,
    pub source: crate::source_occurrence::RegionIdentity,
    pub payload: NativePayloadDescriptor,
}

impl NativePopulationDescriptor {
    pub fn native_name(&self) -> &str {
        &self.native_name
    }

    pub fn source(&self) -> &crate::source_occurrence::RegionIdentity {
        &self.source
    }

    pub fn payload(&self) -> &NativePayloadDescriptor {
        &self.payload
    }

    pub fn exact_extent(&self) -> Option<u64> {
        match self.payload {
            NativePayloadDescriptor::Exact { start, end } => Some(end.saturating_sub(start)),
            NativePayloadDescriptor::Open { .. } => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NativePayloadDescriptor {
    Exact {
        start: u64,
        end: u64,
    },
    Open {
        fibre: crate::ported_operation::CandidateDiagrams,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeRest {
    pub(super) wire: NativeRestWire,
    pub(super) payload: Vec<u8>,
}

impl NativeRest {
    /// Canonical native bytes. `serde_json` emits deterministic object order for the BTreeMap
    /// fields carried by the existing topology and this owner rejects a versioned foreign prefix.
    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, NativeRestRefusal> {
        let mut bytes = Vec::new();
        self.write_native(&mut bytes)?;
        Ok(bytes)
    }

    /// Stream the manifest and raw exact regions without expanding codewords into JSON. This is
    /// the production path for the complete Gemma inventory.
    pub fn write_native<W: Write>(&self, output: &mut W) -> Result<(), NativeRestRefusal> {
        let manifest = serde_json::to_vec(&self.wire)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        output
            .write_all(NATIVE_REST_PREFIX)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        output
            .write_all(&(manifest.len() as u64).to_le_bytes())
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        output
            .write_all(&manifest_digest(&manifest))
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        output
            .write_all(&manifest)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        output
            .write_all(&self.payload)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        Ok(())
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeRestRefusal> {
        if bytes.len() < NATIVE_REST_PREFIX.len()
            || bytes[..NATIVE_REST_PREFIX.len()] != *NATIVE_REST_PREFIX
        {
            return Err(NativeRestRefusal::WirePrefix {
                opened: bytes
                    .iter()
                    .take(NATIVE_REST_PREFIX.len())
                    .copied()
                    .collect(),
            });
        }
        let mut cursor = NATIVE_REST_PREFIX.len();
        if bytes.len() < cursor + 8 {
            return Err(NativeRestRefusal::WireDecode(
                "missing manifest extent".to_owned(),
            ));
        }
        let manifest_len =
            u64::from_le_bytes(bytes[cursor..cursor + 8].try_into().expect("eight bytes")) as usize;
        cursor += 8;
        let digest_end = cursor.checked_add(MANIFEST_DIGEST_OCTETS).ok_or_else(|| {
            NativeRestRefusal::WireDecode("manifest digest extent overflow".to_owned())
        })?;
        if digest_end > bytes.len() {
            return Err(NativeRestRefusal::WireDecode(
                "missing manifest digest".to_owned(),
            ));
        }
        let expected_digest: [u8; MANIFEST_DIGEST_OCTETS] = bytes[cursor..digest_end]
            .try_into()
            .expect("fixed manifest digest extent");
        cursor = digest_end;
        let manifest_end = cursor
            .checked_add(manifest_len)
            .ok_or_else(|| NativeRestRefusal::WireDecode("manifest extent overflow".to_owned()))?;
        if manifest_end > bytes.len() {
            return Err(NativeRestRefusal::WireDecode(
                "manifest exceeds wire".to_owned(),
            ));
        }
        let manifest_bytes = &bytes[cursor..manifest_end];
        validate_manifest_digest(&expected_digest, manifest_bytes)?;
        let wire: NativeRestWire = serde_json::from_slice(manifest_bytes)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        let wire = mount_external_evidence(wire)?;
        let payload = &bytes[manifest_end..];
        if wire.schema != Self::SCHEMA {
            return Err(NativeRestRefusal::WireSchema {
                schema: wire.schema,
            });
        }
        validate_manifest(&wire, payload)?;
        Ok(Self {
            wire,
            payload: payload.to_vec(),
        })
    }

    pub fn read_from<R: Read>(input: &mut R) -> Result<Self, NativeRestRefusal> {
        let mut prefix = vec![0u8; NATIVE_REST_PREFIX.len()];
        input
            .read_exact(&mut prefix)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        if prefix != NATIVE_REST_PREFIX {
            return Err(NativeRestRefusal::WirePrefix { opened: prefix });
        }
        let mut extent = [0u8; 8];
        input
            .read_exact(&mut extent)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        let manifest_len = u64::from_le_bytes(extent) as usize;
        let mut expected_digest = [0u8; MANIFEST_DIGEST_OCTETS];
        input
            .read_exact(&mut expected_digest)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        let mut manifest_bytes = vec![0u8; manifest_len];
        input
            .read_exact(&mut manifest_bytes)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        validate_manifest_digest(&expected_digest, &manifest_bytes)?;
        let wire: NativeRestWire = serde_json::from_slice(&manifest_bytes)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        let wire = mount_external_evidence(wire)?;
        let payload_len = usize::try_from(wire.payload_octets).map_err(|_| {
            NativeRestRefusal::WireDecode("payload extent exceeds this process".to_owned())
        })?;
        let mut payload = vec![0u8; payload_len];
        input
            .read_exact(&mut payload)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?;
        let mut trailing = [0u8; 1];
        if input
            .read(&mut trailing)
            .map_err(|error| NativeRestRefusal::WireDecode(error.to_string()))?
            != 0
        {
            return Err(NativeRestRefusal::WireTrailingOctets);
        }
        validate_manifest(&wire, &payload)?;
        Ok(Self { wire, payload })
    }

    pub fn topology(&self) -> &NativeTopology {
        &self.wire.topology[0]
    }
    pub fn topologies(&self) -> &[NativeTopology] {
        &self.wire.topology
    }
    /// Return the small manifest descriptors. Exact bytes remain owned by this rest and are
    /// never copied merely to enumerate populations.
    pub fn populations(&self) -> &[NativePopulationDescriptor] {
        &self.wire.populations
    }

    pub fn population_descriptor(&self, population: &str) -> Option<&NativePopulationDescriptor> {
        self.wire
            .populations
            .iter()
            .find(|descriptor| descriptor.source.population == population)
    }

    /// Borrow one exact population slice from the rest owner. Open fibres have no bytes and
    /// therefore return `None`; callers can inspect their descriptor separately.
    pub fn population_bytes(&self, population: &str) -> Option<&[u8]> {
        let descriptor = self.population_descriptor(population)?;
        match descriptor.payload {
            NativePayloadDescriptor::Exact { start, end } => {
                Some(&self.payload[start as usize..end as usize])
            }
            NativePayloadDescriptor::Open { .. } => None,
        }
    }
    pub fn laws(&self) -> &[NativeLawIdentity] {
        &self.wire.laws
    }
    /// Resolve a concrete graph through the correspondence registry.  The native rest does not
    /// own a second graph copy: bindings and law identities address this canonical registry.
    pub fn graph(&self, key: &str) -> Option<&NativeGraphIdentity> {
        self.wire
            .correspondence
            .graphs
            .iter()
            .find(|graph| graph.key == key)
    }

    pub fn graphs(&self) -> &[NativeGraphIdentity] {
        &self.wire.correspondence.graphs
    }
    pub fn tilings(&self) -> &[NativeOwnerIdentity] {
        &self.wire.tilings
    }
    pub fn reductions(&self) -> &[NativeOwnerIdentity] {
        &self.wire.reductions
    }
    pub fn correspondence(&self) -> &crate::operation_correspondence::OperationCorrespondenceSeal {
        &self.wire.correspondence
    }
    pub fn codebook(&self) -> &crate::foreign_codec_rest::ExteriorCodebookRest {
        &self.wire.codebook
    }
}

pub(super) fn validate_owner_identities(
    identities: &[NativeOwnerIdentity],
) -> Result<(), NativeRestRefusal> {
    let mut seen = BTreeSet::new();
    for identity in identities {
        if identity.owner.is_empty() || identity.identity.is_empty() {
            return Err(NativeRestRefusal::EmptyIdentity {
                owner: identity.owner.clone(),
            });
        }
        if !seen.insert((&identity.owner, &identity.identity)) {
            return Err(NativeRestRefusal::DuplicateIdentity {
                owner: identity.owner.clone(),
                identity: identity.identity.clone(),
            });
        }
    }
    Ok(())
}

pub(super) fn validate_external_evidence(
    correspondence: &crate::operation_correspondence::OperationCorrespondenceSeal,
    codebook: &crate::foreign_codec_rest::ExteriorCodebookRest,
) -> Result<(), NativeRestRefusal> {
    correspondence
        .validate()
        .map_err(|error| NativeRestRefusal::Correspondence(error.to_string()))?;
    if codebook.codec.is_none() {
        return Err(NativeRestRefusal::Codebook(
            "native rest requires an exterior codec descriptor for source-detached continuation"
                .to_owned(),
        ));
    }
    codebook
        .validate()
        .map_err(|error| NativeRestRefusal::Codebook(error.to_string()))?;
    Ok(())
}

/// Rebuild the non-serialized native-address index after a wire decode. Validation borrows the
/// sealed codebook; a source-detached remount must additionally restore its derived lookup owner
/// without cloning the vocabulary rows.
pub(super) fn mount_external_evidence(
    mut wire: NativeRestWire,
) -> Result<NativeRestWire, NativeRestRefusal> {
    let codebook = crate::foreign_codec_rest::ExteriorCodebookRest::mount(wire.codebook)
        .map_err(|error| NativeRestRefusal::Codebook(error.to_string()))?;
    wire.codebook = codebook;
    validate_external_evidence(&wire.correspondence, &wire.codebook)?;
    Ok(wire)
}

pub(super) fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub(super) fn manifest_digest(bytes: &[u8]) -> [u8; MANIFEST_DIGEST_OCTETS] {
    Sha256::digest(bytes).into()
}

pub(super) fn validate_manifest_digest(
    expected: &[u8; MANIFEST_DIGEST_OCTETS],
    manifest: &[u8],
) -> Result<(), NativeRestRefusal> {
    let actual = manifest_digest(manifest);
    if actual != *expected {
        return Err(NativeRestRefusal::ManifestDigest {
            expected: format_digest(expected),
            actual: format_digest(&actual),
        });
    }
    Ok(())
}

fn format_digest(bytes: &[u8; MANIFEST_DIGEST_OCTETS]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub(super) fn validate_region_digest(
    region: &RegionIdentity,
    bytes: &[u8],
) -> Result<(), NativeRestRefusal> {
    let Some(expected) = &region.sha256 else {
        return Ok(());
    };
    let actual = digest(bytes);
    if actual != *expected {
        return Err(NativeRestRefusal::PopulationDigest {
            population: region.population.clone(),
            expected: expected.clone(),
            actual,
        });
    }
    Ok(())
}

pub(super) fn validate_manifest(
    wire: &NativeRestWire,
    payload: &[u8],
) -> Result<(), NativeRestRefusal> {
    validate_manifest_shape(wire, payload.len() as u64)?;
    let actual = digest(payload);
    if actual != wire.payload_sha256 {
        return Err(NativeRestRefusal::PayloadDigest {
            expected: wire.payload_sha256.clone(),
            actual,
        });
    }
    Ok(())
}

pub(super) fn validate_manifest_shape(
    wire: &NativeRestWire,
    payload_len: u64,
) -> Result<(), NativeRestRefusal> {
    wire.source.validate()?;
    validate_external_evidence(&wire.correspondence, &wire.codebook)?;
    if wire.schema != NativeRest::SCHEMA {
        return Err(NativeRestRefusal::WireSchema {
            schema: wire.schema.clone(),
        });
    }
    if wire.payload_octets != payload_len {
        return Err(NativeRestRefusal::PopulationExtentDiffers {
            population: "<payload>".to_owned(),
            expected: wire.payload_octets as usize,
            supplied: payload_len as usize,
        });
    }
    let mut names = BTreeSet::new();
    let mut native_names = BTreeSet::new();
    let mut previous_end = 0u64;
    for population in &wire.populations {
        if population.native_name.is_empty() || !names.insert(population.source.population.clone())
        {
            return Err(NativeRestRefusal::DuplicatePopulation {
                population: population.source.population.clone(),
            });
        }
        if !native_names.insert(population.native_name.clone()) {
            return Err(NativeRestRefusal::DuplicateNativePopulation {
                native_name: population.native_name.clone(),
            });
        }
        if let NativePayloadDescriptor::Exact { start, end } = &population.payload {
            let start = *start;
            let end = *end;
            let expected = population
                .source
                .end
                .saturating_sub(population.source.start);
            if end < start || end - start != expected || end > payload_len {
                return Err(NativeRestRefusal::PopulationExtentDiffers {
                    population: population.source.population.clone(),
                    expected: expected as usize,
                    supplied: end.saturating_sub(start) as usize,
                });
            }
            if start != previous_end {
                return Err(NativeRestRefusal::WireDecode(
                    "exact population payloads are not contiguous".to_owned(),
                ));
            }
            previous_end = end;
        }
    }
    let correspondence_populations: BTreeSet<&str> = wire
        .correspondence
        .source_populations
        .iter()
        .map(String::as_str)
        .collect();
    for population in &names {
        if !correspondence_populations.contains(population.as_str()) {
            return Err(NativeRestRefusal::CorrespondencePopulationMismatch {
                population: (*population).clone(),
            });
        }
    }
    for population in correspondence_populations {
        if !names.contains(population) {
            return Err(NativeRestRefusal::CorrespondencePopulationMismatch {
                population: population.to_owned(),
            });
        }
    }
    if previous_end != payload_len {
        return Err(NativeRestRefusal::WireDecode(
            "payload contains unaddressed octets".to_owned(),
        ));
    }
    let mut topology_identities = BTreeSet::new();
    for topology in &wire.topology {
        if topology.identity.is_empty() {
            return Err(NativeRestRefusal::EmptyTopology);
        }
        if !topology_identities.insert(topology.identity.as_str()) {
            return Err(NativeRestRefusal::DuplicateTopology {
                identity: topology.identity.clone(),
            });
        }
        for operation in topology.operations.values() {
            if let Some(carrier) = &operation.carrier {
                if !names.contains(carrier) {
                    return Err(NativeRestRefusal::ActivePopulationMissing {
                        population: carrier.clone(),
                    });
                }
            }
        }
    }
    for occurrence in &wire.correspondence.source_operations {
        if !topology_identities.contains(occurrence.source_identity.as_str()) {
            return Err(NativeRestRefusal::TopologyIdentityMissing {
                identity: occurrence.source_identity.clone(),
            });
        }
    }
    let mut law_names = BTreeSet::new();
    let graph_keys: BTreeSet<&str> = wire
        .correspondence
        .graphs
        .iter()
        .map(|graph| graph.key.as_str())
        .collect();
    for law in &wire.laws {
        if law.owner.is_empty()
            || law.graph_identity.is_empty()
            || !law_names.insert(law.law.as_str())
        {
            return Err(NativeRestRefusal::DuplicateIdentity {
                owner: "law".to_owned(),
                identity: law.law.clone(),
            });
        }
        if !graph_keys.contains(law.graph_identity.as_str()) {
            return Err(NativeRestRefusal::GraphIdentityMissing {
                graph_key: law.graph_identity.clone(),
            });
        }
    }
    for topology in &wire.topology {
        for law in topology.shape.laws.values() {
            if !law_names.contains(law.name.as_str()) {
                return Err(NativeRestRefusal::LawIdentityMissing {
                    law: law.name.clone(),
                });
            }
        }
    }
    validate_owner_identities(&wire.tilings)?;
    validate_owner_identities(&wire.reductions)?;
    Ok(())
}

pub(super) fn stream_external<F>(
    locator: &str,
    source: &SourceOccurrence,
    region: &RegionIdentity,
    mut receive: F,
) -> Result<(), NativeRestRefusal>
where
    F: FnMut(&[u8]) -> Result<(), NativeRestRefusal>,
{
    let mut file =
        std::fs::File::open(locator).map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
    let base = 8u64.saturating_add(source.container.header_octets);
    let from = base.saturating_add(region.start);
    let expected = region.end.saturating_sub(region.start);
    let size = file
        .metadata()
        .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?
        .len();
    if from.saturating_add(expected) > size {
        return Err(NativeRestRefusal::PopulationExtentDiffers {
            population: region.population.clone(),
            expected: expected as usize,
            supplied: 0,
        });
    }
    use std::io::Seek;
    file.seek(std::io::SeekFrom::Start(from))
        .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
    let mut remaining = expected as usize;
    let mut chunk = vec![0u8; 1 << 20];
    let mut region_digest = Sha256::new();
    while remaining > 0 {
        let take = remaining.min(chunk.len());
        file.read_exact(&mut chunk[..take])
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        region_digest.update(&chunk[..take]);
        receive(&chunk[..take])?;
        remaining -= take;
    }
    if let Some(expected_digest) = &region.sha256 {
        let actual = format!("{:x}", region_digest.finalize());
        if actual != *expected_digest {
            return Err(NativeRestRefusal::PopulationDigest {
                population: region.population.clone(),
                expected: expected_digest.clone(),
                actual,
            });
        }
    }
    Ok(())
}

/// Consume a ported operation complex into its path-free native rest representation.
///
/// The topology identity is a testimony about the complete foreign complex, so it is computed
/// before the owned fields are moved.  Every other field then crosses by ownership: in particular,
/// operation testimony and candidate fibres are not cloned merely to normalize their source
/// locator-bearing arm.  An implementation testimony retains only its source symbol; the locator
/// is an apparatus path and is deliberately absent from the native rest.
pub(super) fn into_native_topology(complex: PortedOperationComplex) -> NativeTopology {
    let identity = crate::operation_correspondence::topology_identity(&complex);
    let PortedOperationComplex {
        schema: _,
        name,
        shape,
        witness,
        operations,
        undecided,
    } = complex;
    let operations = operations
        .into_iter()
        .map(|(law, operation)| {
            let crate::ported_operation::PortedOperation {
                law: operation_law,
                species,
                carrier,
                testimony,
            } = operation;
            let testimony = testimony
                .into_iter()
                .map(|testimony| match testimony {
                    SourceTestimony::Implementation { symbol, .. } => {
                        NativeTestimony::Implementation { symbol }
                    }
                    SourceTestimony::Configuration { field, value } => {
                        NativeTestimony::Configuration { field, value }
                    }
                    SourceTestimony::DeclaredShape { population, shape } => {
                        NativeTestimony::DeclaredShape { population, shape }
                    }
                    SourceTestimony::AuthoritativeDescription { statement } => {
                        NativeTestimony::AuthoritativeDescription { statement }
                    }
                    SourceTestimony::Intervention { statement } => {
                        NativeTestimony::Intervention { statement }
                    }
                    SourceTestimony::Undecided { question } => {
                        NativeTestimony::Undecided { question }
                    }
                })
                .collect();
            (
                law,
                NativeOperation {
                    law: operation_law,
                    species,
                    carrier,
                    testimony,
                },
            )
        })
        .collect();
    NativeTopology {
        schema: "holonic-engine.native-topology.v1".to_owned(),
        identity,
        name,
        shape,
        witness,
        operations,
        undecided,
    }
}
