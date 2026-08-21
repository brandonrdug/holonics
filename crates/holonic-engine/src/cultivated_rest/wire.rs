use std::collections::BTreeSet;
use std::io::Read;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::directory::{DirectoryCompanion, DirectoryManifest, MountedCultivatedRest};
use super::native_morphology::{NativeMorphologyWitness, hydrate_region_digests};
use super::schema::*;
use super::{
    DIGEST_OCTETS, DIRECTORY_SCHEMA, PREFIX, SCHEMA, canonical_laws_digest, digest, digest_bytes,
    factor_values_bytes, valid_digest,
};
use crate::native_occurrence::NativeOccurrence;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CultivatedRestWire {
    pub(crate) schema: String,
    pub(crate) predecessor: PredecessorProductIdentity,
    pub(crate) codebook_graph: CodebookGraphIdentity,
    pub(crate) material_lineage_sha256: String,
    pub(crate) ports: Vec<TypedPort>,
    pub(crate) laws: Vec<TypedLaw>,
    pub(crate) payload: PayloadDescriptor,
    pub(crate) payload_octets: u64,
    pub(crate) payload_sha256: String,
    pub(crate) receipt: DerivationAdjointRankReceipt,
    pub(crate) reconstruction_fibre: ReconstructionFibre,
    pub(crate) ablation: TargetedAblation,
    pub(crate) native_morphology: Option<NativeMorphologyWitness>,
    pub(crate) runtime_law: RuntimeLawReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CultivatedRest {
    wire: CultivatedRestWire,
    payload: Vec<u8>,
}

impl CultivatedRest {
    pub const SCHEMA: &'static str = SCHEMA;

    pub fn seal(mut input: CultivatedRestInput) -> Result<Self, CultivatedRestRefusal> {
        input.predecessor.validate()?;
        input.codebook_graph.validate()?;
        if !valid_digest(&input.material_lineage_sha256) {
            return Err(CultivatedRestRefusal::InvalidDigest(
                "material lineage".to_owned(),
            ));
        }
        let (payload, payload_bytes) = input.payload.descriptor_and_bytes()?;
        validate_ports_laws(&mut input.ports, &mut input.laws)?;
        validate_fibre(&input.reconstruction_fibre)?;
        validate_receipt(&input.receipt)?;
        if input.ablation.target.is_empty()
            || input.ablation.removed_payload_sha256 != digest(&payload_bytes)
            || input.ablation.predecessor != input.predecessor
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "targeted ablation".to_owned(),
            ));
        }
        let wire = CultivatedRestWire {
            schema: SCHEMA.to_owned(),
            predecessor: input.predecessor,
            codebook_graph: input.codebook_graph,
            material_lineage_sha256: input.material_lineage_sha256,
            ports: input.ports,
            laws: input.laws,
            payload,
            payload_octets: payload_bytes.len() as u64,
            payload_sha256: digest(&payload_bytes),
            receipt: input.receipt,
            reconstruction_fibre: input.reconstruction_fibre,
            ablation: input.ablation,
            native_morphology: None,
            runtime_law: input.runtime_law,
        };
        let rest = Self {
            wire,
            payload: payload_bytes,
        };
        rest.validate(None)?;
        Ok(rest)
    }

    /// Seal only after checking that the supplied predecessor bytes are exactly the declared W1
    /// occurrence.  The bytes are used for authentication and are not retained in the product.
    pub fn seal_authenticated(
        input: CultivatedRestInput,
        predecessor: &[u8],
    ) -> Result<Self, CultivatedRestRefusal> {
        let declared = input.predecessor.clone();
        let actual = PredecessorProductIdentity::from_bytes(predecessor);
        if declared.extent != actual.extent {
            return Err(CultivatedRestRefusal::PredecessorExtent {
                expected: declared.extent,
                actual: actual.extent,
            });
        }
        if declared.sha256 != actual.sha256 {
            return Err(CultivatedRestRefusal::PredecessorDrift {
                expected: declared.sha256,
                actual: actual.sha256,
            });
        }
        Self::seal(input)
    }

    /// Streaming predecessor authentication for the W1-scale file; no predecessor bytes are
    /// buffered or retained.
    pub fn seal_authenticated_path(
        input: CultivatedRestInput,
        predecessor: impl AsRef<Path>,
    ) -> Result<Self, CultivatedRestRefusal> {
        let actual = PredecessorProductIdentity::from_path(predecessor.as_ref())?;
        if input.predecessor != actual {
            if input.predecessor.extent != actual.extent {
                return Err(CultivatedRestRefusal::PredecessorExtent {
                    expected: input.predecessor.extent,
                    actual: actual.extent,
                });
            }
            return Err(CultivatedRestRefusal::PredecessorDrift {
                expected: input.predecessor.sha256,
                actual: actual.sha256,
            });
        }
        Self::seal(input)
    }

    /// Compose the existing native occurrence witness with this product.  The returned wire keeps
    /// only path-free header testimony and does not copy the witness's source file.
    pub fn seal_with_native_occurrence(
        input: CultivatedRestInput,
        occurrence: &NativeOccurrence,
    ) -> Result<Self, CultivatedRestRefusal> {
        let mut rest = Self::seal(input)?;
        let MorphologyPayload::AlignedFactor(factor) = rest.morphology_payload()? else {
            return Err(CultivatedRestRefusal::NativeMorphologyUnsupported(
                "sparse-delta has no exact two-region native binding".to_owned(),
            ));
        };
        let mut witness = NativeMorphologyWitness::from_occurrence(occurrence)?;
        hydrate_region_digests(occurrence, &mut witness)?;
        let left_bytes = factor_values_bytes(&factor.left);
        let right_bytes = factor_values_bytes(&factor.right);
        let left_shape = vec![factor.rows as usize, factor.rank as usize];
        let right_shape = vec![factor.rank as usize, factor.columns as usize];
        let Some(left) = witness.regions.iter().find(|region| {
            region.dtype == "I64"
                && region.shape == left_shape
                && region.sha256.as_deref() == Some(digest(&left_bytes).as_str())
        }) else {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology left factor does not match witness".to_owned(),
            ));
        };
        let Some(right) = witness.regions.iter().find(|region| {
            region.dtype == "I64"
                && region.shape == right_shape
                && region.sha256.as_deref() == Some(digest(&right_bytes).as_str())
        }) else {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "native morphology right factor does not match witness".to_owned(),
            ));
        };
        let constitutive_sha256 = canonical_laws_digest(&rest.wire.laws);
        witness.left_population = left.population.clone();
        witness.right_population = right.population.clone();
        witness.left_sha256 = digest(&left_bytes);
        witness.right_sha256 = digest(&right_bytes);
        witness.left_shape = left_shape;
        witness.right_shape = right_shape;
        witness.left_exponent = factor.left_exponent;
        witness.right_exponent = factor.right_exponent;
        witness.rank = factor.rank;
        witness.resident_grain = factor.resident_grain;
        witness.predecessor_sha256 = rest.wire.predecessor.sha256.clone();
        witness.constitutive_sha256 = constitutive_sha256;
        rest.wire.native_morphology = Some(witness);
        rest.validate(None)?;
        Ok(rest)
    }

    /// Authenticate the product and its immutable predecessor without retaining the predecessor
    /// bytes.  This is the source-detached mount seam used by a `--rest` path.
    pub fn mount(bytes: &[u8], predecessor: &[u8]) -> Result<Self, CultivatedRestRefusal> {
        let rest = Self::read(bytes)?;
        rest.validate(Some(predecessor))?;
        Ok(rest)
    }

    /// Resolve a product path against one immutable W1 base path. Neither locator enters the
    /// returned product or its wire; the base is hashed in bounded chunks.
    pub fn mount_from_paths(
        product: impl AsRef<Path>,
        predecessor: impl AsRef<Path>,
    ) -> Result<Self, CultivatedRestRefusal> {
        let product_bytes = std::fs::read(product)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        let actual = PredecessorProductIdentity::from_path(predecessor.as_ref())?;
        let rest = Self::read(&product_bytes)?;
        rest.validate_identity(&actual)?;
        Ok(rest)
    }

    /// Resolve a product directory from one path. `manifest.json` names only relative files in
    /// that directory; canonicalization rejects absolute paths, `..` escapes, and symlinks which
    /// leave the product root. The directory owner mounts the predecessor once.
    pub fn mount_directory(
        directory: impl AsRef<Path>,
    ) -> Result<MountedCultivatedRest, CultivatedRestRefusal> {
        super::directory::mount_directory(directory)
    }

    /// Emit the small directory manifest which points at an already-existing immutable base;
    /// this does not copy that base. Callers may place the base as a hard link in the directory.
    pub fn write_directory_manifest(
        directory: impl AsRef<Path>,
        rest: &str,
        predecessor: &str,
        morphology: &str,
        codec_companions: Vec<DirectoryCompanion>,
        identity: PredecessorProductIdentity,
    ) -> Result<(), CultivatedRestRefusal> {
        if rest.is_empty()
            || predecessor.is_empty()
            || morphology.is_empty()
            || Path::new(rest).is_absolute()
            || Path::new(predecessor).is_absolute()
            || Path::new(morphology).is_absolute()
            || Path::new(rest)
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir))
            || Path::new(predecessor)
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir))
            || Path::new(morphology)
                .components()
                .any(|component| matches!(component, std::path::Component::ParentDir))
            || identity.validate().is_err()
        {
            return Err(CultivatedRestRefusal::WireDecode(
                "directory manifest requires relative paths and identity".to_owned(),
            ));
        }
        let manifest = DirectoryManifest {
            schema: DIRECTORY_SCHEMA.to_owned(),
            rest: rest.to_owned(),
            predecessor: predecessor.to_owned(),
            identity,
            morphology: morphology.to_owned(),
            codec_companions,
        };
        let bytes = serde_json::to_vec(&manifest)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        std::fs::write(directory.as_ref().join("manifest.json"), bytes)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
    }

    pub fn encode(&self) -> Result<Vec<u8>, CultivatedRestRefusal> {
        let manifest = serde_json::to_vec(&self.wire)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        let mut bytes = Vec::with_capacity(
            PREFIX.len() + 8 + DIGEST_OCTETS + manifest.len() + self.payload.len(),
        );
        bytes.extend_from_slice(PREFIX);
        bytes.extend_from_slice(&(manifest.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&digest_bytes(&manifest));
        bytes.extend_from_slice(&manifest);
        bytes.extend_from_slice(&self.payload);
        Ok(bytes)
    }

    /// The authenticated deterministic JSON manifest, without the exact payload octets.
    pub fn manifest_json(&self) -> Result<Vec<u8>, CultivatedRestRefusal> {
        serde_json::to_vec(&self.wire)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
    }

    /// Write the framed product without requiring a path or retaining one in the product.
    pub fn write_to<W: std::io::Write>(&self, output: &mut W) -> Result<(), CultivatedRestRefusal> {
        output
            .write_all(&self.encode()?)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
    }

    pub fn read_from<R: Read>(input: &mut R) -> Result<Self, CultivatedRestRefusal> {
        let mut bytes = Vec::new();
        input
            .read_to_end(&mut bytes)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        Self::read(&bytes)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, CultivatedRestRefusal> {
        let header = PREFIX.len() + 8 + DIGEST_OCTETS;
        if bytes.len() < header || bytes[..PREFIX.len()] != *PREFIX {
            return Err(CultivatedRestRefusal::WireDecode(
                "wrong cultivated-rest prefix".to_owned(),
            ));
        }
        let manifest_len = usize::try_from(u64::from_le_bytes(
            bytes[PREFIX.len()..PREFIX.len() + 8].try_into().unwrap(),
        ))
        .map_err(|_| CultivatedRestRefusal::WireDecode("manifest too large".to_owned()))?;
        let digest_start = PREFIX.len() + 8;
        let manifest_start = digest_start + DIGEST_OCTETS;
        let manifest_end = manifest_start.checked_add(manifest_len).ok_or_else(|| {
            CultivatedRestRefusal::WireDecode("manifest extent overflow".to_owned())
        })?;
        if manifest_end > bytes.len()
            || digest_bytes(&bytes[manifest_start..manifest_end])
                != bytes[digest_start..manifest_start]
        {
            return Err(CultivatedRestRefusal::ManifestDigestMismatch);
        }
        let wire: CultivatedRestWire = serde_json::from_slice(&bytes[manifest_start..manifest_end])
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        if wire.schema != SCHEMA {
            return Err(CultivatedRestRefusal::WireSchema(wire.schema));
        }
        let payload = bytes[manifest_end..].to_vec();
        if payload.len() as u64 != wire.payload_octets || digest(&payload) != wire.payload_sha256 {
            return Err(CultivatedRestRefusal::PayloadDigestMismatch);
        }
        let rest = Self { wire, payload };
        rest.validate(None)?;
        Ok(rest)
    }

    pub fn predecessor(&self) -> &PredecessorProductIdentity {
        &self.wire.predecessor
    }
    pub fn codebook_graph(&self) -> &CodebookGraphIdentity {
        &self.wire.codebook_graph
    }
    pub fn material_lineage_sha256(&self) -> &str {
        &self.wire.material_lineage_sha256
    }
    pub fn ports(&self) -> &[TypedPort] {
        &self.wire.ports
    }
    pub fn laws(&self) -> &[TypedLaw] {
        &self.wire.laws
    }
    pub fn receipt(&self) -> &DerivationAdjointRankReceipt {
        &self.wire.receipt
    }
    /// The authenticated full derivation bytes remain available to a detached child reader.
    pub fn derivation_receipt_bytes(&self) -> &[u8] {
        self.wire.receipt.derivation.bytes()
    }
    /// The authenticated exact metric adjoint bytes remain available to a detached child reader.
    pub fn adjoint_receipt_bytes(&self) -> &[u8] {
        self.wire.receipt.adjoint.bytes()
    }
    /// The authenticated canonical rank derivation bytes remain available to a detached child reader.
    pub fn rank_receipt_bytes(&self) -> &[u8] {
        self.wire.receipt.rank.bytes()
    }
    pub fn reconstruction_fibre(&self) -> &ReconstructionFibre {
        &self.wire.reconstruction_fibre
    }
    pub fn native_morphology(&self) -> Option<&NativeMorphologyWitness> {
        self.wire.native_morphology.as_ref()
    }
    pub fn runtime_law(&self) -> &RuntimeLawReceipt {
        &self.wire.runtime_law
    }
    pub fn payload_bytes(&self) -> &[u8] {
        &self.payload
    }
    pub fn morphology_payload(&self) -> Result<MorphologyPayload, CultivatedRestRefusal> {
        MorphologyPayload::from_wire(&self.wire.payload, &self.payload)
    }

    /// Receipt accessor: targeted withdrawal names the exact predecessor identity; it does not
    /// claim to conduct restoration, which belongs to the executable W3 deed.
    pub fn ablation_predecessor_identity(&self) -> PredecessorProductIdentity {
        self.wire.ablation.predecessor.clone()
    }

    fn validate(&self, predecessor: Option<&[u8]>) -> Result<(), CultivatedRestRefusal> {
        let runtime = &self.wire.runtime_law;
        if runtime.schema != "holonic-engine.phoenix.runtime-law.v1"
            || runtime.grain == 0
            || runtime.series_aperture == 0
            || runtime.band_terms == 0
            || runtime.vocabulary_extent == 0
            || runtime.hidden_extent == 0
            || runtime.rank == 0
            || runtime.left_population.is_empty()
            || runtime.right_population.is_empty()
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "resident runtime-law receipt".to_owned(),
            ));
        }
        self.wire.predecessor.validate()?;
        self.wire.codebook_graph.validate()?;
        if self.wire.payload_octets != self.payload.len() as u64
            || digest(&self.payload) != self.wire.payload_sha256
        {
            return Err(CultivatedRestRefusal::PayloadDigestMismatch);
        }
        let morphology = MorphologyPayload::from_wire(&self.wire.payload, &self.payload)?;
        if let MorphologyPayload::AlignedFactor(factor) = &morphology {
            if runtime.grain != factor.resident_grain
                || runtime.vocabulary_extent != factor.rows
                || runtime.hidden_extent != factor.columns
                || runtime.rank != factor.rank
            {
                return Err(CultivatedRestRefusal::InvalidIdentity(
                    "runtime-law extents do not bind the resident factor".to_owned(),
                ));
            }
        }
        let mut ports = self.wire.ports.clone();
        let mut laws = self.wire.laws.clone();
        validate_ports_laws(&mut ports, &mut laws)?;
        validate_fibre(&self.wire.reconstruction_fibre)?;
        validate_receipt(&self.wire.receipt)?;
        if self.wire.ablation.predecessor != self.wire.predecessor
            || self.wire.ablation.removed_payload_sha256 != self.wire.payload_sha256
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "targeted ablation".to_owned(),
            ));
        }
        if let Some(bytes) = predecessor {
            self.validate_identity(&PredecessorProductIdentity::from_bytes(bytes))?;
        }
        if let Some(witness) = &self.wire.native_morphology {
            witness.validate()?;
            if let MorphologyPayload::AlignedFactor(factor) = &morphology {
                if witness.resident_grain != factor.resident_grain
                    || witness.left_exponent != factor.left_exponent
                    || witness.right_exponent != factor.right_exponent
                    || witness.rank != factor.rank
                    || witness.left_population != runtime.left_population
                    || witness.right_population != runtime.right_population
                {
                    return Err(CultivatedRestRefusal::InvalidIdentity(
                        "native morphology factor law binding".to_owned(),
                    ));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn validate_identity(
        &self,
        actual: &PredecessorProductIdentity,
    ) -> Result<(), CultivatedRestRefusal> {
        if self.wire.predecessor.extent != actual.extent {
            return Err(CultivatedRestRefusal::PredecessorExtent {
                expected: self.wire.predecessor.extent,
                actual: actual.extent,
            });
        }
        if self.wire.predecessor.sha256 != actual.sha256 {
            return Err(CultivatedRestRefusal::PredecessorDrift {
                expected: self.wire.predecessor.sha256.clone(),
                actual: actual.sha256.clone(),
            });
        }
        Ok(())
    }
}

pub(crate) fn validate_ports_laws(
    ports: &mut Vec<TypedPort>,
    laws: &mut Vec<TypedLaw>,
) -> Result<(), CultivatedRestRefusal> {
    ports.sort_by(|left, right| left.name.cmp(&right.name));
    let mut names = BTreeSet::new();
    for port in ports.iter() {
        if port.name.is_empty()
            || port.carrier.is_empty()
            || port.width == 0
            || matches!(port.octave_bound, OctaveBoundOrigin::Rested(0))
            || matches!(port.rows, ExtentOrigin::Declared(0))
            || !names.insert(port.name.as_str())
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                "port extent {}",
                port.name
            )));
        }
    }
    let mut law_names = BTreeSet::new();
    for law in laws.iter_mut() {
        if law.name.is_empty()
            || !valid_digest(&law.constitutive_digest)
            || !law_names.insert(law.name.as_str())
        {
            return Err(CultivatedRestRefusal::DuplicateLaw(law.name.clone()));
        }
        for list in [&law.inputs, &law.outputs] {
            let mut seen = BTreeSet::new();
            for port in list.iter() {
                if !names.contains(port.as_str()) {
                    return Err(CultivatedRestRefusal::UnknownPort(port.clone()));
                }
                if !seen.insert(port.as_str()) {
                    return Err(CultivatedRestRefusal::DuplicatePort(port.clone()));
                }
            }
        }
        let mut agreements = BTreeSet::new();
        let law_ports: BTreeSet<&str> = law
            .inputs
            .iter()
            .chain(law.outputs.iter())
            .map(String::as_str)
            .collect();
        for agreement in &law.extent_agreements {
            let (left_name, right_name) = agreement.endpoints();
            if left_name == right_name
                || !law_ports.contains(left_name)
                || !law_ports.contains(right_name)
                || !names.contains(left_name)
                || !names.contains(right_name)
                || !agreements.insert((
                    agreement.axis_tag(),
                    left_name.to_owned(),
                    right_name.to_owned(),
                ))
            {
                return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                    "law extent agreement {}",
                    law.name
                )));
            }
            let left = ports
                .iter()
                .find(|port| port.name == left_name)
                .expect("validated port");
            let right = ports
                .iter()
                .find(|port| port.name == right_name)
                .expect("validated port");
            let mismatch = match agreement {
                PortExtentAgreement::Rows { .. } => {
                    matches!((left.rows, right.rows), (ExtentOrigin::Declared(a), ExtentOrigin::Declared(b)) if a != b)
                }
                PortExtentAgreement::Width { .. } => left.width != right.width,
                PortExtentAgreement::OctaveBound { .. } => {
                    matches!((left.octave_bound, right.octave_bound), (OctaveBoundOrigin::Rested(a), OctaveBoundOrigin::Rested(b)) if a != b)
                }
            };
            if mismatch {
                return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                    "law extent mismatch {}",
                    law.name
                )));
            }
        }
    }
    Ok(())
}

fn validate_fibre(fibre: &ReconstructionFibre) -> Result<(), CultivatedRestRefusal> {
    let mut identities = BTreeSet::new();
    for candidate in &fibre.candidates {
        if candidate.identity.is_empty()
            || !valid_digest(&candidate.payload_sha256)
            || !identities.insert(candidate.identity.as_str())
        {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "reconstruction fibre".to_owned(),
            ));
        }
        if candidate.support.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(CultivatedRestRefusal::PayloadShape);
        }
    }
    if let Some(digest) = &fibre.omitted_sha256 {
        if !valid_digest(digest) {
            return Err(CultivatedRestRefusal::InvalidDigest(
                "omitted fibre".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_receipt(receipt: &DerivationAdjointRankReceipt) -> Result<(), CultivatedRestRefusal> {
    for (name, certificate) in [
        ("derivation", &receipt.derivation),
        ("adjoint", &receipt.adjoint),
        ("rank", &receipt.rank),
    ] {
        if certificate.bytes.is_empty()
            || !valid_digest(&certificate.sha256)
            || certificate.sha256 != digest(&certificate.bytes)
        {
            return Err(CultivatedRestRefusal::InvalidDigest(name.to_owned()));
        }
    }
    Ok(())
}
