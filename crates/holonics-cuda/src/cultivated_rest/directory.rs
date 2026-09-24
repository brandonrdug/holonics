use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::schema::{CultivatedRestRefusal, PredecessorProductIdentity};
use super::wire::CultivatedRest;
use super::{DIRECTORY_SCHEMA, digest};
use crate::foreign_codec_rest::ExteriorCodecArtifact;
use crate::native_occurrence::NativeOccurrence;
use crate::native_rest::MountedNativeRest;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DirectoryManifest {
    pub(crate) schema: String,
    pub(crate) rest: String,
    pub(crate) predecessor: String,
    pub(crate) identity: PredecessorProductIdentity,
    pub(crate) morphology: String,
    pub(crate) codec_companions: Vec<DirectoryCompanion>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DirectoryCompanion {
    pub path: String,
    pub sha256: String,
    pub extent: u64,
}

impl DirectoryCompanion {
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, CultivatedRestRefusal> {
        let path = path.as_ref();
        let identity = PredecessorProductIdentity::from_path(path)?;
        Ok(Self {
            path: path.to_string_lossy().into_owned(),
            sha256: identity.sha256,
            extent: identity.extent,
        })
    }
}

/// The one-path directory mount returned to W4. Paths are authenticated relative members; the
/// product itself retains no locator.
#[derive(Debug)]
pub struct MountedCultivatedRest {
    pub product: CultivatedRest,
    pub(crate) root: PathBuf,
    pub(crate) manifest: DirectoryManifest,
    pub(crate) manifest_identity: PredecessorProductIdentity,
    pub(crate) product_identity: PredecessorProductIdentity,
    pub predecessor_path: PathBuf,
    pub(crate) predecessor: MountedNativeRest,
    pub(crate) predecessor_identity: PredecessorProductIdentity,
    pub morphology_path: PathBuf,
    pub(crate) morphology_identity: PredecessorProductIdentity,
    pub morphology: NativeOccurrence,
    pub tokenizer_paths: Vec<PathBuf>,
    pub(crate) companion_identities: Vec<DirectoryCompanion>,
}

impl MountedCultivatedRest {
    /// The predecessor was mounted and content-authenticated as part of this directory mount.
    pub fn predecessor(&self) -> &MountedNativeRest {
        &self.predecessor
    }

    pub fn product_identity(&self) -> &PredecessorProductIdentity {
        &self.product_identity
    }
    pub fn predecessor_identity(&self) -> &PredecessorProductIdentity {
        &self.predecessor_identity
    }
    pub fn morphology_identity(&self) -> &PredecessorProductIdentity {
        &self.morphology_identity
    }
    pub fn codec_companion_identities(&self) -> &[DirectoryCompanion] {
        &self.companion_identities
    }

    /// Re-authenticate every retained member of the cultivated directory. Changing a path,
    /// digest, or companion population is drift, even if the changed member remains readable.
    pub fn verify_still(&self) -> Result<(), CultivatedRestRefusal> {
        let root = std::fs::canonicalize(&self.root)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        if root != self.root {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "cultivated-rest root drift".to_owned(),
            ));
        }
        let manifest_path = self.root.join("manifest.json");
        let manifest_bytes = std::fs::read(&manifest_path)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        if PredecessorProductIdentity::from_bytes(&manifest_bytes) != self.manifest_identity {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "directory manifest drift".to_owned(),
            ));
        }
        let manifest: DirectoryManifest = serde_json::from_slice(&manifest_bytes)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        if manifest != self.manifest {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "directory manifest changed".to_owned(),
            ));
        }
        let product_path = contained_path(&self.root, &self.manifest.rest)?;
        if PredecessorProductIdentity::from_path(&product_path)? != self.product_identity {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "cultivated product drift".to_owned(),
            ));
        }
        self.predecessor.verify_still().map_err(|error| {
            CultivatedRestRefusal::InvalidIdentity(format!(
                "cultivated predecessor occurrence: {error:?}"
            ))
        })?;
        let predecessor_identity = PredecessorProductIdentity {
            sha256: self.predecessor.content_identity().sha256.clone(),
            extent: self.predecessor.content_identity().extent,
        };
        if predecessor_identity != self.predecessor_identity {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "cultivated predecessor drift".to_owned(),
            ));
        }
        let morphology_path = contained_path(&self.root, &self.manifest.morphology)?;
        if PredecessorProductIdentity::from_path(&morphology_path)? != self.morphology_identity {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "cultivated morphology drift".to_owned(),
            ));
        }
        self.morphology.container.verify_still().map_err(|error| {
            CultivatedRestRefusal::InvalidIdentity(format!(
                "cultivated morphology occurrence: {error:?}"
            ))
        })?;
        if self.manifest.codec_companions != self.companion_identities {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "codec companion declarations changed".to_owned(),
            ));
        }
        for companion in &self.companion_identities {
            let path = contained_path(&self.root, &companion.path)?;
            let identity = PredecessorProductIdentity::from_path(&path)?;
            if identity.sha256 != companion.sha256 || identity.extent != companion.extent {
                return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                    "codec companion {} drift",
                    companion.path
                )));
            }
        }
        Ok(())
    }

    /// Read the W1-declared exterior codec from exactly the directory-declared companions and
    /// authenticate it against the predecessor codebook.
    pub fn exterior_codec_artifact(&self) -> Result<ExteriorCodecArtifact, CultivatedRestRefusal> {
        self.verify_still()?;
        let codebook = self.predecessor.codebook();
        let descriptor = codebook.codec.as_ref().ok_or_else(|| {
            CultivatedRestRefusal::InvalidIdentity(
                "W1 codebook lacks exterior codec descriptor".to_owned(),
            )
        })?;
        let select =
            |digest: &str, extent: u64, kind: &str| -> Result<PathBuf, CultivatedRestRefusal> {
                let matches: Vec<&DirectoryCompanion> = self
                    .companion_identities
                    .iter()
                    .filter(|companion| companion.sha256 == digest && companion.extent == extent)
                    .collect();
                match matches.as_slice() {
                    [] => Err(CultivatedRestRefusal::InvalidIdentity(format!(
                        "missing {kind} codec companion"
                    ))),
                    [companion] => contained_path(&self.root, &companion.path),
                    _ => Err(CultivatedRestRefusal::InvalidIdentity(format!(
                        "ambiguous {kind} codec companions"
                    ))),
                }
            };
        let tokenizer_path = select(
            &descriptor.tokenizer_json_sha256,
            descriptor.tokenizer_json_len,
            "tokenizer.json",
        )?;
        let config_path = match (
            &descriptor.tokenizer_config_sha256,
            descriptor.tokenizer_config_json_len,
        ) {
            (Some(digest), Some(extent)) => Some(select(digest, extent, "tokenizer config")?),
            (None, None) => None,
            _ => {
                return Err(CultivatedRestRefusal::InvalidIdentity(
                    "unpaired W1 codec descriptor".to_owned(),
                ));
            }
        };
        let mut selected = BTreeSet::new();
        selected.insert(tokenizer_path.clone());
        if let Some(path) = &config_path {
            if !selected.insert(path.clone()) {
                return Err(CultivatedRestRefusal::InvalidIdentity(
                    "ambiguous codec companion roles".to_owned(),
                ));
            }
        }
        if selected.len() != self.companion_identities.len() {
            return Err(CultivatedRestRefusal::InvalidIdentity(
                "extra codec companion declaration".to_owned(),
            ));
        }
        let tokenizer = std::fs::read(&tokenizer_path)
            .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
        let config = config_path
            .map(|path| {
                std::fs::read(path)
                    .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))
            })
            .transpose()?;
        let artifact = ExteriorCodecArtifact::from_bytes(tokenizer, config);
        codebook.validate_with_codec(&artifact).map_err(|error| {
            CultivatedRestRefusal::InvalidIdentity(format!("W1 exterior codec: {error:?}"))
        })?;
        self.verify_still()?;
        Ok(artifact)
    }
}

pub(crate) fn contained_path(
    root: &Path,
    relative: &str,
) -> Result<PathBuf, CultivatedRestRefusal> {
    let path = Path::new(relative);
    if path.is_absolute()
        || path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return Err(CultivatedRestRefusal::DirectoryEscape(relative.to_owned()));
    }
    let candidate = std::fs::canonicalize(root.join(path))
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    if !candidate.starts_with(root) {
        return Err(CultivatedRestRefusal::DirectoryEscape(relative.to_owned()));
    }
    Ok(candidate)
}

/// Mount and authenticate a cultivated product directory. The manifest selects exactly one
/// product, one addressed W1 predecessor, one morphology witness and the declared codec
/// companions; no source-model locator is accepted by this boundary.
pub fn mount_directory(
    directory: impl AsRef<Path>,
) -> Result<MountedCultivatedRest, CultivatedRestRefusal> {
    let root = std::fs::canonicalize(directory)
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    let manifest_bytes = std::fs::read(root.join("manifest.json"))
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    let manifest: DirectoryManifest = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    if manifest.schema != DIRECTORY_SCHEMA
        || manifest.rest.is_empty()
        || manifest.predecessor.is_empty()
        || manifest.morphology.is_empty()
    {
        return Err(CultivatedRestRefusal::WireDecode(
            "invalid cultivated-rest directory manifest".to_owned(),
        ));
    }
    let rest_path = contained_path(&root, &manifest.rest)?;
    let predecessor_path = contained_path(&root, &manifest.predecessor)?;
    let morphology_path = contained_path(&root, &manifest.morphology)?;
    let rest_bytes = std::fs::read(&rest_path)
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    let product_identity = PredecessorProductIdentity::from_bytes(&rest_bytes);
    let product = CultivatedRest::read(&rest_bytes)?;
    let predecessor = MountedNativeRest::open(&predecessor_path).map_err(|error| {
        CultivatedRestRefusal::InvalidIdentity(format!("W1 predecessor: {error:?}"))
    })?;
    let actual = PredecessorProductIdentity {
        sha256: predecessor.content_identity().sha256.clone(),
        extent: predecessor.content_identity().extent,
    };
    product.validate_identity(&actual)?;
    let predecessor_graph = serde_json::to_vec(predecessor.graphs())
        .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    if product.codebook_graph().codebook_sha256 != predecessor.codebook().codebook_sha256
        || product.codebook_graph().graph_identity != digest(&predecessor_graph)
    {
        return Err(CultivatedRestRefusal::InvalidIdentity(
            "cultivated product codebook/graph does not match its predecessor".to_owned(),
        ));
    }
    if manifest.identity != product.predecessor().clone() {
        return Err(CultivatedRestRefusal::InvalidIdentity(
            "directory predecessor identity".to_owned(),
        ));
    }
    let predecessor_identity = actual;
    let morphology = NativeOccurrence::read(morphology_path.to_str().ok_or_else(|| {
        CultivatedRestRefusal::WireDecode("morphology path is not unicode".to_owned())
    })?)
    .map_err(|error| CultivatedRestRefusal::WireDecode(error.to_string()))?;
    let witness = product.native_morphology().ok_or_else(|| {
        CultivatedRestRefusal::InvalidIdentity(
            "directory product lacks native morphology witness".to_owned(),
        )
    })?;
    if witness.content_sha256
        != morphology
            .container
            .content_sha256
            .clone()
            .unwrap_or_default()
        || witness.extent != morphology.container.octets
        || witness.header_sha256 != morphology.container.header_sha256
    {
        return Err(CultivatedRestRefusal::InvalidIdentity(
            "directory morphology drift".to_owned(),
        ));
    }
    let morphology_identity = PredecessorProductIdentity::from_path(&morphology_path)?;
    let mut tokenizer_paths = Vec::with_capacity(manifest.codec_companions.len());
    for companion in &manifest.codec_companions {
        let path = contained_path(&root, &companion.path)?;
        let identity = PredecessorProductIdentity::from_path(&path)?;
        if identity.sha256 != companion.sha256 || identity.extent != companion.extent {
            return Err(CultivatedRestRefusal::InvalidIdentity(format!(
                "codec companion {}",
                companion.path
            )));
        }
        tokenizer_paths.push(path);
    }
    Ok(MountedCultivatedRest {
        root,
        manifest_identity: PredecessorProductIdentity::from_bytes(&manifest_bytes),
        product_identity,
        predecessor_identity,
        morphology_identity,
        companion_identities: manifest.codec_companions.clone(),
        manifest,
        product,
        predecessor_path,
        predecessor,
        morphology_path,
        morphology,
        tokenizer_paths,
    })
}
