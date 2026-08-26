//! Process-address table over the authenticated W3 cultivation-material manifest.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::cultivation_material::{CultivationMaterialManifest, MaterialArm};

pub const FIXTURE_SCHEMA: &str = "holonic-engine.phoenix.w3-process-addresses.v1";
const ARMS: [MaterialArm; 6] = [
    MaterialArm::Development,
    MaterialArm::StructuralHeldOut,
    MaterialArm::CodecVariant,
    MaterialArm::SubjectDisjointControl,
    MaterialArm::NoOp,
    MaterialArm::MatchedFoil,
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProcessAddress {
    pub arm: MaterialArm,
    pub material_identity: String,
    pub prompt: Vec<u32>,
    pub target: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixtureManifest {
    pub schema: String,
    pub material_manifest_sha256: String,
    pub codebook_sha256: String,
    pub addresses_sha256: String,
    pub addresses: Vec<ProcessAddress>,
}

/// Digest the canonical address table, independent of JSON whitespace or array placement.
pub fn canonical_addresses_sha256(addresses: &[ProcessAddress]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"holonic-engine.phoenix.w3-addresses.v1");
    for address in addresses {
        hasher.update([address.arm as u8]);
        frame(&mut hasher, address.material_identity.as_bytes());
        hasher.update((address.prompt.len() as u64).to_le_bytes());
        for token in &address.prompt {
            hasher.update(token.to_le_bytes());
        }
        match address.target {
            Some(target) => {
                hasher.update([1]);
                hasher.update(target.to_le_bytes());
            }
            None => hasher.update([0]),
        }
    }
    format!("{:x}", hasher.finalize())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn process_prompt(arm: MaterialArm, token_ids: &[u32]) -> Vec<u32> {
    let _ = arm;
    if token_ids.is_empty() {
        Vec::new()
    } else {
        token_ids[..token_ids.len() - 1].to_vec()
    }
}

fn process_target(arm: MaterialArm, token_ids: &[u32]) -> Option<u32> {
    let _ = arm;
    token_ids.last().copied()
}

fn validate_shape(fixture: &FixtureManifest) -> Result<(), String> {
    if fixture.schema != FIXTURE_SCHEMA || fixture.addresses.len() != ARMS.len() {
        return Err("W3 process-address fixture schema refused".to_owned());
    }
    if fixture.material_manifest_sha256.len() != 64
        || !fixture
            .material_manifest_sha256
            .chars()
            .all(|c| c.is_ascii_hexdigit())
        || fixture.codebook_sha256.len() != 64
        || !fixture
            .codebook_sha256
            .chars()
            .all(|c| c.is_ascii_hexdigit())
        || fixture.addresses.iter().any(|address| {
            address.material_identity.len() != 64
                || !address
                    .material_identity
                    .chars()
                    .all(|c| c.is_ascii_hexdigit())
        })
    {
        return Err("W3 process-address fixture digest refused".to_owned());
    }
    if ARMS.iter().any(|arm| {
        fixture
            .addresses
            .iter()
            .filter(|address| address.arm == *arm)
            .count()
            != 1
    }) {
        return Err("W3 process-address fixture must carry exactly one address per arm".to_owned());
    }
    if fixture.addresses_sha256 != canonical_addresses_sha256(&fixture.addresses) {
        return Err("W3 process-address address digest refused".to_owned());
    }
    Ok(())
}

pub fn from_material_manifest(
    manifest: &CultivationMaterialManifest,
) -> Result<FixtureManifest, String> {
    manifest.validate().map_err(|error| error.to_string())?;
    let mut addresses = Vec::new();
    for arm in ARMS {
        let entry = manifest
            .entries
            .iter()
            .find(|entry| entry.arm == arm)
            .ok_or_else(|| format!("material arm {arm:?} absent"))?;
        let target = process_target(arm, &entry.token_ids);
        let prompt = process_prompt(arm, &entry.token_ids);
        addresses.push(ProcessAddress {
            arm,
            material_identity: entry.identity.clone(),
            prompt,
            target,
        });
    }
    let fixture = FixtureManifest {
        schema: FIXTURE_SCHEMA.to_owned(),
        material_manifest_sha256: manifest.manifest_sha256.clone(),
        codebook_sha256: manifest.w1_codebook_sha256.clone(),
        addresses_sha256: canonical_addresses_sha256(&addresses),
        addresses,
    };
    fixture.validate_against(manifest)?;
    Ok(fixture)
}

impl FixtureManifest {
    /// Bind every serialized process address back to the authenticated material entry.
    pub fn validate_against(&self, manifest: &CultivationMaterialManifest) -> Result<(), String> {
        validate_shape(self)?;
        manifest.validate().map_err(|error| error.to_string())?;
        if self.material_manifest_sha256 != manifest.manifest_sha256
            || self.codebook_sha256 != manifest.w1_codebook_sha256
        {
            return Err(
                "W3 process-address fixture does not name this material manifest".to_owned(),
            );
        }
        for arm in ARMS {
            let address = self
                .addresses
                .iter()
                .find(|address| address.arm == arm)
                .ok_or_else(|| format!("fixture arm {arm:?} absent"))?;
            let entry = manifest
                .entries
                .iter()
                .find(|entry| entry.arm == arm)
                .ok_or_else(|| format!("material arm {arm:?} absent"))?;
            let target = process_target(arm, &entry.token_ids);
            let prompt = process_prompt(arm, &entry.token_ids);
            if address.material_identity != entry.identity
                || address.prompt != prompt
                || address.target != target
            {
                return Err(format!(
                    "W3 process address for {arm:?} does not match material"
                ));
            }
        }
        Ok(())
    }
}

pub fn write(path: impl AsRef<std::path::Path>, fixture: &FixtureManifest) -> Result<(), String> {
    validate_shape(fixture)?;
    std::fs::write(
        path,
        serde_json::to_vec(fixture).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

pub fn read(path: impl AsRef<std::path::Path>) -> Result<FixtureManifest, String> {
    let fixture: FixtureManifest =
        serde_json::from_slice(&std::fs::read(path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    validate_shape(&fixture)?;
    Ok(fixture)
}

/// Address selection is by the authenticated material arm, never by serialized position.
pub fn address_for(fixture: &FixtureManifest, arm: MaterialArm) -> Result<&ProcessAddress, String> {
    fixture
        .addresses
        .iter()
        .find(|address| address.arm == arm)
        .ok_or_else(|| format!("W3 process address for {arm:?} is absent"))
}
