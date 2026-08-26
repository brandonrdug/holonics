use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use holonic_engine::native_ecology::inference_ecology::InferenceEcologyRest;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const I5_REST: &str = "output/the_athena_gemma_ecology_infers_returns_and_remounts/native-rest";
const REST_SCHEMA: &str = "holonics.i5.inference-rest-directory.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ComponentIdentity {
    pub role: String,
    pub path: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestDirectory {
    schema: String,
    components: Vec<ComponentIdentity>,
}

pub struct LoadedI5 {
    pub rest: InferenceEcologyRest,
    pub components: Vec<ComponentIdentity>,
    pub accessed_paths: Vec<String>,
}

pub fn load(root: &Path) -> Result<LoadedI5, String> {
    let directory = root.join(I5_REST);
    let manifest_path = directory.join("manifest.json");
    let manifest_bytes = fs::read(&manifest_path).map_err(|error| error.to_string())?;
    let manifest: RestDirectory =
        serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
    if manifest.schema != REST_SCHEMA || manifest.components.len() != 7 {
        return Err("the canonical I5 rest schema or component population moved".to_owned());
    }
    let mut components = BTreeMap::<String, Vec<u8>>::new();
    let mut accessed_paths = vec![format!("{I5_REST}/manifest.json")];
    for identity in &manifest.components {
        let relative = format!("{I5_REST}/{}", identity.path);
        let bytes = fs::read(root.join(&relative)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != identity.octets || digest(&bytes) != identity.sha256 {
            return Err(format!("I5 component {} failed identity", identity.role));
        }
        accessed_paths.push(relative);
        if components.insert(identity.role.clone(), bytes).is_some() {
            return Err("the I5 rest repeats a component role".to_owned());
        }
    }
    let component = |role: &str| {
        components
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("I5 component {role} is absent"))
    };
    let rest = InferenceEcologyRest::read(
        component("recurrent-standing")?,
        component("recurrent-decoder")?,
        component("recurrent-fibres")?,
        component("heterogeneous-standing")?,
        component("heterogeneous-decoder")?,
        component("heterogeneous-fibres")?,
        component("inference-junction")?,
    )
    .map_err(|error| error.to_string())?;
    Ok(LoadedI5 {
        rest,
        components: manifest.components,
        accessed_paths,
    })
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
