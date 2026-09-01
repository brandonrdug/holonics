use std::collections::BTreeMap;

use serde_json::{json, Map, Value};

use super::{MorphologyExportArtifact, MorphologyExportError};
use crate::native_intelligence::{ExportCodecKind, NativeMorphologyPackage};

const SCHEMA: &str = "holonics.native-morphology.safetensors.v1";
const MEDIA_TYPE: &str = "application/x-safetensors";
const PACKAGE_TENSOR: &str = "holonics.package.bytes";
const ANATOMY_TENSOR: &str = "holonics.anatomy.bytes";

struct Tensor {
    shape: Vec<usize>,
    data: Vec<u8>,
}

pub(super) fn exact(
    package: &NativeMorphologyPackage,
) -> Result<MorphologyExportArtifact, MorphologyExportError> {
    let tensors = BTreeMap::from([
        (
            PACKAGE_TENSOR.to_owned(),
            Tensor {
                shape: vec![package.canonical_bytes()?.len()],
                data: package.canonical_bytes()?,
            },
        ),
        (ANATOMY_TENSOR.to_owned(), anatomy_tensor(package)?),
    ]);
    Ok(artifact(encode(tensors, "exact")?))
}

pub(super) fn anatomy(
    package: &NativeMorphologyPackage,
) -> Result<MorphologyExportArtifact, MorphologyExportError> {
    Ok(artifact(encode(
        BTreeMap::from([(ANATOMY_TENSOR.to_owned(), anatomy_tensor(package)?)]),
        "projected-anatomy",
    )?))
}

pub(super) fn import_exact(
    artifact: &MorphologyExportArtifact,
) -> Result<NativeMorphologyPackage, MorphologyExportError> {
    if artifact.media_type != MEDIA_TYPE || artifact.schema_or_opset != SCHEMA {
        return Err(MorphologyExportError::Wire(
            "unknown Safetensors morphology schema".to_owned(),
        ));
    }
    let package = tensor(&artifact.bytes, PACKAGE_TENSOR)?;
    NativeMorphologyPackage::read(package).map_err(MorphologyExportError::Package)
}

fn anatomy_tensor(package: &NativeMorphologyPackage) -> Result<Tensor, MorphologyExportError> {
    let data = serde_json::to_vec(&package.manifest.anatomy)
        .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    Ok(Tensor {
        shape: vec![data.len()],
        data,
    })
}

fn artifact(bytes: Vec<u8>) -> MorphologyExportArtifact {
    MorphologyExportArtifact {
        codec: ExportCodecKind::Safetensors,
        media_type: MEDIA_TYPE.to_owned(),
        schema_or_opset: SCHEMA.to_owned(),
        bytes,
    }
}

fn encode(
    tensors: BTreeMap<String, Tensor>,
    exactness: &str,
) -> Result<Vec<u8>, MorphologyExportError> {
    let mut header = Map::new();
    header.insert(
        "__metadata__".to_owned(),
        json!({
            "holonics_schema": SCHEMA,
            "exactness": exactness,
            "native_identity": "external-receiver-projection-only"
        }),
    );
    let mut data = Vec::new();
    for (name, tensor) in tensors {
        let begin = data.len();
        data.extend_from_slice(&tensor.data);
        let end = data.len();
        header.insert(
            name,
            json!({
                "dtype": "U8",
                "shape": tensor.shape,
                "data_offsets": [begin, end]
            }),
        );
    }
    let mut header = serde_json::to_vec(&Value::Object(header))
        .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    while header.len() % 8 != 0 {
        header.push(b' ');
    }
    let header_len = u64::try_from(header.len())
        .map_err(|_| MorphologyExportError::Wire("Safetensors header overflow".to_owned()))?;
    let mut bytes = Vec::with_capacity(8 + header.len() + data.len());
    bytes.extend_from_slice(&header_len.to_le_bytes());
    bytes.extend_from_slice(&header);
    bytes.extend_from_slice(&data);
    Ok(bytes)
}

fn tensor<'a>(bytes: &'a [u8], name: &str) -> Result<&'a [u8], MorphologyExportError> {
    let header_len = bytes
        .get(..8)
        .and_then(|bytes| bytes.try_into().ok())
        .map(u64::from_le_bytes)
        .and_then(|length| usize::try_from(length).ok())
        .ok_or_else(|| MorphologyExportError::Wire("truncated Safetensors header".to_owned()))?;
    let header_end = 8usize
        .checked_add(header_len)
        .ok_or_else(|| MorphologyExportError::Wire("Safetensors extent overflow".to_owned()))?;
    let header: Value = serde_json::from_slice(
        bytes
            .get(8..header_end)
            .ok_or_else(|| MorphologyExportError::Wire("truncated Safetensors JSON".to_owned()))?,
    )
    .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    let tensor = header
        .get(name)
        .and_then(Value::as_object)
        .ok_or_else(|| MorphologyExportError::Wire(format!("Safetensors tensor {name} absent")))?;
    if tensor.get("dtype").and_then(Value::as_str) != Some("U8") {
        return Err(MorphologyExportError::Wire(
            "morphology package tensor is not U8".to_owned(),
        ));
    }
    let offsets = tensor
        .get("data_offsets")
        .and_then(Value::as_array)
        .filter(|offsets| offsets.len() == 2)
        .ok_or_else(|| MorphologyExportError::Wire("tensor offsets malformed".to_owned()))?;
    let begin = offsets[0]
        .as_u64()
        .and_then(|offset| usize::try_from(offset).ok())
        .ok_or_else(|| MorphologyExportError::Wire("tensor begin overflow".to_owned()))?;
    let end = offsets[1]
        .as_u64()
        .and_then(|offset| usize::try_from(offset).ok())
        .ok_or_else(|| MorphologyExportError::Wire("tensor end overflow".to_owned()))?;
    bytes
        .get(header_end + begin..header_end + end)
        .ok_or_else(|| MorphologyExportError::Wire("tensor payload truncated".to_owned()))
}
