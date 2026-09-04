use holonic_engine::native_ecology::holonic_intelligence::ForeignOnnxChart;

use super::{MorphologyExportArtifact, MorphologyExportError};
use crate::native_intelligence::{ExportCodecKind, NativeMorphologyArtifact};

const DOMAIN: &str = "org.holonics";
const OPSET: u64 = 1;
const IR_VERSION: u64 = 14;
const MEDIA_TYPE: &str = "application/onnx";
const SCHEMA: &str = "ir14;org.holonics-opset1;native-morphology-v1";
const PACKAGE_TENSOR: &str = "holonics.package.bytes";
const ANATOMY_TENSOR: &str = "holonics.anatomy.bytes";

pub(super) fn exact(
    package: &NativeMorphologyArtifact,
) -> Result<MorphologyExportArtifact, MorphologyExportError> {
    let package_bytes = package.canonical_bytes()?;
    let anatomy = serde_json::to_vec(&package.manifest.anatomy)
        .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    Ok(artifact(model(
        "NativeHolonMorphology",
        vec![(PACKAGE_TENSOR, package_bytes), (ANATOMY_TENSOR, anatomy)],
        "exact",
    )?))
}

pub(super) fn anatomy(
    package: &NativeMorphologyArtifact,
) -> Result<MorphologyExportArtifact, MorphologyExportError> {
    let anatomy = serde_json::to_vec(&package.manifest.anatomy)
        .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    Ok(artifact(model(
        "AnatomyProjection",
        vec![(ANATOMY_TENSOR, anatomy)],
        "projected-anatomy",
    )?))
}

pub(super) fn import_exact(
    artifact: &MorphologyExportArtifact,
) -> Result<NativeMorphologyArtifact, MorphologyExportError> {
    if artifact.media_type != MEDIA_TYPE || artifact.schema_or_opset != SCHEMA {
        return Err(MorphologyExportError::Wire(
            "unknown ONNX morphology schema".to_owned(),
        ));
    }
    let chart = ForeignOnnxChart::read("morphology-export.onnx", artifact.bytes.clone())
        .map_err(|error| MorphologyExportError::Wire(error.to_string()))?;
    if chart.ir_version != IR_VERSION as i64
        || chart.domain != DOMAIN
        || chart.operator_sets.len() != 1
        || chart.operator_sets[0].domain != DOMAIN
        || chart.operator_sets[0].version != OPSET as i64
        || chart.metadata.get("holonics_schema").map(String::as_str) != Some("native-morphology-v1")
    {
        return Err(MorphologyExportError::Wire(
            "ONNX version/domain testimony disagrees".to_owned(),
        ));
    }
    let tensor = chart
        .graph
        .initializers
        .iter()
        .find(|tensor| tensor.name == PACKAGE_TENSOR)
        .ok_or_else(|| MorphologyExportError::Wire("ONNX package initializer absent".to_owned()))?;
    if tensor.data_type != 2
        || tensor.dimensions != [tensor.raw_data.as_ref().map_or(0, |r| r.len()) as u64]
    {
        return Err(MorphologyExportError::Wire(
            "ONNX package initializer type/shape disagrees".to_owned(),
        ));
    }
    let range = tensor
        .raw_data
        .clone()
        .ok_or_else(|| MorphologyExportError::Wire("ONNX package data absent".to_owned()))?;
    NativeMorphologyArtifact::read(&chart.raw[range]).map_err(MorphologyExportError::Package)
}

fn artifact(bytes: Vec<u8>) -> MorphologyExportArtifact {
    MorphologyExportArtifact {
        codec: ExportCodecKind::Onnx,
        media_type: MEDIA_TYPE.to_owned(),
        schema_or_opset: SCHEMA.to_owned(),
        bytes,
    }
}

fn model(
    operation: &str,
    tensors: Vec<(&str, Vec<u8>)>,
    exactness: &str,
) -> Result<Vec<u8>, MorphologyExportError> {
    let input = tensors
        .first()
        .map(|(name, _)| *name)
        .ok_or_else(|| MorphologyExportError::Wire("ONNX tensor family empty".to_owned()))?;
    let output = "holonics.output";
    let mut graph = Vec::new();
    message_field(&mut graph, 1, &node(operation, input, output));
    string_field(&mut graph, 2, "native-morphology");
    for (name, data) in tensors {
        message_field(&mut graph, 5, &tensor(name, &data)?);
    }
    message_field(&mut graph, 11, &value(input));
    message_field(&mut graph, 12, &value(output));

    let mut opset = Vec::new();
    string_field(&mut opset, 1, DOMAIN);
    varint_field(&mut opset, 2, OPSET);

    let mut model = Vec::new();
    varint_field(&mut model, 1, IR_VERSION);
    string_field(&mut model, 2, "holonics");
    string_field(&mut model, 3, "native-morphology-export-v1");
    string_field(&mut model, 4, DOMAIN);
    varint_field(&mut model, 5, 1);
    message_field(&mut model, 7, &graph);
    message_field(&mut model, 8, &opset);
    message_field(
        &mut model,
        14,
        &metadata("holonics_schema", "native-morphology-v1"),
    );
    message_field(&mut model, 14, &metadata("exactness", exactness));
    Ok(model)
}

fn node(operation: &str, input: &str, output: &str) -> Vec<u8> {
    let mut node = Vec::new();
    string_field(&mut node, 1, input);
    string_field(&mut node, 2, output);
    string_field(&mut node, 3, "holonics-native-morphology");
    string_field(&mut node, 4, operation);
    string_field(&mut node, 7, DOMAIN);
    node
}

fn tensor(name: &str, data: &[u8]) -> Result<Vec<u8>, MorphologyExportError> {
    let mut tensor = Vec::new();
    let extent = u64::try_from(data.len())
        .map_err(|_| MorphologyExportError::Wire("ONNX tensor extent overflow".to_owned()))?;
    let mut packed_dimension = Vec::new();
    push_varint(&mut packed_dimension, extent);
    bytes_field(&mut tensor, 1, &packed_dimension);
    varint_field(&mut tensor, 2, 2); // TensorProto.UINT8
    string_field(&mut tensor, 8, name);
    bytes_field(&mut tensor, 9, data);
    Ok(tensor)
}

fn value(name: &str) -> Vec<u8> {
    let mut value = Vec::new();
    string_field(&mut value, 1, name);
    value
}

fn metadata(key: &str, value: &str) -> Vec<u8> {
    let mut metadata = Vec::new();
    string_field(&mut metadata, 1, key);
    string_field(&mut metadata, 2, value);
    metadata
}

fn varint_field(target: &mut Vec<u8>, field: u32, value: u64) {
    push_varint(target, u64::from(field) << 3);
    push_varint(target, value);
}

fn string_field(target: &mut Vec<u8>, field: u32, value: &str) {
    bytes_field(target, field, value.as_bytes());
}

fn message_field(target: &mut Vec<u8>, field: u32, value: &[u8]) {
    bytes_field(target, field, value);
}

fn bytes_field(target: &mut Vec<u8>, field: u32, value: &[u8]) {
    push_varint(target, (u64::from(field) << 3) | 2);
    push_varint(target, value.len() as u64);
    target.extend_from_slice(value);
}

fn push_varint(target: &mut Vec<u8>, mut value: u64) {
    while value >= 0x80 {
        target.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    target.push(value as u8);
}
