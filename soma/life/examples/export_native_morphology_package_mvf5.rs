use std::{collections::BTreeSet, env, error::Error, fs, path::PathBuf};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation, ForeignOnnxChart,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
    BoundaryId, EventId,
};
use life::native_intelligence::{
    consume_dismantling_return, export_morphology, ExactMorphologyExport, ExportCodecKind,
    ExportPurpose, MorphologyExportRequest, MorphologyExportReturn, MorphologyLineage,
    NativeMorphologyPackage,
};
use serde_json::json;

fn main() -> Result<(), Box<dyn Error>> {
    let output = env::args()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: export_native_morphology_package_mvf5 OUTPUT_DIR")?;
    fs::create_dir(&output)?;
    let returned = dismantle(Bf16ExcitationDismantling {
        receiver: ReceiverId(7),
        excitations: vec![ForeignBf16Excitation {
            event: EventId(1),
            predecessor: None,
            entering_boundary: BoundaryId(1),
            emitting_boundary: BoundaryId(2),
            source_occurrence: "cold/export-control".to_owned(),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![0x3f80, 0x0000],
            returned_codewords: vec![0x4000, 0x3f80],
            interventions: BTreeSet::from(["withdraw-control".to_owned()]),
            receiver_consequences: BTreeSet::from(["returned-control".to_owned()]),
        }],
    })?;
    let hot = consume_dismantling_return(returned)?.0;
    let package = NativeMorphologyPackage::found(
        hot,
        MorphologyLineage::origin(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )?;
    let safetensors = exact(&package, ExportCodecKind::Safetensors)?;
    let onnx = exact(&package, ExportCodecKind::Onnx)?;
    fs::write(
        output.join("morphology.safetensors"),
        &safetensors.artifact.bytes,
    )?;
    fs::write(output.join("morphology.onnx"), &onnx.artifact.bytes)?;
    fs::write(
        output.join("morphology.package.json"),
        package.canonical_bytes()?,
    )?;
    let chart = ForeignOnnxChart::read("morphology.onnx", onnx.artifact.bytes.clone())?;
    fs::write(
        output.join("receipt.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "holonics.mvf5.export-control.v1",
            "safetensors": {
                "schema": safetensors.artifact.schema_or_opset,
                "octets": safetensors.artifact.bytes.len(),
                "round_trip": safetensors.complete_package_round_trip,
            },
            "onnx": {
                "schema": onnx.artifact.schema_or_opset,
                "octets": onnx.artifact.bytes.len(),
                "round_trip": onnx.complete_package_round_trip,
                "ir_version": chart.ir_version,
                "domain": chart.domain,
                "opsets": chart.operator_sets.iter().map(|opset| json!({
                    "domain": opset.domain,
                    "version": opset.version,
                })).collect::<Vec<_>>(),
                "nodes": chart.graph.nodes.len(),
                "initializers": chart.graph.initializers.len(),
            }
        }))?,
    )?;
    println!("{}", output.display());
    Ok(())
}

fn exact(
    package: &NativeMorphologyPackage,
    codec: ExportCodecKind,
) -> Result<ExactMorphologyExport, Box<dyn Error>> {
    match export_morphology(
        package,
        MorphologyExportRequest {
            codec,
            receiver_family: BTreeSet::from([ReceiverId(7)]),
            purpose: ExportPurpose::RestedInference,
        },
    )? {
        MorphologyExportReturn::Exact(exact) => Ok(exact),
        returned => Err(format!("exact export refused: {returned:?}").into()),
    }
}
