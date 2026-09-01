//! Read lossless foreign configuration, shard-index, and optional ONNX charts without assigning
//! source names any native role.

use std::{env, fs};

use holonic_engine::native_ecology::holonic_intelligence::{
    ForeignConfigurationChart, ForeignOnnxChart, ShardedWeightIndexChart,
};
use serde_json::json;

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if !(1..=3).contains(&arguments.len()) {
        return Err(
            "usage: inspect_foreign_model_charts_hif2 CONFIG [INDEX] [MODEL_ONNX]".to_owned(),
        );
    }
    let configuration_bytes = fs::read(&arguments[0]).map_err(display)?;
    let configuration =
        ForeignConfigurationChart::read(&arguments[0], configuration_bytes).map_err(display)?;
    let index_address = arguments
        .get(1)
        .filter(|address| !address.ends_with(".onnx"));
    let index = index_address
        .map(|address| {
            fs::read(address)
                .map_err(display)
                .and_then(|bytes| ShardedWeightIndexChart::read(address, bytes).map_err(display))
        })
        .transpose()?;
    let onnx_address = arguments
        .get(2)
        .or_else(|| arguments.get(1).filter(|address| address.ends_with(".onnx")));
    let onnx = onnx_address
        .map(|address| {
            fs::read(address)
                .map_err(display)
                .and_then(|bytes| ForeignOnnxChart::read(address, bytes).map_err(display))
        })
        .transpose()?;
    let receipt = json!({
        "schema":"holonic-engine.foreign-model-chart-inspection.v1",
        "truth_status":"established-bounded; source-inspected; measured",
        "configuration":{
            "address":configuration.address,
            "octets":configuration.raw.len(),
            "root_field_population":configuration.root_fields.len(),
        },
        "sharded_weights":index.as_ref().map(|index| json!({
            "address":index.address,
            "octets":index.raw.len(),
            "declared_weight_octets":index.total_size,
            "tensor_population":index.weight_map.len(),
            "shard_population":index.shards().len(),
        })),
        "onnx":onnx.as_ref().map(|chart| json!({
            "address":chart.address,
            "octets":chart.raw.len(),
            "ir_version":chart.ir_version,
            "graph":chart.graph.name,
            "node_population":chart.graph.nodes.len(),
            "initializer_population":chart.graph.initializers.len(),
            "opset_population":chart.operator_sets.len(),
            "function_population":chart.functions.len(),
            "training_information_population":chart.training_information_population,
        })),
        "source_names_assign_native_roles":false,
        "foreign_executor_reachable":false,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&receipt).map_err(display)?
    );
    Ok(())
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
