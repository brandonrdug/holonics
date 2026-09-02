use holonic_engine::native_ecology::holonic_intelligence::{
    ForeignConfigurationChart, ForeignOnnxChart, ShardedWeightIndexChart,
};
use serde_json::json;

use crate::adapters::AdapterReturn;
use crate::runtime::WorkbenchError;
use crate::store;
use crate::SoulkillerCommand;

pub fn execute(command: SoulkillerCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        SoulkillerCommand::Config { path } => {
            let raw = store::read(&path)?;
            let chart = ForeignConfigurationChart::read(path.display().to_string(), raw)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            let fields = chart
                .root_fields
                .iter()
                .map(|field| json!({"name": field.name, "raw_value": field.raw_value}))
                .collect::<Vec<_>>();
            Ok(AdapterReturn::consequence(
                "soulkiller/configuration",
                format!(
                    "retained {} octets and {} lossless root fields; no model executed",
                    chart.raw.len(),
                    chart.root_fields.len()
                ),
                json!({
                    "address": chart.address,
                    "octets": chart.raw.len(),
                    "fields": fields,
                    "foreign_execution": false
                }),
            ))
        }
        SoulkillerCommand::Index { path } => {
            let raw = store::read(&path)?;
            let chart = ShardedWeightIndexChart::read(path.display().to_string(), raw)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            let declarations = chart
                .declaration_order
                .iter()
                .take(32)
                .map(|tensor| json!({"tensor": tensor, "shard": chart.weight_map[tensor]}))
                .collect::<Vec<_>>();
            Ok(AdapterReturn::consequence(
                "soulkiller/shard-index",
                format!(
                    "retained {} tensor declarations over {} shard(s), total size {}",
                    chart.weight_map.len(),
                    chart.shards().len(),
                    chart.total_size
                ),
                json!({
                    "address": chart.address,
                    "octets": chart.raw.len(),
                    "total_size": chart.total_size,
                    "tensor_population": chart.weight_map.len(),
                    "shards": chart.shards(),
                    "first_declarations": declarations,
                    "foreign_execution": false
                }),
            ))
        }
        SoulkillerCommand::Onnx { path } => {
            let raw = store::read(&path)?;
            let chart = ForeignOnnxChart::read(path.display().to_string(), raw)
                .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            let operators = chart
                .graph
                .nodes
                .iter()
                .take(32)
                .map(|node| {
                    json!({
                        "name": node.name,
                        "operation": node.operation,
                        "domain": node.domain,
                        "inputs": node.inputs,
                        "outputs": node.outputs
                    })
                })
                .collect::<Vec<_>>();
            Ok(AdapterReturn::consequence(
                "soulkiller/onnx",
                format!(
                    "retained ONNX IR {} graph with {} node(s) and {} initializer(s); no graph executed",
                    chart.ir_version,
                    chart.graph.nodes.len(),
                    chart.graph.initializers.len()
                ),
                json!({
                    "address": chart.address,
                    "octets": chart.raw.len(),
                    "ir_version": chart.ir_version,
                    "producer": chart.producer_name,
                    "domain": chart.domain,
                    "graph": chart.graph.name,
                    "nodes": chart.graph.nodes.len(),
                    "initializers": chart.graph.initializers.len(),
                    "inputs": chart.graph.inputs.len(),
                    "outputs": chart.graph.outputs.len(),
                    "operator_sets": chart.operator_sets.iter().map(|set| json!({"domain": set.domain, "version": set.version})).collect::<Vec<_>>(),
                    "first_operators": operators,
                    "foreign_execution": false
                }),
            ))
        }
    }
}
