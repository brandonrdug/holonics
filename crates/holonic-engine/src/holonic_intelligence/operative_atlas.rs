//! The complete source-neutral text-operator ecology returned from one inherited realization.
//!
//! The source dismantler below may read foreign names in order to recover the graph.  Its hot
//! return contains only native ordinals, symbolic carrier axes, generic mathematical operations,
//! coefficient populations, chronology, and explicit obstructions.  In particular, a coefficient
//! present in the source container but absent from the source's configured operation is retained as
//! an obstruction rather than silently dropped or assigned an invented use.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use thiserror::Error;

use crate::{
    foreign_map::{ForeignDtype, ForeignMapError, manifest_safetensors},
    resident_law::decimal_to_rat,
};

pub const NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA: &str =
    "holonic-engine.native-full-operator-ecology.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct NativeTensorOrdinal(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct NativeCarrierOrdinal(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeCarrierAxis {
    Occurrence,
    Fixed(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCarrierChart {
    pub ordinal: NativeCarrierOrdinal,
    pub axes: Vec<NativeCarrierAxis>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCoefficientPopulation {
    pub ordinal: NativeTensorOrdinal,
    pub shape: Vec<usize>,
    pub coefficient_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeScaleConstraint {
    Bfloat16NearestSquareRootOf(u32),
    ReciprocalSquareRootOf(u32),
    Rational { numerator: i64, denominator: u64 },
    Coefficient,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeCausalReach {
    Window(usize),
    Complete,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeOperationPrimitive {
    Lookup {
        scale: NativeScaleConstraint,
    },
    Reshape,
    Select {
        axis: usize,
        at: usize,
    },
    Contract,
    RmsRebase {
        group: usize,
        epsilon: Rat,
        has_gain: bool,
    },
    RotaryChronology {
        theta: u64,
        head_width: usize,
        rotated_width: usize,
    },
    CausalContact {
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        reach: NativeCausalReach,
        series_terms: u32,
    },
    GeluTanh,
    Hadamard,
    Add,
    Scale {
        by: NativeScaleConstraint,
    },
    Tanh,
    Emit,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorNode {
    pub ordinal: u32,
    pub layer: Option<u16>,
    pub primitive: NativeOperationPrimitive,
    pub inputs: Vec<NativeCarrierOrdinal>,
    pub output: NativeCarrierOrdinal,
    pub coefficients: Vec<NativeTensorOrdinal>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeAttentionTopology {
    Local,
    Global,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeKvStanding {
    Own,
    SharedFrom { layer: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeLayerTopology {
    pub ordinal: u16,
    pub attention: NativeAttentionTopology,
    pub kv_standing: NativeKvStanding,
    pub first_operation: u32,
    pub operation_population: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeCoefficientObstructionKind {
    DeclaredButUnreachedBySharedStanding { owner_layer: u16 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCoefficientObstruction {
    pub population: NativeTensorOrdinal,
    pub layer: u16,
    pub kind: NativeCoefficientObstructionKind,
}

/// One complete hot operator ecology.  It carries no source path or tensor name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFullOperatorEcology {
    pub schema: String,
    pub shared_carrier_extent: usize,
    pub coefficient_populations: Vec<NativeCoefficientPopulation>,
    pub carriers: Vec<NativeCarrierChart>,
    pub operations: Vec<NativeOperatorNode>,
    pub layers: Vec<NativeLayerTopology>,
    pub coefficient_obstructions: Vec<NativeCoefficientObstruction>,
}

impl NativeFullOperatorEcology {
    pub fn validate(&self) -> Result<(), NativeFullOperatorError> {
        if self.schema != NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA
            || self.shared_carrier_extent == 0
            || self.coefficient_populations.is_empty()
            || self.carriers.is_empty()
            || self.operations.is_empty()
            || self.layers.is_empty()
        {
            return Err(NativeFullOperatorError::Malformed("empty ecology"));
        }
        for (at, population) in self.coefficient_populations.iter().enumerate() {
            if population.ordinal != NativeTensorOrdinal(at as u32)
                || population.shape.is_empty()
                || population.shape.contains(&0)
                || population.coefficient_population
                    != product(&population.shape).ok_or(NativeFullOperatorError::Extent)?
            {
                return Err(NativeFullOperatorError::Malformed("coefficient population"));
            }
        }
        for (at, carrier) in self.carriers.iter().enumerate() {
            if carrier.ordinal != NativeCarrierOrdinal(at as u32)
                || carrier.axes.is_empty()
                || carrier
                    .axes
                    .iter()
                    .any(|axis| matches!(axis, NativeCarrierAxis::Fixed(0)))
            {
                return Err(NativeFullOperatorError::Malformed("carrier chart"));
            }
        }
        let mut produced = BTreeSet::new();
        let mut used = BTreeSet::new();
        for (at, operation) in self.operations.iter().enumerate() {
            // These are the actual ports consumed by the resident primitive owner. Refuse a
            // malformed artifact before an unchecked input/parameter index can reach the device.
            let (inputs, coefficients) = match &operation.primitive {
                NativeOperationPrimitive::Lookup { .. } => (0, 1),
                NativeOperationPrimitive::Contract => (1, 1),
                NativeOperationPrimitive::RmsRebase { has_gain, .. } => (1, usize::from(*has_gain)),
                NativeOperationPrimitive::Scale { by: NativeScaleConstraint::Coefficient } => (1, 1),
                NativeOperationPrimitive::Add | NativeOperationPrimitive::Hadamard => (2, 0),
                NativeOperationPrimitive::CausalContact { .. } => (3, 0),
                _ => (1, 0),
            };
            if operation.inputs.len() != inputs || operation.coefficients.len() != coefficients {
                return Err(NativeFullOperatorError::Malformed("operator port arity"));
            }
            if operation.ordinal != at as u32
                || operation.output.0 as usize >= self.carriers.len()
                || !produced.insert(operation.output)
                || operation.inputs.iter().any(|input| {
                    input.0 as usize >= self.carriers.len() || input.0 >= operation.output.0
                })
                || operation
                    .coefficients
                    .iter()
                    .any(|population| population.0 as usize >= self.coefficient_populations.len())
            {
                return Err(NativeFullOperatorError::Malformed("operator occurrence"));
            }
            used.extend(operation.coefficients.iter().copied());
        }
        let mut first = self.layers[0].first_operation;
        if first as usize > self.operations.len() {
            return Err(NativeFullOperatorError::Malformed("operator prefix extent"));
        }
        if self.operations[..first as usize]
            .iter()
            .any(|operation| operation.layer.is_some())
        {
            return Err(NativeFullOperatorError::Malformed("operator prefix"));
        }
        for (at, layer) in self.layers.iter().enumerate() {
            let end = layer.first_operation.checked_add(layer.operation_population)
                .ok_or(NativeFullOperatorError::Malformed("layer extent overflow"))?;
            if layer.ordinal != at as u16
                || layer.first_operation != first
                || layer.operation_population == 0
                || end as usize > self.operations.len()
                || self.operations[layer.first_operation as usize
                    ..end as usize]
                    .iter()
                    .any(|operation| operation.layer != Some(layer.ordinal))
            {
                return Err(NativeFullOperatorError::Malformed("layer topology"));
            }
            first = end;
        }
        if self.operations[first as usize..]
            .iter()
            .any(|operation| operation.layer.is_some())
        {
            return Err(NativeFullOperatorError::Malformed("operator suffix"));
        }
        let mut obstructed = BTreeSet::new();
        for obstruction in &self.coefficient_obstructions {
            if obstruction.population.0 as usize >= self.coefficient_populations.len()
                || used.contains(&obstruction.population)
                || !obstructed.insert(obstruction.population)
                || obstruction.layer as usize >= self.layers.len()
            {
                return Err(NativeFullOperatorError::Malformed(
                    "coefficient obstruction",
                ));
            }
        }
        if used.len() + obstructed.len() != self.coefficient_populations.len()
            || (0..self.coefficient_populations.len()).any(|at| {
                let ordinal = NativeTensorOrdinal(at as u32);
                !used.contains(&ordinal) && !obstructed.contains(&ordinal)
            })
        {
            return Err(NativeFullOperatorError::Malformed("coefficient coverage"));
        }
        Ok(())
    }

    pub fn operative_coefficient_population(&self) -> usize {
        self.coefficient_populations.len() - self.coefficient_obstructions.len()
    }

    pub fn coefficient_octets(&self) -> Result<u64, NativeFullOperatorError> {
        self.coefficient_populations
            .iter()
            .try_fold(0u64, |sum, population| {
                sum.checked_add(
                    population
                        .coefficient_population
                        .checked_mul(2)
                        .ok_or(NativeFullOperatorError::Extent)?,
                )
                .ok_or(NativeFullOperatorError::Extent)
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorColdPopulation {
    pub ordinal: NativeTensorOrdinal,
    pub source_name: String,
    pub source_start: u64,
    pub source_end: u64,
}

/// Source coordinates remain physically separate from the hot ecology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFullOperatorColdWitness {
    pub source_container: String,
    pub source_configuration: String,
    pub payload_base: u64,
    pub populations: Vec<NativeOperatorColdPopulation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeFullOperatorDismantlingReturn {
    pub native: NativeFullOperatorEcology,
    pub exterior: NativeFullOperatorColdWitness,
}

#[derive(Debug, Error)]
pub enum NativeFullOperatorError {
    #[error("foreign container: {0}")]
    Foreign(#[from] ForeignMapError),
    #[error("source I/O: {0}")]
    Io(String),
    #[error("the source configuration is malformed at {0}")]
    Configuration(&'static str),
    #[error("the source operator is missing {0}")]
    Missing(String),
    #[error("the source operator population has an unexpected shape")]
    Shape,
    #[error("an operator extent overflowed its exact integer carrier")]
    Extent,
    #[error("the native operator ecology is malformed at {0}")]
    Malformed(&'static str),
}

struct GraphBuilder {
    carriers: Vec<NativeCarrierChart>,
    operations: Vec<NativeOperatorNode>,
}

impl GraphBuilder {
    fn push(
        &mut self,
        layer: Option<u16>,
        primitive: NativeOperationPrimitive,
        inputs: Vec<NativeCarrierOrdinal>,
        axes: Vec<NativeCarrierAxis>,
        coefficients: Vec<NativeTensorOrdinal>,
    ) -> NativeCarrierOrdinal {
        let output = NativeCarrierOrdinal(self.carriers.len() as u32);
        self.carriers.push(NativeCarrierChart {
            ordinal: output,
            axes,
        });
        self.operations.push(NativeOperatorNode {
            ordinal: self.operations.len() as u32,
            layer,
            primitive,
            inputs,
            output,
            coefficients,
        });
        output
    }
}

/// Dismantle the complete configured text operation into a name-free native graph while retaining
/// every source-declared text coefficient population, including populations the source executor
/// itself leaves unreachable.
pub fn dismantle_full_native_operator(
    root: &Path,
) -> Result<NativeFullOperatorDismantlingReturn, NativeFullOperatorError> {
    let container_path = root.join("model.safetensors");
    let (_, container) = manifest_safetensors(
        container_path
            .to_str()
            .ok_or_else(|| NativeFullOperatorError::Io("non-text path".to_owned()))?,
    )?;
    let configuration_path = root.join("config.json");
    let configuration = fs::read_to_string(&configuration_path)
        .map_err(|error| NativeFullOperatorError::Io(error.to_string()))?;
    let json: Value = serde_json::from_str(&configuration)
        .map_err(|_| NativeFullOperatorError::Configuration("root"))?;
    let text = json
        .get("text_config")
        .and_then(Value::as_object)
        .ok_or(NativeFullOperatorError::Configuration("text_config"))?;

    let hidden = usize_field(text, "hidden_size")?;
    let layers = usize_field(text, "num_hidden_layers")?;
    let heads = usize_field(text, "num_attention_heads")?;
    let kv_heads = usize_field(text, "num_key_value_heads")?;
    let local_head = usize_field(text, "head_dim")?;
    let global_head = usize_field(text, "global_head_dim")?;
    let intermediate = usize_field(text, "intermediate_size")?;
    let per_layer = usize_field(text, "hidden_size_per_layer_input")?;
    let shared_layers = usize_field(text, "num_kv_shared_layers")?;
    let sliding_window = usize_field(text, "sliding_window")?;
    let vocabulary = usize_field(text, "vocab_size")?;
    let per_layer_vocabulary = usize_field(text, "vocab_size_per_layer_input")?;
    if bool_field(text, "enable_moe_block")?
        || bool_field(text, "use_double_wide_mlp")?
        || bool_field(text, "attention_k_eq_v")?
        || layers == 0
        || shared_layers > layers
    {
        return Err(NativeFullOperatorError::Configuration(
            "configured dense operator",
        ));
    }
    let layer_types = text
        .get("layer_types")
        .and_then(Value::as_array)
        .ok_or(NativeFullOperatorError::Configuration("layer_types"))?;
    if layer_types.len() != layers {
        return Err(NativeFullOperatorError::Configuration("layer_types"));
    }
    let epsilon = decimal_to_rat(
        &text
            .get("rms_norm_eps")
            .ok_or(NativeFullOperatorError::Configuration("rms_norm_eps"))?
            .to_string(),
    )
    .ok_or(NativeFullOperatorError::Configuration("rms_norm_eps"))?;
    let final_cap = text
        .get("final_logit_softcapping")
        .and_then(integral_number)
        .ok_or(NativeFullOperatorError::Configuration(
            "final_logit_softcapping",
        ))?;
    let rope = text
        .get("rope_parameters")
        .and_then(Value::as_object)
        .ok_or(NativeFullOperatorError::Configuration("rope_parameters"))?;
    let local_theta = rope_theta(rope, "sliding_attention")?;
    let global_theta = rope_theta(rope, "full_attention")?;
    let global_partial = rope
        .get("full_attention")
        .and_then(Value::as_object)
        .and_then(|value| value.get("partial_rotary_factor"))
        .map(Value::to_string)
        .filter(|value| value == "0.25")
        .ok_or(NativeFullOperatorError::Configuration(
            "partial_rotary_factor",
        ))?;
    drop(global_partial);

    let source = container
        .tensors
        .values()
        .filter(|tensor| tensor.name.starts_with("model.language_model."))
        .collect::<Vec<_>>();
    if source.is_empty() {
        return Err(NativeFullOperatorError::Missing(
            "text coefficient population".to_owned(),
        ));
    }
    let mut ordinals = BTreeMap::new();
    let mut coefficient_populations = Vec::with_capacity(source.len());
    let mut cold = Vec::with_capacity(source.len());
    for (at, tensor) in source.iter().enumerate() {
        if tensor.dtype != ForeignDtype::Bf16 || tensor.extent_agrees() != Some(true) {
            return Err(NativeFullOperatorError::Shape);
        }
        let ordinal = NativeTensorOrdinal(at as u32);
        ordinals.insert(tensor.name.as_str(), ordinal);
        coefficient_populations.push(NativeCoefficientPopulation {
            ordinal,
            shape: tensor.shape.clone(),
            coefficient_population: tensor.elements().ok_or(NativeFullOperatorError::Extent)?,
        });
        cold.push(NativeOperatorColdPopulation {
            ordinal,
            source_name: tensor.name.clone(),
            source_start: tensor.start,
            source_end: tensor.end,
        });
    }
    let tensor = |name: &str| {
        ordinals
            .get(name)
            .copied()
            .ok_or_else(|| NativeFullOperatorError::Missing(name.to_owned()))
    };
    let require_shape = |ordinal: NativeTensorOrdinal, expected: &[usize]| {
        if coefficient_populations[ordinal.0 as usize].shape == expected {
            Ok(())
        } else {
            Err(NativeFullOperatorError::Shape)
        }
    };
    let occurrence = NativeCarrierAxis::Occurrence;
    let fixed = NativeCarrierAxis::Fixed;
    let mut graph = GraphBuilder {
        carriers: Vec::new(),
        operations: Vec::new(),
    };

    let main_embedding = tensor("model.language_model.embed_tokens.weight")?;
    require_shape(main_embedding, &[vocabulary, hidden])?;
    let mut hidden_state = graph.push(
        None,
        NativeOperationPrimitive::Lookup {
            scale: NativeScaleConstraint::Bfloat16NearestSquareRootOf(hidden as u32),
        },
        vec![],
        vec![occurrence.clone(), fixed(hidden)],
        vec![main_embedding],
    );

    let per_layer_embedding = tensor("model.language_model.embed_tokens_per_layer.weight")?;
    require_shape(
        per_layer_embedding,
        &[per_layer_vocabulary, layers * per_layer],
    )?;
    let per_layer_identity_flat = graph.push(
        None,
        NativeOperationPrimitive::Lookup {
            scale: NativeScaleConstraint::Bfloat16NearestSquareRootOf(per_layer as u32),
        },
        vec![],
        vec![occurrence.clone(), fixed(layers * per_layer)],
        vec![per_layer_embedding],
    );
    let per_layer_identity = graph.push(
        None,
        NativeOperationPrimitive::Reshape,
        vec![per_layer_identity_flat],
        vec![occurrence.clone(), fixed(layers), fixed(per_layer)],
        vec![],
    );
    let model_projection = tensor("model.language_model.per_layer_model_projection.weight")?;
    require_shape(model_projection, &[layers * per_layer, hidden])?;
    let projected_flat = graph.push(
        None,
        NativeOperationPrimitive::Contract,
        vec![hidden_state],
        vec![occurrence.clone(), fixed(layers * per_layer)],
        vec![model_projection],
    );
    let projected_flat = graph.push(
        None,
        NativeOperationPrimitive::Scale {
            by: NativeScaleConstraint::ReciprocalSquareRootOf(hidden as u32),
        },
        vec![projected_flat],
        vec![occurrence.clone(), fixed(layers * per_layer)],
        vec![],
    );
    let projected = graph.push(
        None,
        NativeOperationPrimitive::Reshape,
        vec![projected_flat],
        vec![occurrence.clone(), fixed(layers), fixed(per_layer)],
        vec![],
    );
    let projection_norm = tensor("model.language_model.per_layer_projection_norm.weight")?;
    require_shape(projection_norm, &[per_layer])?;
    let projected = graph.push(
        None,
        NativeOperationPrimitive::RmsRebase {
            group: per_layer,
            epsilon: epsilon.clone(),
            has_gain: true,
        },
        vec![projected],
        vec![occurrence.clone(), fixed(layers), fixed(per_layer)],
        vec![projection_norm],
    );
    let per_layer_inputs = graph.push(
        None,
        NativeOperationPrimitive::Add,
        vec![projected, per_layer_identity],
        vec![occurrence.clone(), fixed(layers), fixed(per_layer)],
        vec![],
    );
    let per_layer_inputs = graph.push(
        None,
        NativeOperationPrimitive::Scale {
            by: NativeScaleConstraint::ReciprocalSquareRootOf(2),
        },
        vec![per_layer_inputs],
        vec![occurrence.clone(), fixed(layers), fixed(per_layer)],
        vec![],
    );

    let first_shared = layers - shared_layers;
    let mut latest_local_kv: Option<(usize, NativeCarrierOrdinal, NativeCarrierOrdinal)> = None;
    let mut latest_global_kv: Option<(usize, NativeCarrierOrdinal, NativeCarrierOrdinal)> = None;
    let mut layer_topologies = Vec::with_capacity(layers);
    let mut coefficient_obstructions = Vec::new();

    for layer in 0..layers {
        let layer_u16 = u16::try_from(layer).map_err(|_| NativeFullOperatorError::Extent)?;
        let first_operation = graph.operations.len() as u32;
        let kind = layer_types[layer]
            .as_str()
            .ok_or(NativeFullOperatorError::Configuration("layer_types"))?;
        let (attention, head_width, theta, rotated_width, reach) = match kind {
            "sliding_attention" => (
                NativeAttentionTopology::Local,
                local_head,
                local_theta,
                local_head,
                NativeCausalReach::Window(sliding_window),
            ),
            "full_attention" => (
                NativeAttentionTopology::Global,
                global_head,
                global_theta,
                global_head / 4,
                NativeCausalReach::Complete,
            ),
            _ => return Err(NativeFullOperatorError::Configuration("layer_types")),
        };
        let named = |suffix: &str| format!("model.language_model.layers.{layer}.{suffix}");
        let coefficient = |suffix: &str| tensor(&named(suffix));
        let gain = |suffix: &str| -> Result<NativeTensorOrdinal, NativeFullOperatorError> {
            let ordinal = coefficient(suffix)?;
            require_shape(ordinal, &[hidden])?;
            Ok(ordinal)
        };

        let residual_attention = hidden_state;
        let input_gain = gain("input_layernorm.weight")?;
        let attention_input = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: hidden,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![hidden_state],
            vec![occurrence.clone(), fixed(hidden)],
            vec![input_gain],
        );
        let q_matrix = coefficient("self_attn.q_proj.weight")?;
        require_shape(q_matrix, &[heads * head_width, hidden])?;
        let q = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![attention_input],
            vec![occurrence.clone(), fixed(heads * head_width)],
            vec![q_matrix],
        );
        let q = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Reshape,
            vec![q],
            vec![occurrence.clone(), fixed(heads), fixed(head_width)],
            vec![],
        );
        let q_gain = coefficient("self_attn.q_norm.weight")?;
        require_shape(q_gain, &[head_width])?;
        let q = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: head_width,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![q],
            vec![occurrence.clone(), fixed(heads), fixed(head_width)],
            vec![q_gain],
        );
        let q = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            },
            vec![q],
            vec![occurrence.clone(), fixed(heads), fixed(head_width)],
            vec![],
        );

        let (kv_standing, k, v) = if layer < first_shared {
            let k_matrix = coefficient("self_attn.k_proj.weight")?;
            let v_matrix = coefficient("self_attn.v_proj.weight")?;
            require_shape(k_matrix, &[kv_heads * head_width, hidden])?;
            require_shape(v_matrix, &[kv_heads * head_width, hidden])?;
            let k = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::Contract,
                vec![attention_input],
                vec![occurrence.clone(), fixed(kv_heads * head_width)],
                vec![k_matrix],
            );
            let k = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::Reshape,
                vec![k],
                vec![occurrence.clone(), fixed(kv_heads), fixed(head_width)],
                vec![],
            );
            let k_gain = coefficient("self_attn.k_norm.weight")?;
            require_shape(k_gain, &[head_width])?;
            let k = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::RmsRebase {
                    group: head_width,
                    epsilon: epsilon.clone(),
                    has_gain: true,
                },
                vec![k],
                vec![occurrence.clone(), fixed(kv_heads), fixed(head_width)],
                vec![k_gain],
            );
            let k = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::RotaryChronology {
                    theta,
                    head_width,
                    rotated_width,
                },
                vec![k],
                vec![occurrence.clone(), fixed(kv_heads), fixed(head_width)],
                vec![],
            );
            let v = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::Contract,
                vec![attention_input],
                vec![occurrence.clone(), fixed(kv_heads * head_width)],
                vec![v_matrix],
            );
            let v = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::Reshape,
                vec![v],
                vec![occurrence.clone(), fixed(kv_heads), fixed(head_width)],
                vec![],
            );
            let v = graph.push(
                Some(layer_u16),
                NativeOperationPrimitive::RmsRebase {
                    group: head_width,
                    epsilon: epsilon.clone(),
                    has_gain: false,
                },
                vec![v],
                vec![occurrence.clone(), fixed(kv_heads), fixed(head_width)],
                vec![],
            );
            match attention {
                NativeAttentionTopology::Local => latest_local_kv = Some((layer, k, v)),
                NativeAttentionTopology::Global => latest_global_kv = Some((layer, k, v)),
            }
            (NativeKvStanding::Own, k, v)
        } else {
            let (owner, k, v) = match attention {
                NativeAttentionTopology::Local => latest_local_kv,
                NativeAttentionTopology::Global => latest_global_kv,
            }
            .ok_or(NativeFullOperatorError::Configuration(
                "shared K/V standing",
            ))?;
            for suffix in [
                "self_attn.k_proj.weight",
                "self_attn.v_proj.weight",
                "self_attn.k_norm.weight",
            ] {
                coefficient_obstructions.push(NativeCoefficientObstruction {
                    population: coefficient(suffix)?,
                    layer: layer_u16,
                    kind: NativeCoefficientObstructionKind::DeclaredButUnreachedBySharedStanding {
                        owner_layer: owner as u16,
                    },
                });
            }
            (
                NativeKvStanding::SharedFrom {
                    layer: owner as u16,
                },
                k,
                v,
            )
        };
        let attention_output = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::CausalContact {
                heads,
                kv_heads,
                head_width,
                reach,
                series_terms: 14,
            },
            vec![q, k, v],
            vec![occurrence.clone(), fixed(heads), fixed(head_width)],
            vec![],
        );
        let attention_output = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Reshape,
            vec![attention_output],
            vec![occurrence.clone(), fixed(heads * head_width)],
            vec![],
        );
        let o_matrix = coefficient("self_attn.o_proj.weight")?;
        require_shape(o_matrix, &[hidden, heads * head_width])?;
        let attention_output = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![attention_output],
            vec![occurrence.clone(), fixed(hidden)],
            vec![o_matrix],
        );
        let post_attention_gain = gain("post_attention_layernorm.weight")?;
        let attention_output = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: hidden,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![attention_output],
            vec![occurrence.clone(), fixed(hidden)],
            vec![post_attention_gain],
        );
        hidden_state = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Add,
            vec![residual_attention, attention_output],
            vec![occurrence.clone(), fixed(hidden)],
            vec![],
        );

        let residual_feedforward = hidden_state;
        let pre_feedforward_gain = gain("pre_feedforward_layernorm.weight")?;
        let feedforward_input = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: hidden,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![hidden_state],
            vec![occurrence.clone(), fixed(hidden)],
            vec![pre_feedforward_gain],
        );
        let gate_matrix = coefficient("mlp.gate_proj.weight")?;
        let up_matrix = coefficient("mlp.up_proj.weight")?;
        require_shape(gate_matrix, &[intermediate, hidden])?;
        require_shape(up_matrix, &[intermediate, hidden])?;
        let gate = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![feedforward_input],
            vec![occurrence.clone(), fixed(intermediate)],
            vec![gate_matrix],
        );
        let gate = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::GeluTanh,
            vec![gate],
            vec![occurrence.clone(), fixed(intermediate)],
            vec![],
        );
        let raised = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![feedforward_input],
            vec![occurrence.clone(), fixed(intermediate)],
            vec![up_matrix],
        );
        let feedforward = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Hadamard,
            vec![gate, raised],
            vec![occurrence.clone(), fixed(intermediate)],
            vec![],
        );
        let down_matrix = coefficient("mlp.down_proj.weight")?;
        require_shape(down_matrix, &[hidden, intermediate])?;
        let feedforward = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![feedforward],
            vec![occurrence.clone(), fixed(hidden)],
            vec![down_matrix],
        );
        let post_feedforward_gain = gain("post_feedforward_layernorm.weight")?;
        let feedforward = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: hidden,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![feedforward],
            vec![occurrence.clone(), fixed(hidden)],
            vec![post_feedforward_gain],
        );
        hidden_state = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Add,
            vec![residual_feedforward, feedforward],
            vec![occurrence.clone(), fixed(hidden)],
            vec![],
        );

        let residual_per_layer = hidden_state;
        let per_layer_gate = coefficient("per_layer_input_gate.weight")?;
        require_shape(per_layer_gate, &[per_layer, hidden])?;
        let per_layer_branch = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![hidden_state],
            vec![occurrence.clone(), fixed(per_layer)],
            vec![per_layer_gate],
        );
        let per_layer_branch = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::GeluTanh,
            vec![per_layer_branch],
            vec![occurrence.clone(), fixed(per_layer)],
            vec![],
        );
        let per_layer_input = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Select { axis: 1, at: layer },
            vec![per_layer_inputs],
            vec![occurrence.clone(), fixed(per_layer)],
            vec![],
        );
        let per_layer_branch = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Hadamard,
            vec![per_layer_branch, per_layer_input],
            vec![occurrence.clone(), fixed(per_layer)],
            vec![],
        );
        let per_layer_projection = coefficient("per_layer_projection.weight")?;
        require_shape(per_layer_projection, &[hidden, per_layer])?;
        let per_layer_branch = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Contract,
            vec![per_layer_branch],
            vec![occurrence.clone(), fixed(hidden)],
            vec![per_layer_projection],
        );
        let post_per_layer_gain = gain("post_per_layer_input_norm.weight")?;
        let per_layer_branch = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::RmsRebase {
                group: hidden,
                epsilon: epsilon.clone(),
                has_gain: true,
            },
            vec![per_layer_branch],
            vec![occurrence.clone(), fixed(hidden)],
            vec![post_per_layer_gain],
        );
        hidden_state = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Add,
            vec![residual_per_layer, per_layer_branch],
            vec![occurrence.clone(), fixed(hidden)],
            vec![],
        );
        let layer_scalar = coefficient("layer_scalar")?;
        require_shape(layer_scalar, &[1])?;
        hidden_state = graph.push(
            Some(layer_u16),
            NativeOperationPrimitive::Scale {
                by: NativeScaleConstraint::Coefficient,
            },
            vec![hidden_state],
            vec![occurrence.clone(), fixed(hidden)],
            vec![layer_scalar],
        );
        layer_topologies.push(NativeLayerTopology {
            ordinal: layer_u16,
            attention,
            kv_standing,
            first_operation,
            operation_population: graph.operations.len() as u32 - first_operation,
        });
    }

    let final_norm = tensor("model.language_model.norm.weight")?;
    require_shape(final_norm, &[hidden])?;
    hidden_state = graph.push(
        None,
        NativeOperationPrimitive::RmsRebase {
            group: hidden,
            epsilon,
            has_gain: true,
        },
        vec![hidden_state],
        vec![occurrence.clone(), fixed(hidden)],
        vec![final_norm],
    );
    let logits = graph.push(
        None,
        NativeOperationPrimitive::Contract,
        vec![hidden_state],
        vec![occurrence.clone(), fixed(vocabulary)],
        vec![main_embedding],
    );
    let logits = graph.push(
        None,
        NativeOperationPrimitive::Scale {
            by: NativeScaleConstraint::Rational {
                numerator: 1,
                denominator: final_cap,
            },
        },
        vec![logits],
        vec![occurrence.clone(), fixed(vocabulary)],
        vec![],
    );
    let logits = graph.push(
        None,
        NativeOperationPrimitive::Tanh,
        vec![logits],
        vec![occurrence.clone(), fixed(vocabulary)],
        vec![],
    );
    let logits = graph.push(
        None,
        NativeOperationPrimitive::Scale {
            by: NativeScaleConstraint::Rational {
                numerator: final_cap as i64,
                denominator: 1,
            },
        },
        vec![logits],
        vec![occurrence.clone(), fixed(vocabulary)],
        vec![],
    );
    graph.push(
        None,
        NativeOperationPrimitive::Emit,
        vec![logits],
        vec![occurrence, fixed(vocabulary)],
        vec![],
    );

    let native = NativeFullOperatorEcology {
        schema: NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.to_owned(),
        shared_carrier_extent: hidden,
        coefficient_populations,
        carriers: graph.carriers,
        operations: graph.operations,
        layers: layer_topologies,
        coefficient_obstructions,
    };
    native.validate()?;
    Ok(NativeFullOperatorDismantlingReturn {
        native,
        exterior: NativeFullOperatorColdWitness {
            source_container: container_path.display().to_string(),
            source_configuration: configuration_path.display().to_string(),
            payload_base: container.payload_base(),
            populations: cold,
        },
    })
}

fn usize_field(
    object: &serde_json::Map<String, Value>,
    field: &'static str,
) -> Result<usize, NativeFullOperatorError> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or(NativeFullOperatorError::Configuration(field))
}

fn bool_field(
    object: &serde_json::Map<String, Value>,
    field: &'static str,
) -> Result<bool, NativeFullOperatorError> {
    object
        .get(field)
        .and_then(Value::as_bool)
        .ok_or(NativeFullOperatorError::Configuration(field))
}

fn rope_theta(
    object: &serde_json::Map<String, Value>,
    kind: &'static str,
) -> Result<u64, NativeFullOperatorError> {
    object
        .get(kind)
        .and_then(Value::as_object)
        .and_then(|value| value.get("rope_theta"))
        .and_then(integral_number)
        .ok_or(NativeFullOperatorError::Configuration("rope_theta"))
}

fn integral_number(value: &Value) -> Option<u64> {
    value.as_u64().or_else(|| {
        value
            .as_f64()
            .filter(|number| number.is_finite() && *number >= 0.0 && number.fract() == 0.0)
            .and_then(|number| u64::try_from(number as u128).ok())
    })
}

fn product(shape: &[usize]) -> Option<u64> {
    shape.iter().try_fold(1u64, |total, extent| {
        total.checked_mul(u64::try_from(*extent).ok()?)
    })
}
