//! Source-detached resident chart declarations shared by the Phoenix tower.
//!
//! This owner carries exact constants and operation-complex construction helpers only. It does
//! not open a foreign container, authenticate a source occurrence, or name a host implementation
//! path. The native-rest adapter is the sole material crossing for production runtime.

use std::collections::BTreeMap;

use crate::category::BoundaryId;
use crate::causal::EventId;
use crate::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use crate::front_passage::ResidentRealization;
use crate::interaction::OccurrencePort;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use crate::resident_section::{Dyadic, DyadicEnclosure};
use num_bigint::BigInt;
use relational_geometry::Rat;

pub const HIDDEN: usize = 2560;
pub const HEADS: usize = 8;
pub const KV_HEADS: usize = 2;
pub const HEAD_WIDTH: usize = 256;
pub const PLE_WIDTH: usize = 256;
pub const FFN: usize = 10240;
pub const SLIDING_WINDOW: usize = 512;
pub const EMBED_SCALE: Dyadic = Dyadic {
    significand: 101,
    exponent: -1,
};
pub const PLE_EMBED_SCALE: Dyadic = Dyadic {
    significand: 16,
    exponent: 0,
};
pub const EPS_BITS: u64 = 0x3eb0c6f7a0b5ed8d;
pub const GELU_SCALE_BITS: u64 = 0x3fe9884533d43651;
pub const GELU_CUBIC_BITS: u64 = 0x3fa6e4e26d4801f7;
pub const ROPE_THETA: u64 = 10_000;
pub const BAND_GRAIN: u32 = 60;
pub const ENTERING: &str = "entering rows";
pub const PLE_ENTERING: &str = "per-layer entering rows";
pub const PLE_MODEL_PROJECTION: &str = "model.language_model.per_layer_model_projection.weight";
pub const PLE_PROJECTION_NORM: &str = "model.language_model.per_layer_projection_norm.weight";
pub const EMBED: &str = "model.language_model.embed_tokens.weight";
pub const PLE_EMBED: &str = "model.language_model.embed_tokens_per_layer.weight";
pub const POPULATIONS: [&str; 10] = [
    "self_attn.q_proj.weight",
    "self_attn.k_proj.weight",
    "self_attn.v_proj.weight",
    "self_attn.o_proj.weight",
    "mlp.gate_proj.weight",
    "mlp.up_proj.weight",
    "mlp.down_proj.weight",
    "per_layer_input_gate.weight",
    "per_layer_projection.weight",
    "input_layernorm.weight",
];
pub const GAINS: [&str; 7] = [
    "input_layernorm.weight",
    "self_attn.q_norm.weight",
    "self_attn.k_norm.weight",
    "post_attention_layernorm.weight",
    "pre_feedforward_layernorm.weight",
    "post_feedforward_layernorm.weight",
    "post_per_layer_input_norm.weight",
];

pub fn named(suffix: &str) -> String {
    format!("model.language_model.layers.0.{suffix}")
}

/// Production testimony is path-free. Foreign implementation bindings belong to example sites.
pub fn implementation(statement: &str) -> SourceTestimony {
    SourceTestimony::RestedImplementation {
        symbol: statement.to_owned(),
    }
}
pub fn configuration(field: &str, value: &str) -> SourceTestimony {
    SourceTestimony::Configuration {
        field: field.to_owned(),
        value: value.to_owned(),
    }
}
pub fn shape(population: &str, shape: &[usize]) -> SourceTestimony {
    SourceTestimony::DeclaredShape {
        population: population.to_owned(),
        shape: shape.to_vec(),
    }
}
pub fn intervention(statement: &str) -> SourceTestimony {
    SourceTestimony::Intervention {
        statement: statement.to_owned(),
    }
}
pub fn rebase_testimony(site: &str, population: &str, group: usize) -> Vec<SourceTestimony> {
    vec![
        implementation(site),
        implementation(
            "Gemma4RMSNorm._norm (mean_squared = hidden_states.pow(2).mean(-1, keepdim=True) + self.eps)",
        ),
        implementation(
            "Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))",
        ),
        implementation(
            "Gemma4RMSNorm.forward (normed_output = normed_output * self.weight.float())",
        ),
        configuration("rms_norm_eps", "1e-06"),
        shape(population, &[group]),
    ]
}
pub fn law(
    complex: &mut PortedOperationComplex,
    name: &str,
    species: OperationSpecies,
    inputs: Vec<BoundaryId>,
    outputs: Vec<BoundaryId>,
    carrier: Option<String>,
    testimony: Vec<SourceTestimony>,
) -> Result<EventId, String> {
    let law = complex
        .bind_operation(name, species, inputs, outputs, carrier, testimony)
        .map_err(|e| e.to_string())?;
    complex.occur(law).map_err(|e| e.to_string())
}
pub fn bond(
    complex: &mut PortedOperationComplex,
    name: &str,
    port: BoundaryId,
    from: EventId,
    to: EventId,
    input: usize,
) -> Result<(), String> {
    complex
        .carries_precedence(
            name,
            port,
            OccurrencePort::output(from, 0),
            OccurrencePort::input(to, input),
        )
        .map_err(|e| e.to_string())
}
pub struct Founded {
    pub complex: PortedOperationComplex,
    pub realization: ResidentRealization,
    pub returns: BTreeMap<&'static str, EventId>,
}
pub fn point_enclosure(dyadic: Dyadic) -> DyadicEnclosure {
    if dyadic.exponent >= 0 {
        let value = dyadic.significand << dyadic.exponent;
        DyadicEnclosure {
            lo: value,
            hi: value,
            grain: 0,
        }
    } else {
        DyadicEnclosure {
            lo: dyadic.significand,
            hi: dyadic.significand,
            grain: (-dyadic.exponent) as u32,
        }
    }
}
pub fn found_bands(terms: usize) -> Result<Vec<((i64, i64), (i64, i64))>, String> {
    let bands = HEAD_WIDTH / 2;
    let ratio = AlgebraicRoot::nth_root(
        &Rat::from_integer(BigInt::from(ROPE_THETA)),
        bands as u32,
        64,
    )
    .map_err(|e| format!("{e:?}"))?
    .enclosure()
    .reciprocal()
    .map_err(|e| format!("{e:?}"))?;
    let mut angle = ExactInterval::point(Rat::from_integer(BigInt::from(1)));
    let mut elements = Vec::with_capacity(bands);
    for _ in 0..bands {
        let (cl, sl) =
            CertifiedSeries::circular_series(&angle.lower, terms).map_err(|e| format!("{e:?}"))?;
        let (ch, sh) =
            CertifiedSeries::circular_series(&angle.upper, terms).map_err(|e| format!("{e:?}"))?;
        let cos = ExactInterval::new(
            ch.enclosure()
                .lower
                .clone()
                .min(cl.enclosure().lower.clone()),
            cl.enclosure()
                .upper
                .clone()
                .max(ch.enclosure().upper.clone()),
        )
        .map_err(|e| format!("{e:?}"))?;
        let sin = ExactInterval::new(
            sl.enclosure()
                .lower
                .clone()
                .min(sh.enclosure().lower.clone()),
            sh.enclosure()
                .upper
                .clone()
                .max(sl.enclosure().upper.clone()),
        )
        .map_err(|e| format!("{e:?}"))?;
        let cos = DyadicEnclosure::of_interval(&cos, BAND_GRAIN).map_err(|e| e.to_string())?;
        let sin = DyadicEnclosure::of_interval(&sin, BAND_GRAIN).map_err(|e| e.to_string())?;
        elements.push(((cos.lo, cos.hi), (sin.lo, sin.hi)));
        angle = angle
            .times(&ratio)
            .map_err(|e| format!("{e:?}"))?
            .round_out(64)
            .map_err(|e| format!("{e:?}"))?;
    }
    Ok(elements)
}
pub fn algebraic_scales() -> Result<(DyadicEnclosure, DyadicEnclosure), String> {
    let projection =
        AlgebraicRoot::reciprocal_square_root(&Rat::from_integer(BigInt::from(HIDDEN as u64)), 64)
            .map_err(|e| format!("{e:?}"))?;
    let half = AlgebraicRoot::reciprocal_square_root(&Rat::from_integer(BigInt::from(2)), 64)
        .map_err(|e| format!("{e:?}"))?;
    Ok((
        DyadicEnclosure::of_interval(projection.enclosure(), BAND_GRAIN)
            .map_err(|e| e.to_string())?,
        DyadicEnclosure::of_interval(half.enclosure(), BAND_GRAIN).map_err(|e| e.to_string())?,
    ))
}
