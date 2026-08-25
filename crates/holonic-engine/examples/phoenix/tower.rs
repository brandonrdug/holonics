//! **The whole text tower of Gemma-4-E4B, founded layer by layer as bound deeds** — every layer a
//! `PortedOperationComplex` over the same laws the layer-zero site binds, generalized over the
//! source's two attention species, its KV-sharing realization and its per-layer input, with the
//! final normalization and the tied output boundary as a last deed.
//!
//! Plan: the Gemma instance blueprint §6 (*the generalization to all 42 layers proceeds only after
//! serial composition preserves port lineage*) and Stations B–C of the complete sequence. This is a
//! site, not a library owner: it binds one source instance and never becomes internal anatomy.
//!
//! # What the source realization decides, and where it is read
//!
//! Read from `modeling_gemma4.py` (transformers 5.8.1) and `config.json`, and carried as testimony
//! on every binding so the passage refuses if the text drifts:
//!
//! * `layer_types`: 35 sliding layers and 7 full (`{5, 11, 17, 23, 29, 35, 41}`); a sliding layer
//!   has head width `head_dim = 256`, window `sliding_window = 512`, `default` RoPE at θ = 10⁴ over
//!   the whole head; a full layer has head width `global_head_dim = 512`, no window, `proportional`
//!   RoPE at θ = 10⁶ rotating `int(0.25 · 512 / 2) = 64` pairs and leaving 192 pairs fixed.
//! * `num_kv_shared_layers = 18`: `first_kv_shared_layer_idx = 42 − 18 = 24`; layers `24..41` build
//!   no `k_proj`/`v_proj`/`k_norm`/`v_norm` and read `shared_kv_states[layer_type]`, which the last
//!   non-shared layer of each type stores after its K chronology and V rebase — layer 22 for the
//!   sliding type and layer 23 for the full. The stored `k_proj`/`v_proj`/`k_norm` populations of
//!   layers 24–41 are therefore present in the container and **unbound by the source realization**:
//!   the manifest says so by name rather than inferring inertness from a count.
//! * `per_layer_inputs` are projected from the EMBEDDING (`inputs_embeds`), not from the residual
//!   stream, so every layer's per-layer predecessor re-enters `x0`.
//! * the final `norm`, then the tied `lm_head` (= `embed_tokens` read in the other direction), then
//!   `final_logit_softcapping = 30` — a strictly monotone transformation, so every order face of the
//!   potential section is invariant under it and it is reported, not enacted.
//!
//! # Standings carried between layer deeds
//!
//! The residual stream leaving layer ℓ is released from its passage and enters layer ℓ+1 as a
//! [`Standing`]; the K and V standings of layers 22 and 23 are released and carried into every
//! shared layer. A carry copies on the card (`section_carry`); nothing crosses the apparatus
//! boundary.

#![allow(dead_code)]

use std::collections::BTreeMap;

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use holonic_engine::front_passage::{
    Chronology, Contact, Contract, Enter, GeluTanh, Hadamard, MaterialPlan, MidpointQuotient,
    PermuteColumns, ReEntry, ResidentRealization, RmsRebase, Scale, Standing, WithdrawColumns,
    WithdrawRows,
};
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex};
use holonic_engine::resident_section::{Dyadic, DyadicEnclosure, SeriesAperture};
use num_bigint::BigInt;
use relational_geometry::Rat;

pub use super::resident_layer::{
    EMBED, EMBED_SCALE, EPS_BITS, FFN, Founded, GAINS, GELU_CUBIC_BITS, GELU_SCALE_BITS, HEADS,
    HIDDEN, KV_HEADS, PLE_EMBED, PLE_EMBED_SCALE, PLE_MODEL_PROJECTION, PLE_PROJECTION_NORM,
    PLE_WIDTH, POPULATIONS, SLIDING_WINDOW, Source, bond, configuration, implementation,
    intervention, law, point_enclosure, rebase_testimony, shape,
};

pub const LAYERS: usize = 42;
pub const FULL_LAYERS: [usize; 7] = [5, 11, 17, 23, 29, 35, 41];
pub const FIRST_SHARED: usize = 24;
pub const SLIDING_HEAD: usize = 256;
pub const FULL_HEAD: usize = 512;
/// `int(0.25 · 512 / 2)`: the rotated pairs of a full layer's proportional chronology.
pub const FULL_ROTATED_PAIRS: usize = 64;
pub const SLIDING_THETA: u64 = 10_000;
pub const FULL_THETA: u64 = 1_000_000;
pub const VOCABULARY: usize = 262_144;
pub const BAND_GRAIN: u32 = 60;
pub const BAND_TERMS: usize = 40;
pub const FINAL_NORM: &str = "model.language_model.norm.weight";

pub const SLIDING_BANDS: &str = "sliding band elements (theta 1e4, 128 rotated pairs of 256)";
pub const FULL_BANDS: &str = "full band elements (theta 1e6, 64 rotated pairs of 512, 192 fixed)";
pub const ENTERING: &str = "entering rows";
/// The residual stream carried in from the previous layer.
pub const CARRIED_STANDING: &str = "carried standing";
pub const SHARED_K_SLIDING: &str = "shared K, sliding (stored by layer 22)";
pub const SHARED_V_SLIDING: &str = "shared V, sliding (stored by layer 22)";
pub const SHARED_K_FULL: &str = "shared K, full (stored by layer 23)";
pub const SHARED_V_FULL: &str = "shared V, full (stored by layer 23)";

/// Named returns a caller may read or release.
pub const X0: &str = "x0";
pub const LAYER_RETURN: &str = "layer";
/// The layer scalar's own enclosure, before the terminal quotient under the midpoint chart.
pub const LAYER_ENCLOSURE: &str = "layer enclosure";
pub const K_STANDING: &str = "k standing";
pub const V_STANDING: &str = "v standing";
pub const CONTACT: &str = "contact";
/// The layer's per-layer input section after the join, scale and (under the midpoint chart) seal.
pub const PLE_SECTION: &str = "ple section";
pub const FINAL_NORMED: &str = "final normed";
pub const POTENTIAL: &str = "potential section";

/// The two attention species the source declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Species {
    Sliding,
    Full,
}

impl Species {
    pub fn of(layer: usize) -> Self {
        if FULL_LAYERS.contains(&layer) {
            Self::Full
        } else {
            Self::Sliding
        }
    }
    pub fn head_width(self) -> usize {
        match self {
            Self::Sliding => SLIDING_HEAD,
            Self::Full => FULL_HEAD,
        }
    }
    pub fn bands(self) -> &'static str {
        match self {
            Self::Sliding => SLIDING_BANDS,
            Self::Full => FULL_BANDS,
        }
    }
    pub fn layer_type(self) -> &'static str {
        match self {
            Self::Sliding => "sliding_attention",
            Self::Full => "full_attention",
        }
    }
}

/// The K/V realization of one layer, bound from the source's `is_kv_shared_layer` and
/// `store_full_length_kv`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KvRole {
    /// Builds its own K and V from its own projections and rebases.
    Own,
    /// Builds its own, and stores them for the shared layers of its type (22 sliding, 23 full).
    OwnAndStore,
    /// Reads the stored K and V of the last non-shared layer of its type; builds none.
    Shared,
}

impl KvRole {
    pub fn of(layer: usize) -> Self {
        if layer >= FIRST_SHARED {
            Self::Shared
        } else if layer == 22 || layer == 23 {
            Self::OwnAndStore
        } else {
            Self::Own
        }
    }
}

pub fn named(layer: usize, suffix: &str) -> String {
    format!("model.language_model.layers.{layer}.{suffix}")
}

/// The stored populations a layer's deed mounts, given its role: the attention and passage maps,
/// the gains, the per-layer projections, the layer's slice of the per-layer model projection and
/// the projection norm. A shared layer mounts no K/V projection and no K norm.
pub fn populations(layer: usize) -> Vec<String> {
    let role = KvRole::of(layer);
    let mut names: Vec<String> = Vec::new();
    for suffix in POPULATIONS.iter().chain(GAINS.iter()) {
        let shared_only = matches!(
            *suffix,
            "self_attn.k_proj.weight" | "self_attn.v_proj.weight" | "self_attn.k_norm.weight"
        );
        if role == KvRole::Shared && shared_only {
            continue;
        }
        let name = named(layer, suffix);
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

/// The stored populations of a layer that the source realization leaves UNBOUND: a shared layer's
/// `k_proj`, `v_proj` and `k_norm`, present in the container and built by no module.
pub fn unbound_populations(layer: usize) -> Vec<String> {
    if KvRole::of(layer) != KvRole::Shared {
        return Vec::new();
    }
    [
        "self_attn.k_proj.weight",
        "self_attn.v_proj.weight",
        "self_attn.k_norm.weight",
    ]
    .iter()
    .map(|s| named(layer, s))
    .collect()
}

/// The receipt of one layer's mount.
#[derive(Debug, Default)]
pub struct LayerMount {
    pub populations: usize,
    pub stored_octets: u64,
    pub resident_octets: u64,
    pub layer_scalar: Option<Dyadic>,
    pub regions: BTreeMap<String, holonic_engine::source_occurrence::RegionIdentity>,
}

/// **Mount one layer's stored populations** — the layer's maps and gains, its slice of the per-layer
/// model projection, the projection norm, and its layer scalar — hashing every region as it is read.
/// The caller has admitted the material deed before this is called.
pub fn mount_layer<'chart>(
    source: &mut Source,
    readout: &'chart holonic_engine::embedding_fiber::ResidentReadout,
    material: &mut holonic_engine::front_passage::ResidentMaterial<'chart>,
    layer: usize,
) -> Result<LayerMount, String> {
    use super::resident_layer::digest_words;
    use holonic_engine::front_passage::MountedPopulation;
    let mut receipt = LayerMount::default();
    fn mount_one<'chart>(
        readout: &'chart holonic_engine::embedding_fiber::ResidentReadout,
        material: &mut holonic_engine::front_passage::ResidentMaterial<'chart>,
        receipt: &mut LayerMount,
        name: String,
        words: Vec<u16>,
        dim: usize,
    ) -> Result<(), String> {
        let mounted = readout
            .mount_bfloat16(&words, dim)
            .map_err(|error| format!("{error:?}"))?;
        let masses = mounted
            .absolute_row_mass()
            .map_err(|error| format!("{error:?}"))?;
        let widest = masses.iter().map(|m| m.unsigned_abs()).max().unwrap_or(0);
        let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
        receipt.populations += 1;
        receipt.stored_octets += (words.len() * 2) as u64;
        receipt.resident_octets += mounted.resident_octets() as u64;
        material.populations.insert(
            name,
            MountedPopulation {
                readout: mounted,
                mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0),
            },
        );
        Ok(())
    }
    for name in populations(layer) {
        if material.populations.contains_key(&name) {
            continue;
        }
        let (words, shape) = source.whole(&name)?;
        let dim = *shape.last().ok_or_else(|| format!("{name} has no shape"))?;
        receipt.regions.insert(
            name.clone(),
            source.region(&name, Some(digest_words(&words)))?,
        );
        mount_one(readout, material, &mut receipt, name, words, dim)?;
    }
    if !material.populations.contains_key(PLE_MODEL_PROJECTION) {
        let (words, dim) = source.rows(PLE_MODEL_PROJECTION, PLE_WIDTH * layer, PLE_WIDTH)?;
        receipt.regions.insert(
            PLE_MODEL_PROJECTION.to_owned(),
            source.region(PLE_MODEL_PROJECTION, None)?,
        );
        let mut slice = source.region(PLE_MODEL_PROJECTION, Some(digest_words(&words)))?;
        slice.population = format!(
            "{PLE_MODEL_PROJECTION} rows {}..{}",
            PLE_WIDTH * layer,
            PLE_WIDTH * (layer + 1)
        );
        slice.shape = vec![PLE_WIDTH, dim];
        slice.start += (PLE_WIDTH * layer * dim * 2) as u64;
        slice.end = slice.start + (PLE_WIDTH * dim * 2) as u64;
        receipt.regions.insert(slice.population.clone(), slice);
        mount_one(
            readout,
            material,
            &mut receipt,
            PLE_MODEL_PROJECTION.to_owned(),
            words,
            dim,
        )?;
    }
    if !material.populations.contains_key(PLE_PROJECTION_NORM) {
        let (words, shape) = source.whole(PLE_PROJECTION_NORM)?;
        receipt.regions.insert(
            PLE_PROJECTION_NORM.to_owned(),
            source.region(PLE_PROJECTION_NORM, Some(digest_words(&words)))?,
        );
        mount_one(
            readout,
            material,
            &mut receipt,
            PLE_PROJECTION_NORM.to_owned(),
            words,
            shape[0],
        )?;
    }
    let scalar_name = named(layer, "layer_scalar");
    let (scalar, _) = source.whole(&scalar_name)?;
    receipt.regions.insert(
        scalar_name.clone(),
        source.region(&scalar_name, Some(digest_words(&scalar)))?,
    );
    let word = *scalar.first().ok_or("layer_scalar is empty")?;
    receipt.layer_scalar = Some(Dyadic::of_bfloat16_bits(word).map_err(|error| error.to_string())?);
    receipt
        .regions
        .insert(EMBED.to_owned(), source.region(EMBED, None)?);
    receipt
        .regions
        .insert(PLE_EMBED.to_owned(), source.region(PLE_EMBED, None)?);
    Ok(receipt)
}

/// **Mount the final deed's populations**: the final norm gain and the tied output table as a map
/// over the whole vocabulary.
pub fn mount_final<'chart>(
    source: &mut Source,
    readout: &'chart holonic_engine::embedding_fiber::ResidentReadout,
    material: &mut holonic_engine::front_passage::ResidentMaterial<'chart>,
) -> Result<LayerMount, String> {
    use super::resident_layer::digest_words;
    use holonic_engine::front_passage::MountedPopulation;
    let mut receipt = LayerMount::default();
    for name in [FINAL_NORM, EMBED] {
        let (words, shape) = source.whole(name)?;
        let dim = *shape.last().ok_or_else(|| format!("{name} has no shape"))?;
        receipt.regions.insert(
            name.to_owned(),
            source.region(name, Some(digest_words(&words)))?,
        );
        let mounted = readout
            .mount_bfloat16(&words, dim)
            .map_err(|error| format!("{error:?}"))?;
        let masses = mounted
            .absolute_row_mass()
            .map_err(|error| format!("{error:?}"))?;
        let widest = masses.iter().map(|m| m.unsigned_abs()).max().unwrap_or(0);
        let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
        receipt.populations += 1;
        receipt.stored_octets += (words.len() * 2) as u64;
        receipt.resident_octets += mounted.resident_octets() as u64;
        material.populations.insert(
            name.to_owned(),
            MountedPopulation {
                readout: mounted,
                mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0),
            },
        );
    }
    Ok(receipt)
}

/// **The runtime-supplied material of one layer**: the embedding rows of the tokens and the layer's
/// slice of their per-layer embedding rows. Nothing about the tokens is compiled into any diagram.
pub fn enter(
    source: &mut Source,
    tokens: &[usize],
    layer: usize,
    material: &mut holonic_engine::front_passage::ResidentMaterial<'_>,
) -> Result<(), String> {
    use holonic_engine::front_passage::EnteringRows;
    let mut entering = Vec::with_capacity(tokens.len() * HIDDEN);
    let mut per_layer = Vec::with_capacity(tokens.len() * PLE_WIDTH);
    for token in tokens {
        let (row, width) = source.rows(EMBED, *token, 1)?;
        if width != HIDDEN {
            return Err(format!("{EMBED} is {width} wide"));
        }
        entering.extend(row);
        let (row, width) = source.rows(PLE_EMBED, *token, 1)?;
        let from = layer * PLE_WIDTH;
        if width < from + PLE_WIDTH {
            return Err(format!("{PLE_EMBED} is {width} wide"));
        }
        per_layer.extend_from_slice(&row[from..from + PLE_WIDTH]);
    }
    material.entering.insert(
        ENTERING.to_owned(),
        EnteringRows {
            words: entering,
            rows: tokens.len(),
            width: HIDDEN,
        },
    );
    material.entering.insert(
        super::resident_layer::PLE_ENTERING.to_owned(),
        EnteringRows {
            words: per_layer,
            rows: tokens.len(),
            width: PLE_WIDTH,
        },
    );
    Ok(())
}

/// The material plan of one layer's deed, from the container header.
pub fn material_plan(source: &Source, layer: usize, tokens: usize) -> Result<MaterialPlan, String> {
    let mut maps: Vec<(String, usize, usize)> = Vec::new();
    for name in populations(layer) {
        let shape = source
            .container
            .tensor(&name)
            .map_err(|error| error.to_string())?
            .shape
            .clone();
        let dim = *shape.last().ok_or_else(|| format!("{name} has no shape"))?;
        let rows: usize = shape.iter().take(shape.len() - 1).product::<usize>().max(1);
        maps.push((name, rows, dim));
    }
    let projection = source
        .container
        .tensor(PLE_MODEL_PROJECTION)
        .map_err(|error| error.to_string())?
        .shape
        .clone();
    maps.push((PLE_MODEL_PROJECTION.to_owned(), PLE_WIDTH, projection[1]));
    let norm = source
        .container
        .tensor(PLE_PROJECTION_NORM)
        .map_err(|error| error.to_string())?
        .shape
        .clone();
    maps.push((PLE_PROJECTION_NORM.to_owned(), 1, norm[0]));
    let bands = Species::of(layer).head_width() / 2;
    Ok(MaterialPlan {
        maps,
        band_elements: bands,
        positions: tokens,
    })
}

/// The material plan of the final deed: the final norm gain and the tied output table.
pub fn final_material_plan(source: &Source) -> Result<MaterialPlan, String> {
    let embed = source
        .container
        .tensor(EMBED)
        .map_err(|error| error.to_string())?
        .shape
        .clone();
    let norm = source
        .container
        .tensor(FINAL_NORM)
        .map_err(|error| error.to_string())?
        .shape
        .clone();
    Ok(MaterialPlan {
        maps: vec![
            (EMBED.to_owned(), embed[0], embed[1]),
            (FINAL_NORM.to_owned(), 1, norm[0]),
        ],
        band_elements: 0,
        positions: 0,
    })
}

/// The band group elements of one species' chronology: `(cos θ_b, sin θ_b)`, `θ_b = θ^{-2b/d}` for
/// the rotated pairs and the identity for the fixed pairs of a proportional chronology, each a
/// certified enclosure at `2^-60`. Founded once on the serial chart; the position is spent on the
/// card by repeated squaring of the interval rotation.
pub fn found_bands(
    species: Species,
    terms: usize,
) -> Result<Vec<((i64, i64), (i64, i64))>, String> {
    let head = species.head_width();
    let pairs = head / 2;
    let (theta, rotated) = match species {
        Species::Sliding => (SLIDING_THETA, pairs),
        Species::Full => (FULL_THETA, FULL_ROTATED_PAIRS),
    };
    // θ^{-2b/d} = (θ^{-1/(d/2)})^b : the ratio is the reciprocal of the (d/2)-th root of θ
    let ratio = AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(theta)), pairs as u32, 64)
        .map_err(|error| format!("{error:?}"))?
        .enclosure()
        .reciprocal()
        .map_err(|error| format!("{error:?}"))?;
    let mut angle = ExactInterval::point(Rat::from_integer(BigInt::from(1)));
    let mut elements = Vec::with_capacity(pairs);
    for band in 0..pairs {
        if band < rotated {
            let (cos_low, sin_low) = CertifiedSeries::circular_series(&angle.lower, terms)
                .map_err(|e| format!("{e:?}"))?;
            let (cos_high, sin_high) = CertifiedSeries::circular_series(&angle.upper, terms)
                .map_err(|e| format!("{e:?}"))?;
            let cos = ExactInterval::new(
                cos_high
                    .enclosure()
                    .lower
                    .clone()
                    .min(cos_low.enclosure().lower.clone()),
                cos_low
                    .enclosure()
                    .upper
                    .clone()
                    .max(cos_high.enclosure().upper.clone()),
            )
            .map_err(|e| format!("{e:?}"))?;
            let sin = ExactInterval::new(
                sin_low
                    .enclosure()
                    .lower
                    .clone()
                    .min(sin_high.enclosure().lower.clone()),
                sin_high
                    .enclosure()
                    .upper
                    .clone()
                    .max(sin_low.enclosure().upper.clone()),
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
        } else {
            // the fixed pairs: inverse frequency zero, the identity rotation exactly
            let one = 1i64 << BAND_GRAIN;
            elements.push(((one, one), (0, 0)));
        }
    }
    Ok(elements)
}

/// `2560^{-1/2}` and `2^{-1/2}` as certified enclosures at the band grain.
pub fn algebraic_scales() -> Result<(DyadicEnclosure, DyadicEnclosure), String> {
    super::resident_layer::algebraic_scales()
}

/// **The carrier chart of a deed.** `Interval` propagates every certified enclosure into its
/// successors — exact, and diverging: the composed enclosure's a-priori amplification is ≈ 2^35 per
/// layer (measured at grains 2^-48 and 2^-24), so the word is exhausted inside layer 1. `Midpoint`
/// is the receiver's declared quotient chart: after every occurrence whose enclosure can widen, a
/// [`MidpointQuotient`] collapses the enclosure to its midpoint for the successors while the
/// enclosure stays resident in the predecessor's section as the complete per-entry residual and its
/// collapsed population (widest, summed and nonzero widths) is censused. Each occurrence's enclosure
/// is then certified relative to its midpoint predecessors; the composition is not, and the receipt
/// says so.
pub use holonic_engine::phoenix::tower::Chart;

pub const QUOTIENT_DECLARATION: &str = "declared quotient chart: the certified enclosure is collapsed to its midpoint for the successors; the enclosure is retained in the predecessor's section as the complete per-entry residual and its collapsed population is censused; forced by the carrier's word at the measured amplification of the composed enclosure (about 2^35 per layer), not chosen to improve a number";

/// Seal an occurrence's output under the chart: under `Midpoint`, a quotient occurrence after it,
/// whose output the successors read; under `Interval`, the occurrence itself.
pub fn seal(
    chart: Chart,
    complex: &mut PortedOperationComplex,
    realization: &mut ResidentRealization,
    event: EventId,
    port: BoundaryId,
    label: &str,
) -> Result<EventId, String> {
    match chart {
        Chart::Interval => Ok(event),
        Chart::Midpoint => {
            let quotient = law(
                complex,
                &format!("{label} · midpoint quotient"),
                OperationSpecies::Quotient,
                vec![port],
                vec![port],
                None,
                vec![intervention(QUOTIENT_DECLARATION)],
            )?;
            realization.bind(quotient, MidpointQuotient);
            bond(
                complex,
                &format!("{label} sealed"),
                port,
                event,
                quotient,
                0,
            )?;
            Ok(quotient)
        }
    }
}

/// How a layer's deed enters its standing: layer zero from the embedding rows the runtime supplied;
/// every later layer from the residual stream the previous layer released.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Entry {
    Rows,
    Carried,
}

/// **The matched sibling's intervention, at one declared site of one layer.** Every variant is
/// realized as an occurrence typed as the caller's intervention (quotient or intervention-only
/// transport), never as source law; the base deed carries `None`. Remove / replace / permute /
/// rebase / isolate, by the directive's panel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intervention {
    None,
    /// initial embedding: the columns `[from, from+span)` of `x0` withdrawn (remove)
    WithdrawEmbeddingColumns {
        from: usize,
        span: usize,
    },
    /// per-layer embedding: the layer's PLE section withdrawn whole (remove)
    WithdrawPle,
    /// normalization: the standing rebased by `by` BEFORE the input rebase — a gauge the norm
    /// quotients away up to its epsilon (rebase)
    ScaleBeforeInputRebase {
        by: i64,
    },
    /// normalization: the standing rebased by `by` AFTER the input rebase (rebase)
    ScaleAfterInputRebase {
        by: i64,
    },
    /// chronology: the band elements replaced by the identity — no rotation (replace)
    IdentityChronology,
    /// chronology: the positions reversed (permute) — the driver mounts reversed positions
    ReversedPositions,
    /// Q/K contact: two receiver heads permuted after the chronology (permute)
    PermuteReceiverHeads {
        a: usize,
        b: usize,
    },
    /// softmax ratio geometry: the receiver standing rebased by `by` before the contact — the
    /// ratio family's temperature (rebase)
    ScaleReceiver {
        by: i64,
    },
    /// K/V weights: one presented+carried family withdrawn after the head rebases, where the layer
    /// builds its own (remove) — Station A's family intervention
    WithdrawKvFamily {
        family: usize,
    },
    /// V/O transport: two heads of the carried construction permuted before the output transport (permute)
    PermuteCarriedHeads {
        a: usize,
        b: usize,
    },
    /// residual standing: the retained standing withdrawn at the first re-entry (isolate the return)
    WithdrawResidualAtFirstReEntry,
    /// MLP/gated transport: the gated passage's columns `[from, from+span)` withdrawn after the GELU (remove)
    WithdrawGateSpan {
        from: usize,
        span: usize,
    },
    /// sliding versus global chronology: every key/value position but the last withdrawn (a window of one)
    KeepOnlyLastKeyPosition {
        tokens: usize,
    },
    /// KV reuse: one family of the SHARED presented+carried standings withdrawn at this shared
    /// layer only — separates the reuse from the weights (remove)
    WithdrawSharedKvFamily {
        family: usize,
    },
    /// output boundary: the columns `[from, from+span)` of the final normed standing withdrawn
    WithdrawFinalSpan {
        from: usize,
        span: usize,
    },
}

pub const IDENTITY_BANDS: &str = "identity band elements (intervention: no rotation)";
pub const HEAD_PERMUTATION: &str = "head permutation (intervention)";

/// The identity band elements: cos 1, sin 0 at the band grain, for every pair.
pub fn identity_bands(pairs: usize) -> Vec<((i64, i64), (i64, i64))> {
    let one = 1i64 << BAND_GRAIN;
    (0..pairs).map(|_| ((one, one), (0, 0))).collect()
}

/// The permutation of `blocks` swapping `a` and `b`.
pub fn swap_permutation(blocks: usize, a: usize, b: usize) -> Vec<usize> {
    (0..blocks)
        .map(|i| {
            if i == a {
                b
            } else if i == b {
                a
            } else {
                i
            }
        })
        .collect()
}

fn intervention_statement(kind: &str, detail: &str) -> String {
    format!("matched sibling: {kind} — {detail}; the caller's intervention, not a source law")
}

/// **One layer's deed**: the per-layer input predecessor (from `x0`) and the layer proper, as one
/// diagram, with the layer's species and K/V role bound from the source realization. Returns the
/// named occurrences a caller reads or releases: `X0`, `LAYER_RETURN`, `CONTACT`, and — where the
/// layer builds its own K/V — `K_STANDING` (after the chronology) and `V_STANDING` (after the
/// rebase), which an `OwnAndStore` layer releases for the shared layers.
#[allow(clippy::too_many_arguments)]
pub fn found_layer(
    layer: usize,
    entry: Entry,
    chart: Chart,
    scales: &(DyadicEnclosure, DyadicEnclosure),
    terms: SeriesAperture,
    layer_scalar: Dyadic,
    sibling: &Intervention,
    tokens: usize,
) -> Result<Founded, String> {
    let species = Species::of(layer);
    let role = KvRole::of(layer);
    let head = species.head_width();
    let eps = Dyadic::of_binary64_bits(EPS_BITS).map_err(|e| e.to_string())?;
    let c1 = Dyadic::of_binary64_bits(GELU_SCALE_BITS).map_err(|e| e.to_string())?;
    let c2 = Dyadic::of_binary64_bits(GELU_CUBIC_BITS).map_err(|e| e.to_string())?;
    let mut complex = PortedOperationComplex::new(&format!(
        "Gemma-4-E4B layer {layer} with its per-layer input, {} attention, K/V {role:?}",
        species.layer_type()
    ));
    let standing = complex.port("continuing standing, 2560");
    let ple = complex.port("per-layer section, 256");
    let receivers = complex.port(&format!("receiver chart, 8 heads x {head}"));
    let families = complex.port(&format!("presented/carried chart, 2 families x {head}"));
    let passage = complex.port("gated passage chart, 10240");
    let mut realization = ResidentRealization::default();
    let mut returns = BTreeMap::new();
    let n = |suffix: &str| named(layer, suffix);
    let layer_type_field = format!("layer_types[{layer}]");
    let head_field = match species {
        Species::Sliding => "head_dim",
        Species::Full => "global_head_dim",
    };
    let head_value = head.to_string();

    // --- the embedding x0: the per-layer predecessor re-enters it in every layer ---
    let x0 = law(
        &mut complex,
        "entering standing",
        OperationSpecies::Construction,
        vec![],
        vec![standing],
        Some(EMBED.to_owned()),
        vec![
            implementation(
                "Gemma4TextScaledWordEmbedding.forward (return super().forward(input_ids) * self.embed_scale.to(self.weight.dtype))",
            ),
            implementation("Gemma4TextModel.__init__ (embed_scale=self.config.hidden_size**0.5)"),
            configuration("hidden_size", "2560"),
            shape(EMBED, &[VOCABULARY, HIDDEN]),
        ],
    )?;
    realization.bind(
        x0,
        Enter {
            population: ENTERING.to_owned(),
            scale: EMBED_SCALE,
        },
    );
    returns.insert(X0, x0);
    let x0 = if let Intervention::WithdrawEmbeddingColumns { from, span } = sibling {
        let w = law(
            &mut complex,
            "initial embedding withdrawn (intervention)",
            OperationSpecies::Quotient,
            vec![standing],
            vec![standing],
            None,
            vec![intervention(&intervention_statement(
                "initial embedding",
                &format!("columns {from}..{} of x0 withdrawn", from + span),
            ))],
        )?;
        realization.bind(
            w,
            WithdrawColumns {
                from: *from,
                span: *span,
            },
        );
        bond(&mut complex, "x0 withdrawn", standing, x0, w, 0)?;
        w
    } else {
        x0
    };

    // --- the residual stream entering this layer ---
    let residual_in = match entry {
        Entry::Rows => x0,
        Entry::Carried => {
            let carried = law(
                &mut complex,
                "carried standing",
                OperationSpecies::Construction,
                vec![],
                vec![standing],
                None,
                vec![
                    implementation("Gemma4TextModel.forward (hidden_states = decoder_layer()"),
                    implementation(
                        "Gemma4TextModel.forward (for i, decoder_layer in enumerate(self.layers[: self.config.num_hidden_layers]):)",
                    ),
                ],
            )?;
            realization.bind(
                carried,
                Standing {
                    name: CARRIED_STANDING.to_owned(),
                },
            );
            carried
        }
    };

    // --- the per-layer input predecessor ---
    let projected = law(
        &mut complex,
        "per-layer model projection",
        OperationSpecies::Transport,
        vec![standing],
        vec![ple],
        Some(PLE_MODEL_PROJECTION.to_owned()),
        vec![
            implementation(
                "Gemma4TextModel.project_per_layer_inputs (per_layer_projection = self.per_layer_model_projection(inputs_embeds) * self.per_layer_model_projection_scale)",
            ),
            configuration("hidden_size_per_layer_input", "256"),
            configuration("num_hidden_layers", "42"),
            shape(PLE_MODEL_PROJECTION, &[LAYERS * PLE_WIDTH, HIDDEN]),
        ],
    )?;
    realization.bind(
        projected,
        Contract {
            population: PLE_MODEL_PROJECTION.to_owned(),
        },
    );
    bond(&mut complex, "x0 projects", standing, x0, projected, 0)?;
    let projected = seal(
        chart,
        &mut complex,
        &mut realization,
        projected,
        ple,
        "projected",
    )?;
    let scaled = law(
        &mut complex,
        "per-layer projection scale 2560^-1/2",
        OperationSpecies::Transport,
        vec![ple],
        vec![ple],
        None,
        vec![
            implementation(
                "Gemma4TextModel.__init__ (self.per_layer_model_projection_scale = config.hidden_size**-0.5)",
            ),
            configuration("hidden_size", "2560"),
        ],
    )?;
    realization.bind(scaled, Scale { by: scales.0 });
    bond(&mut complex, "projection scales", ple, projected, scaled, 0)?;
    let scaled = seal(chart, &mut complex, &mut realization, scaled, ple, "scaled")?;
    let normed = law(
        &mut complex,
        "per-layer projection norm",
        OperationSpecies::Transport,
        vec![ple],
        vec![ple],
        Some(PLE_PROJECTION_NORM.to_owned()),
        rebase_testimony(
            "Gemma4TextModel.project_per_layer_inputs (per_layer_projection = self.per_layer_projection_norm(per_layer_projection))",
            PLE_PROJECTION_NORM,
            PLE_WIDTH,
        ),
    )?;
    realization.bind(
        normed,
        RmsRebase {
            group: PLE_WIDTH,
            gain: Some(PLE_PROJECTION_NORM.to_owned()),
            eps,
        },
    );
    bond(&mut complex, "projection norms", ple, scaled, normed, 0)?;
    let normed = seal(chart, &mut complex, &mut realization, normed, ple, "normed")?;
    let token = law(
        &mut complex,
        "per-layer token identity",
        OperationSpecies::Construction,
        vec![],
        vec![ple],
        Some(PLE_EMBED.to_owned()),
        vec![
            implementation(
                "Gemma4TextModel.get_per_layer_inputs (return self.embed_tokens_per_layer(input_ids).reshape()",
            ),
            implementation(
                "Gemma4TextModel.__init__ (embed_scale=config.hidden_size_per_layer_input**0.5,)",
            ),
            configuration("hidden_size_per_layer_input", "256"),
            shape(PLE_EMBED, &[VOCABULARY, LAYERS * PLE_WIDTH]),
        ],
    )?;
    realization.bind(
        token,
        Enter {
            population: super::resident_layer::PLE_ENTERING.to_owned(),
            scale: PLE_EMBED_SCALE,
        },
    );
    let joined = law(
        &mut complex,
        "per-layer join",
        OperationSpecies::Construction,
        vec![ple, ple],
        vec![ple],
        None,
        vec![implementation(
            "Gemma4TextModel.project_per_layer_inputs (return (per_layer_projection + per_layer_inputs) * self.per_layer_input_scale)",
        )],
    )?;
    realization.bind(joined, ReEntry);
    bond(&mut complex, "join projection", ple, normed, joined, 0)?;
    bond(&mut complex, "join token", ple, token, joined, 1)?;
    let joined = seal(chart, &mut complex, &mut realization, joined, ple, "joined")?;
    let halved = law(
        &mut complex,
        "per-layer input scale 2^-1/2",
        OperationSpecies::Transport,
        vec![ple],
        vec![ple],
        None,
        vec![implementation(
            "Gemma4TextModel.__init__ (self.per_layer_input_scale = 2.0**-0.5)",
        )],
    )?;
    realization.bind(halved, Scale { by: scales.1 });
    bond(&mut complex, "join scales", ple, joined, halved, 0)?;
    let halved = seal(chart, &mut complex, &mut realization, halved, ple, "halved")?;
    let halved = if matches!(sibling, Intervention::WithdrawPle) {
        let w = law(
            &mut complex,
            "per-layer input withdrawn (intervention)",
            OperationSpecies::Quotient,
            vec![ple],
            vec![ple],
            None,
            vec![intervention(&intervention_statement(
                "per-layer embedding",
                "the layer's PLE section withdrawn whole",
            ))],
        )?;
        realization.bind(
            w,
            WithdrawColumns {
                from: 0,
                span: PLE_WIDTH,
            },
        );
        bond(&mut complex, "ple withdrawn", ple, halved, w, 0)?;
        w
    } else {
        halved
    };
    returns.insert(PLE_SECTION, halved);

    // --- the layer ---
    let decoder = "Gemma4TextDecoderLayer.forward";
    let rebase_in = if let Intervention::ScaleBeforeInputRebase { by } = sibling {
        let sc = law(
            &mut complex,
            "standing rebased before the input rebase (intervention)",
            OperationSpecies::Transport,
            vec![standing],
            vec![standing],
            None,
            vec![intervention(&intervention_statement(
                "normalization, rebase before",
                &format!(
                    "the standing multiplied by {by} before the input rebase: a gauge the norm quotients away up to its epsilon"
                ),
            ))],
        )?;
        realization.bind(
            sc,
            Scale {
                by: DyadicEnclosure {
                    lo: *by,
                    hi: *by,
                    grain: 0,
                },
            },
        );
        bond(&mut complex, "rebased before", standing, residual_in, sc, 0)?;
        sc
    } else {
        residual_in
    };
    let rebased = law(
        &mut complex,
        "input rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("input_layernorm.weight")),
        rebase_testimony(
            "Gemma4TextDecoderLayer.forward (hidden_states = self.input_layernorm(hidden_states))",
            &n("input_layernorm.weight"),
            HIDDEN,
        ),
    )?;
    realization.bind(
        rebased,
        RmsRebase {
            group: HIDDEN,
            gain: Some(n("input_layernorm.weight")),
            eps,
        },
    );
    bond(
        &mut complex,
        "standing rebases",
        standing,
        rebase_in,
        rebased,
        0,
    )?;
    let rebased = seal(
        chart,
        &mut complex,
        &mut realization,
        rebased,
        standing,
        "rebased",
    )?;
    let rebased = if let Intervention::ScaleAfterInputRebase { by } = sibling {
        let sc = law(
            &mut complex,
            "standing rebased after the input rebase (intervention)",
            OperationSpecies::Transport,
            vec![standing],
            vec![standing],
            None,
            vec![intervention(&intervention_statement(
                "normalization, rebase after",
                &format!("the rebased standing multiplied by {by}"),
            ))],
        )?;
        realization.bind(
            sc,
            Scale {
                by: DyadicEnclosure {
                    lo: *by,
                    hi: *by,
                    grain: 0,
                },
            },
        );
        bond(&mut complex, "rebased after", standing, rebased, sc, 0)?;
        sc
    } else {
        rebased
    };

    // the receiver projection, always the layer's own
    let q = law(
        &mut complex,
        "receiver projection",
        OperationSpecies::Transport,
        vec![standing],
        vec![receivers],
        Some(n("self_attn.q_proj.weight")),
        vec![
            implementation(
                "Gemma4TextAttention.forward (query_states = self.q_proj(hidden_states).view(hidden_shape))",
            ),
            implementation(
                "Gemma4TextAttention.__init__ (self.head_dim = config.global_head_dim if not self.is_sliding and config.global_head_dim else config.head_dim)",
            ),
            configuration("num_attention_heads", "8"),
            configuration("num_key_value_heads", "2"),
            configuration(head_field, &head_value),
            configuration(&layer_type_field, species.layer_type()),
            shape(&n("self_attn.q_proj.weight"), &[HEADS * head, HIDDEN]),
        ],
    )?;
    realization.bind(
        q,
        Contract {
            population: n("self_attn.q_proj.weight"),
        },
    );
    bond(&mut complex, "receiver projection", standing, rebased, q, 0)?;
    let q = seal(chart, &mut complex, &mut realization, q, receivers, "q")?;
    let qn = law(
        &mut complex,
        "receiver head rebase",
        OperationSpecies::Transport,
        vec![receivers],
        vec![receivers],
        Some(n("self_attn.q_norm.weight")),
        {
            let mut t = rebase_testimony(
                "Gemma4TextAttention.forward (query_states = self.q_norm(query_states))",
                &n("self_attn.q_norm.weight"),
                head,
            );
            t.push(implementation("Gemma4TextAttention.__init__ (self.q_norm = Gemma4RMSNorm(dim=self.head_dim, eps=config.rms_norm_eps))"));
            t
        },
    )?;
    realization.bind(
        qn,
        RmsRebase {
            group: head,
            gain: Some(n("self_attn.q_norm.weight")),
            eps,
        },
    );
    bond(&mut complex, "q rebases", receivers, q, qn, 0)?;
    let qn = seal(chart, &mut complex, &mut realization, qn, receivers, "qn")?;

    let chronology_testimony = |site: &str| {
        let mut t = vec![
            implementation(site),
            implementation("apply_rotary_pos_emb (return (x * cos) + (rotate_half(x) * sin))"),
            implementation("rotate_half (return torch.cat((-x2, x1), dim=-1))"),
            implementation(
                "Gemma4TextRotaryEmbedding.forward (emb = torch.cat((freqs, freqs), dim=-1))",
            ),
            configuration(&layer_type_field, species.layer_type()),
            configuration("num_attention_heads", "8"),
            configuration("num_key_value_heads", "2"),
            configuration(head_field, &head_value),
        ];
        match species {
            Species::Sliding => {
                t.push(implementation("Gemma4TextRotaryEmbedding.compute_default_rope_parameters (base ** (torch.arange(0, dim, 2, dtype=torch.int64))"));
                t.push(configuration(
                    "rope_parameters.sliding_attention.rope_type",
                    "default",
                ));
                t.push(configuration(
                    "rope_parameters.sliding_attention.rope_theta",
                    "10000.0",
                ));
            }
            Species::Full => {
                t.push(implementation("Gemma4TextRotaryEmbedding.__init__ (if layer_type == \"full_attention\" and rope_type == \"proportional\":)"));
                t.push(implementation("Gemma4TextRotaryEmbedding.__init__ (rope_init_fn_kwargs[\"head_dim_key\"] = \"global_head_dim\")"));
                t.push(configuration(
                    "rope_parameters.full_attention.rope_type",
                    "proportional",
                ));
                t.push(configuration(
                    "rope_parameters.full_attention.rope_theta",
                    "1000000.0",
                ));
                t.push(configuration(
                    "rope_parameters.full_attention.partial_rotary_factor",
                    "0.25",
                ));
            }
        }
        t
    };
    let chronology_intervened = matches!(
        sibling,
        Intervention::IdentityChronology | Intervention::ReversedPositions
    );
    let bands_name = if matches!(sibling, Intervention::IdentityChronology) {
        IDENTITY_BANDS.to_owned()
    } else {
        species.bands().to_owned()
    };
    let chronology_law_testimony =
        |site: &str| -> Vec<holonic_engine::ported_operation::SourceTestimony> {
            match sibling {
                Intervention::IdentityChronology => vec![intervention(&intervention_statement(
                    "chronology replaced",
                    "the band elements replaced by the identity: no rotation",
                ))],
                Intervention::ReversedPositions => vec![intervention(&intervention_statement(
                    "chronology permuted",
                    "the positions reversed",
                ))],
                _ => chronology_testimony(site),
            }
        };
    let qr = law(
        &mut complex,
        if chronology_intervened {
            "receiver chronology (intervention)"
        } else {
            "receiver chronology"
        },
        OperationSpecies::Transport,
        vec![receivers],
        vec![receivers],
        None,
        chronology_law_testimony(
            "Gemma4TextAttention.forward (query_states = apply_rotary_pos_emb(query_states, cos, sin, unsqueeze_dim=2))",
        ),
    )?;
    realization.bind(
        qr,
        Chronology {
            bands: bands_name.clone(),
            heads: HEADS,
            head_width: head,
        },
    );
    bond(&mut complex, "q turns", receivers, qn, qr, 0)?;
    let qr = seal(chart, &mut complex, &mut realization, qr, receivers, "qr")?;
    let qr = match sibling {
        Intervention::PermuteReceiverHeads { a, b } => {
            let pm = law(
                &mut complex,
                "receiver heads permuted (intervention)",
                OperationSpecies::Transport,
                vec![receivers],
                vec![receivers],
                None,
                vec![intervention(&intervention_statement(
                    "Q/K contact permuted",
                    &format!("receiver heads {a} and {b} swapped after the chronology"),
                ))],
            )?;
            realization.bind(
                pm,
                PermuteColumns {
                    block: head,
                    permutation: swap_permutation(HEADS, *a, *b),
                    mounted: HEAD_PERMUTATION.to_owned(),
                },
            );
            bond(&mut complex, "q heads permuted", receivers, qr, pm, 0)?;
            pm
        }
        Intervention::ScaleReceiver { by } => {
            let sc = law(
                &mut complex,
                "receiver rebased before the contact (intervention)",
                OperationSpecies::Transport,
                vec![receivers],
                vec![receivers],
                None,
                vec![intervention(&intervention_statement(
                    "softmax ratio geometry",
                    &format!(
                        "the receiver standing multiplied by {by}: the ratio family's temperature"
                    ),
                ))],
            )?;
            realization.bind(
                sc,
                Scale {
                    by: DyadicEnclosure {
                        lo: *by,
                        hi: *by,
                        grain: 0,
                    },
                },
            );
            bond(&mut complex, "q rebased", receivers, qr, sc, 0)?;
            sc
        }
        _ => qr,
    };

    // the presented and carried standings: the layer's own, or the stored ones
    let (k_in, v_in) = match role {
        KvRole::Own | KvRole::OwnAndStore => {
            let k = law(
                &mut complex,
                "presented projection",
                OperationSpecies::Transport,
                vec![standing],
                vec![families],
                Some(n("self_attn.k_proj.weight")),
                vec![
                    implementation(
                        "Gemma4TextAttention.forward (key_states = self.k_proj(hidden_states).view(hidden_shape))",
                    ),
                    implementation(
                        "Gemma4TextAttention.__init__ (if not self.is_kv_shared_layer:)",
                    ),
                    configuration("num_key_value_heads", "2"),
                    configuration(head_field, &head_value),
                    configuration("num_kv_shared_layers", "18"),
                    shape(&n("self_attn.k_proj.weight"), &[KV_HEADS * head, HIDDEN]),
                ],
            )?;
            realization.bind(
                k,
                Contract {
                    population: n("self_attn.k_proj.weight"),
                },
            );
            bond(
                &mut complex,
                "presented projection",
                standing,
                rebased,
                k,
                0,
            )?;
            let k = seal(chart, &mut complex, &mut realization, k, families, "k")?;
            let v = law(
                &mut complex,
                "carried projection",
                OperationSpecies::Transport,
                vec![standing],
                vec![families],
                Some(n("self_attn.v_proj.weight")),
                vec![
                    implementation(
                        "Gemma4TextAttention.forward (value_states = self.v_proj(hidden_states).view(hidden_shape) if self.v_proj is not None else key_states)",
                    ),
                    implementation(
                        "Gemma4TextAttention.__init__ (if not self.is_kv_shared_layer:)",
                    ),
                    configuration("num_key_value_heads", "2"),
                    configuration(head_field, &head_value),
                    configuration("attention_k_eq_v", "false"),
                    shape(&n("self_attn.v_proj.weight"), &[KV_HEADS * head, HIDDEN]),
                ],
            )?;
            realization.bind(
                v,
                Contract {
                    population: n("self_attn.v_proj.weight"),
                },
            );
            bond(&mut complex, "carried projection", standing, rebased, v, 0)?;
            let v = seal(chart, &mut complex, &mut realization, v, families, "v")?;
            let kn = law(
                &mut complex,
                "presented head rebase",
                OperationSpecies::Transport,
                vec![families],
                vec![families],
                Some(n("self_attn.k_norm.weight")),
                {
                    let mut t = rebase_testimony(
                        "Gemma4TextAttention.forward (key_states = self.k_norm(key_states))",
                        &n("self_attn.k_norm.weight"),
                        head,
                    );
                    t.push(implementation("Gemma4TextAttention.__init__ (self.k_norm = Gemma4RMSNorm(dim=self.head_dim, eps=config.rms_norm_eps))"));
                    t
                },
            )?;
            realization.bind(
                kn,
                RmsRebase {
                    group: head,
                    gain: Some(n("self_attn.k_norm.weight")),
                    eps,
                },
            );
            bond(&mut complex, "k rebases", families, k, kn, 0)?;
            let kn = seal(chart, &mut complex, &mut realization, kn, families, "kn")?;
            let vn = law(
                &mut complex,
                "carried head rebase, no gain",
                OperationSpecies::Transport,
                vec![families],
                vec![families],
                None,
                vec![
                    implementation(
                        "Gemma4TextAttention.forward (value_states = self.v_norm(value_states))",
                    ),
                    implementation(
                        "Gemma4TextAttention.__init__ (self.v_norm = Gemma4RMSNorm(self.head_dim, eps=config.rms_norm_eps, with_scale=False))",
                    ),
                    implementation(
                        "Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))",
                    ),
                    configuration("rms_norm_eps", "1e-06"),
                    configuration(head_field, &head_value),
                ],
            )?;
            realization.bind(
                vn,
                RmsRebase {
                    group: head,
                    gain: None,
                    eps,
                },
            );
            bond(&mut complex, "v rebases", families, v, vn, 0)?;
            let vn = seal(chart, &mut complex, &mut realization, vn, families, "vn")?;
            let (k_source, v_source) = match sibling {
                Intervention::WithdrawKvFamily { family } => {
                    let ka = law(
                        &mut complex,
                        "presented family withdrawn (intervention)",
                        OperationSpecies::Quotient,
                        vec![families],
                        vec![families],
                        None,
                        vec![intervention(&format!(
                            "matched sibling: presented family {family} withdrawn after its head rebase; not a source law"
                        ))],
                    )?;
                    realization.bind(
                        ka,
                        WithdrawColumns {
                            from: family * head,
                            span: head,
                        },
                    );
                    bond(&mut complex, "k withdrawn", families, kn, ka, 0)?;
                    let va = law(
                        &mut complex,
                        "carried family withdrawn (intervention)",
                        OperationSpecies::Quotient,
                        vec![families],
                        vec![families],
                        None,
                        vec![intervention(&format!(
                            "matched sibling: carried family {family} withdrawn after its head rebase; not a source law"
                        ))],
                    )?;
                    realization.bind(
                        va,
                        WithdrawColumns {
                            from: family * head,
                            span: head,
                        },
                    );
                    bond(&mut complex, "v withdrawn", families, vn, va, 0)?;
                    (ka, va)
                }
                _ => (kn, vn),
            };
            let kr = law(
                &mut complex,
                if chronology_intervened {
                    "presented chronology (intervention)"
                } else {
                    "presented chronology"
                },
                OperationSpecies::Transport,
                vec![families],
                vec![families],
                None,
                chronology_law_testimony(
                    "Gemma4TextAttention.forward (key_states = apply_rotary_pos_emb(key_states, cos, sin, unsqueeze_dim=2))",
                ),
            )?;
            realization.bind(
                kr,
                Chronology {
                    bands: bands_name.clone(),
                    heads: KV_HEADS,
                    head_width: head,
                },
            );
            bond(&mut complex, "k turns", families, k_source, kr, 0)?;
            let kr = seal(chart, &mut complex, &mut realization, kr, families, "kr")?;
            returns.insert(K_STANDING, kr);
            returns.insert(V_STANDING, v_source);
            (kr, v_source)
        }
        KvRole::Shared => {
            let (k_name, v_name) = match species {
                Species::Sliding => (SHARED_K_SLIDING, SHARED_V_SLIDING),
                Species::Full => (SHARED_K_FULL, SHARED_V_FULL),
            };
            let k = law(
                &mut complex,
                "shared presented standing",
                OperationSpecies::Construction,
                vec![],
                vec![families],
                None,
                vec![
                    implementation(
                        "Gemma4TextAttention.forward (key_states, value_states = shared_kv_states[self.layer_type])",
                    ),
                    implementation(
                        "Gemma4TextAttention.__init__ (self.is_kv_shared_layer = layer_idx >= first_kv_shared_layer_idx >= 0)",
                    ),
                    implementation(
                        "Gemma4TextAttention.__init__ (first_kv_shared_layer_idx = self.config.num_hidden_layers - getattr(self.config, \"num_kv_shared_layers\", 0))",
                    ),
                    configuration("num_kv_shared_layers", "18"),
                    configuration("num_hidden_layers", "42"),
                    configuration(&layer_type_field, species.layer_type()),
                ],
            )?;
            realization.bind(
                k,
                Standing {
                    name: k_name.to_owned(),
                },
            );
            let v = law(
                &mut complex,
                "shared carried standing",
                OperationSpecies::Construction,
                vec![],
                vec![families],
                None,
                vec![
                    implementation(
                        "Gemma4TextAttention.forward (key_states, value_states = shared_kv_states[self.layer_type])",
                    ),
                    implementation("Gemma4TextAttention.forward (if self.store_full_length_kv:)"),
                    implementation(
                        "Gemma4TextAttention.forward (shared_kv_states[self.layer_type] = key_states, value_states)",
                    ),
                    configuration("num_kv_shared_layers", "18"),
                    configuration(&layer_type_field, species.layer_type()),
                ],
            )?;
            realization.bind(
                v,
                Standing {
                    name: v_name.to_owned(),
                },
            );
            (k, v)
        }
    };

    // the K/V interventions at the contact's presented and carried inputs
    let (k_in, v_in) = match sibling {
        Intervention::WithdrawSharedKvFamily { family } if role == KvRole::Shared => {
            let ka = law(
                &mut complex,
                "shared presented family withdrawn (intervention)",
                OperationSpecies::Quotient,
                vec![families],
                vec![families],
                None,
                vec![intervention(&intervention_statement(
                    "KV reuse",
                    &format!(
                        "shared presented family {family} withdrawn at this shared layer only"
                    ),
                ))],
            )?;
            realization.bind(
                ka,
                WithdrawColumns {
                    from: family * head,
                    span: head,
                },
            );
            bond(&mut complex, "shared k withdrawn", families, k_in, ka, 0)?;
            let va = law(
                &mut complex,
                "shared carried family withdrawn (intervention)",
                OperationSpecies::Quotient,
                vec![families],
                vec![families],
                None,
                vec![intervention(&intervention_statement(
                    "KV reuse",
                    &format!("shared carried family {family} withdrawn at this shared layer only"),
                ))],
            )?;
            realization.bind(
                va,
                WithdrawColumns {
                    from: family * head,
                    span: head,
                },
            );
            bond(&mut complex, "shared v withdrawn", families, v_in, va, 0)?;
            (ka, va)
        }
        Intervention::KeepOnlyLastKeyPosition { tokens: t } if *t > 1 => {
            let ka = law(
                &mut complex,
                "key positions but the last withdrawn (intervention)",
                OperationSpecies::Quotient,
                vec![families],
                vec![families],
                None,
                vec![intervention(&intervention_statement(
                    "chronology window",
                    &format!(
                        "positions 0..{} of the presented standing withdrawn: a window of one",
                        t - 1
                    ),
                ))],
            )?;
            realization.bind(
                ka,
                WithdrawRows {
                    from: 0,
                    span: t - 1,
                },
            );
            bond(&mut complex, "k positions withdrawn", families, k_in, ka, 0)?;
            let va = law(
                &mut complex,
                "value positions but the last withdrawn (intervention)",
                OperationSpecies::Quotient,
                vec![families],
                vec![families],
                None,
                vec![intervention(&intervention_statement(
                    "chronology window",
                    &format!("positions 0..{} of the carried standing withdrawn", t - 1),
                ))],
            )?;
            realization.bind(
                va,
                WithdrawRows {
                    from: 0,
                    span: t - 1,
                },
            );
            bond(&mut complex, "v positions withdrawn", families, v_in, va, 0)?;
            (ka, va)
        }
        _ => (k_in, v_in),
    };
    let mut contact_testimony = vec![
        implementation(
            "eager_attention_forward (attn_weights = torch.matmul(query, key_states.transpose(2, 3)) * scaling)",
        ),
        implementation(
            "eager_attention_forward (attn_weights = nn.functional.softmax(attn_weights, dim=-1, dtype=torch.float32).to(query.dtype))",
        ),
        implementation(
            "eager_attention_forward (attn_output = torch.matmul(attn_weights, value_states))",
        ),
        implementation("Gemma4TextAttention.__init__ (self.scaling = 1.0)"),
        implementation(
            "Gemma4TextAttention.__init__ (self.sliding_window = config.sliding_window if self.is_sliding else None)",
        ),
        implementation(
            "Gemma4TextAttention.__init__ (self.num_key_value_groups = config.num_attention_heads // num_key_value_heads)",
        ),
        implementation(
            "repeat_kv (hidden_states = hidden_states[:, :, None, :, :].expand(batch, num_key_value_heads, n_rep, slen, head_dim))",
        ),
        configuration("num_attention_heads", "8"),
        configuration("num_key_value_heads", "2"),
        configuration(head_field, &head_value),
        configuration(&layer_type_field, species.layer_type()),
    ];
    let window = match species {
        Species::Sliding => {
            contact_testimony.push(configuration("sliding_window", "512"));
            SLIDING_WINDOW
        }
        Species::Full => tokens.max(1),
    };
    let contact = law(
        &mut complex,
        "contact and carried construction",
        OperationSpecies::Construction,
        vec![receivers, families, families],
        vec![receivers],
        None,
        contact_testimony,
    )?;
    realization.bind(
        contact,
        Contact {
            heads: HEADS,
            kv_heads: KV_HEADS,
            head_width: head,
            window,
            terms,
            partition: None,
            partition_reach: None,
            partition_reach_sum: None,
        },
    );
    bond(&mut complex, "contact receiver", receivers, qr, contact, 0)?;
    bond(
        &mut complex,
        "contact presented",
        families,
        k_in,
        contact,
        1,
    )?;
    bond(&mut complex, "contact carried", families, v_in, contact, 2)?;
    let contact = seal(
        chart,
        &mut complex,
        &mut realization,
        contact,
        receivers,
        "contact",
    )?;
    returns.insert(CONTACT, contact);
    let contact = if let Intervention::PermuteCarriedHeads { a, b } = sibling {
        let pm = law(
            &mut complex,
            "carried heads permuted before the output transport (intervention)",
            OperationSpecies::Transport,
            vec![receivers],
            vec![receivers],
            None,
            vec![intervention(&intervention_statement(
                "V/O transport permuted",
                &format!("heads {a} and {b} of the carried construction swapped before o_proj"),
            ))],
        )?;
        realization.bind(
            pm,
            PermuteColumns {
                block: head,
                permutation: swap_permutation(HEADS, *a, *b),
                mounted: HEAD_PERMUTATION.to_owned(),
            },
        );
        bond(
            &mut complex,
            "carried heads permuted",
            receivers,
            contact,
            pm,
            0,
        )?;
        pm
    } else {
        contact
    };

    let o = law(
        &mut complex,
        "contact returns",
        OperationSpecies::Transport,
        vec![receivers],
        vec![standing],
        Some(n("self_attn.o_proj.weight")),
        vec![
            implementation("Gemma4TextAttention.forward (attn_output = self.o_proj(attn_output))"),
            shape(&n("self_attn.o_proj.weight"), &[HIDDEN, HEADS * head]),
        ],
    )?;
    realization.bind(
        o,
        Contract {
            population: n("self_attn.o_proj.weight"),
        },
    );
    bond(
        &mut complex,
        "contact projects back",
        receivers,
        contact,
        o,
        0,
    )?;
    let o = seal(chart, &mut complex, &mut realization, o, standing, "o")?;
    let on = law(
        &mut complex,
        "post-attention rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("post_attention_layernorm.weight")),
        rebase_testimony(
            "Gemma4TextDecoderLayer.forward (hidden_states = self.post_attention_layernorm(hidden_states))",
            &n("post_attention_layernorm.weight"),
            HIDDEN,
        ),
    )?;
    realization.bind(
        on,
        RmsRebase {
            group: HIDDEN,
            gain: Some(n("post_attention_layernorm.weight")),
            eps,
        },
    );
    bond(&mut complex, "return rebases", standing, o, on, 0)?;
    let on = seal(chart, &mut complex, &mut realization, on, standing, "on")?;
    let retained = if matches!(sibling, Intervention::WithdrawResidualAtFirstReEntry) {
        let w = law(
            &mut complex,
            "retained standing withdrawn at the first re-entry (intervention)",
            OperationSpecies::Quotient,
            vec![standing],
            vec![standing],
            None,
            vec![intervention(&intervention_statement(
                "residual standing",
                "the retained standing withdrawn whole at the first re-entry: the return stands alone",
            ))],
        )?;
        realization.bind(
            w,
            WithdrawColumns {
                from: 0,
                span: HIDDEN,
            },
        );
        bond(
            &mut complex,
            "residual withdrawn",
            standing,
            residual_in,
            w,
            0,
        )?;
        w
    } else {
        residual_in
    };
    let r1 = law(
        &mut complex,
        "first re-entry",
        OperationSpecies::Construction,
        vec![standing, standing],
        vec![standing],
        None,
        vec![implementation(&format!(
            "{decoder} (hidden_states = residual + hidden_states)"
        ))],
    )?;
    realization.bind(r1, ReEntry);
    bond(
        &mut complex,
        "re-entry retains the standing",
        standing,
        retained,
        r1,
        0,
    )?;
    bond(&mut complex, "re-entry returns", standing, on, r1, 1)?;
    let r1 = seal(chart, &mut complex, &mut realization, r1, standing, "r1")?;

    let h2 = law(
        &mut complex,
        "pre-feedforward rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("pre_feedforward_layernorm.weight")),
        rebase_testimony(
            "Gemma4TextDecoderLayer.forward (hidden_states = self.pre_feedforward_layernorm(hidden_states))",
            &n("pre_feedforward_layernorm.weight"),
            HIDDEN,
        ),
    )?;
    realization.bind(
        h2,
        RmsRebase {
            group: HIDDEN,
            gain: Some(n("pre_feedforward_layernorm.weight")),
            eps,
        },
    );
    bond(&mut complex, "r1 rebases", standing, r1, h2, 0)?;
    let h2 = seal(chart, &mut complex, &mut realization, h2, standing, "h2")?;
    let mut branches = Vec::new();
    for (what, suffix) in [
        ("gate", "mlp.gate_proj.weight"),
        ("up", "mlp.up_proj.weight"),
    ] {
        let event = law(
            &mut complex,
            what,
            OperationSpecies::Transport,
            vec![standing],
            vec![passage],
            Some(n(suffix)),
            vec![
                implementation(
                    "Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))",
                ),
                configuration("intermediate_size", "10240"),
                shape(&n(suffix), &[FFN, HIDDEN]),
            ],
        )?;
        realization.bind(
            event,
            Contract {
                population: n(suffix),
            },
        );
        bond(&mut complex, what, standing, h2, event, 0)?;
        let event = seal(chart, &mut complex, &mut realization, event, passage, what)?;
        branches.push(event);
    }
    let gated = law(
        &mut complex,
        "gate turns",
        OperationSpecies::Transport,
        vec![passage],
        vec![passage],
        None,
        vec![
            implementation(
                "Gemma4TextMLP.__init__ (self.act_fn = ACT2FN[config.hidden_activation])",
            ),
            implementation(
                "Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))",
            ),
            configuration("hidden_activation", "gelu_pytorch_tanh"),
        ],
    )?;
    realization.bind(gated, GeluTanh { c1, c2, terms });
    bond(&mut complex, "gate turns", passage, branches[0], gated, 0)?;
    let gated = seal(
        chart,
        &mut complex,
        &mut realization,
        gated,
        passage,
        "gated",
    )?;
    let gated = if let Intervention::WithdrawGateSpan { from, span } = sibling {
        let w = law(
            &mut complex,
            "gated passage span withdrawn (intervention)",
            OperationSpecies::Quotient,
            vec![passage],
            vec![passage],
            None,
            vec![intervention(&intervention_statement(
                "MLP/gated transport",
                &format!(
                    "columns {from}..{} of the gated passage withdrawn after the GELU",
                    from + span
                ),
            ))],
        )?;
        realization.bind(
            w,
            WithdrawColumns {
                from: *from,
                span: *span,
            },
        );
        bond(&mut complex, "gate span withdrawn", passage, gated, w, 0)?;
        w
    } else {
        gated
    };
    let admitted = law(
        &mut complex,
        "gate admits",
        OperationSpecies::Construction,
        vec![passage, passage],
        vec![passage],
        None,
        vec![implementation(
            "Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))",
        )],
    )?;
    realization.bind(admitted, Hadamard);
    bond(&mut complex, "admits gate", passage, gated, admitted, 0)?;
    bond(&mut complex, "admits up", passage, branches[1], admitted, 1)?;
    let admitted = seal(
        chart,
        &mut complex,
        &mut realization,
        admitted,
        passage,
        "admitted",
    )?;
    let down = law(
        &mut complex,
        "passage returns",
        OperationSpecies::Transport,
        vec![passage],
        vec![standing],
        Some(n("mlp.down_proj.weight")),
        vec![
            implementation(
                "Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))",
            ),
            shape(&n("mlp.down_proj.weight"), &[HIDDEN, FFN]),
        ],
    )?;
    realization.bind(
        down,
        Contract {
            population: n("mlp.down_proj.weight"),
        },
    );
    bond(&mut complex, "passage returns", passage, admitted, down, 0)?;
    let down = seal(
        chart,
        &mut complex,
        &mut realization,
        down,
        standing,
        "down",
    )?;
    let dn = law(
        &mut complex,
        "post-feedforward rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("post_feedforward_layernorm.weight")),
        rebase_testimony(
            "Gemma4TextDecoderLayer.forward (hidden_states = self.post_feedforward_layernorm(hidden_states))",
            &n("post_feedforward_layernorm.weight"),
            HIDDEN,
        ),
    )?;
    realization.bind(
        dn,
        RmsRebase {
            group: HIDDEN,
            gain: Some(n("post_feedforward_layernorm.weight")),
            eps,
        },
    );
    bond(&mut complex, "down rebases", standing, down, dn, 0)?;
    let dn = seal(chart, &mut complex, &mut realization, dn, standing, "dn")?;
    let r2 = law(
        &mut complex,
        "second re-entry",
        OperationSpecies::Construction,
        vec![standing, standing],
        vec![standing],
        None,
        vec![implementation(&format!(
            "{decoder} (hidden_states = residual + hidden_states)"
        ))],
    )?;
    realization.bind(r2, ReEntry);
    bond(&mut complex, "second re-entry retains", standing, r1, r2, 0)?;
    bond(&mut complex, "second re-entry returns", standing, dn, r2, 1)?;
    let r2 = seal(chart, &mut complex, &mut realization, r2, standing, "r2")?;

    // the PLE branch, in the source's own order
    let pg = law(
        &mut complex,
        "per-layer input gate",
        OperationSpecies::Transport,
        vec![standing],
        vec![ple],
        Some(n("per_layer_input_gate.weight")),
        vec![
            implementation(&format!(
                "{decoder} (hidden_states = self.per_layer_input_gate(hidden_states))"
            )),
            shape(&n("per_layer_input_gate.weight"), &[PLE_WIDTH, HIDDEN]),
        ],
    )?;
    realization.bind(
        pg,
        Contract {
            population: n("per_layer_input_gate.weight"),
        },
    );
    bond(&mut complex, "r2 gates", standing, r2, pg, 0)?;
    let pg = seal(chart, &mut complex, &mut realization, pg, ple, "pg")?;
    let pga = law(
        &mut complex,
        "per-layer gate turns",
        OperationSpecies::Transport,
        vec![ple],
        vec![ple],
        None,
        vec![
            implementation(&format!(
                "{decoder} (hidden_states = self.act_fn(hidden_states))"
            )),
            implementation(
                "Gemma4TextDecoderLayer.__init__ (self.act_fn = ACT2FN[config.hidden_activation])",
            ),
            configuration("hidden_activation", "gelu_pytorch_tanh"),
        ],
    )?;
    realization.bind(pga, GeluTanh { c1, c2, terms });
    bond(&mut complex, "per-layer gate turns", ple, pg, pga, 0)?;
    let pga = seal(chart, &mut complex, &mut realization, pga, ple, "pga")?;
    let pm = law(
        &mut complex,
        "per-layer gate admits the input",
        OperationSpecies::Construction,
        vec![ple, ple],
        vec![ple],
        None,
        vec![implementation(&format!(
            "{decoder} (hidden_states = hidden_states * per_layer_input)"
        ))],
    )?;
    realization.bind(pm, Hadamard);
    bond(&mut complex, "admits gate", ple, pga, pm, 0)?;
    bond(&mut complex, "admits per-layer input", ple, halved, pm, 1)?;
    let pm = seal(chart, &mut complex, &mut realization, pm, ple, "pm")?;
    let pp = law(
        &mut complex,
        "per-layer projection",
        OperationSpecies::Transport,
        vec![ple],
        vec![standing],
        Some(n("per_layer_projection.weight")),
        vec![
            implementation(&format!(
                "{decoder} (hidden_states = self.per_layer_projection(hidden_states))"
            )),
            shape(&n("per_layer_projection.weight"), &[HIDDEN, PLE_WIDTH]),
        ],
    )?;
    realization.bind(
        pp,
        Contract {
            population: n("per_layer_projection.weight"),
        },
    );
    bond(&mut complex, "per-layer projects", ple, pm, pp, 0)?;
    let pp = seal(chart, &mut complex, &mut realization, pp, standing, "pp")?;
    let ppn = law(
        &mut complex,
        "post per-layer input rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("post_per_layer_input_norm.weight")),
        rebase_testimony(
            "Gemma4TextDecoderLayer.forward (hidden_states = self.post_per_layer_input_norm(hidden_states))",
            &n("post_per_layer_input_norm.weight"),
            HIDDEN,
        ),
    )?;
    realization.bind(
        ppn,
        RmsRebase {
            group: HIDDEN,
            gain: Some(n("post_per_layer_input_norm.weight")),
            eps,
        },
    );
    bond(&mut complex, "per-layer rebases", standing, pp, ppn, 0)?;
    let ppn = seal(chart, &mut complex, &mut realization, ppn, standing, "ppn")?;
    let r3 = law(
        &mut complex,
        "third re-entry",
        OperationSpecies::Construction,
        vec![standing, standing],
        vec![standing],
        None,
        vec![implementation(&format!(
            "{decoder} (hidden_states = residual + hidden_states)"
        ))],
    )?;
    realization.bind(r3, ReEntry);
    bond(&mut complex, "third re-entry retains", standing, r2, r3, 0)?;
    bond(&mut complex, "third re-entry returns", standing, ppn, r3, 1)?;
    let r3 = seal(chart, &mut complex, &mut realization, r3, standing, "r3")?;
    let out = law(
        &mut complex,
        "layer scalar",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(n("layer_scalar")),
        vec![
            implementation(&format!("{decoder} (hidden_states *= self.layer_scalar)")),
            shape(&n("layer_scalar"), &[1]),
        ],
    )?;
    realization.bind(
        out,
        Scale {
            by: point_enclosure(layer_scalar),
        },
    );
    bond(&mut complex, "layer scales", standing, r3, out, 0)?;
    returns.insert(LAYER_ENCLOSURE, out);
    let out = seal(chart, &mut complex, &mut realization, out, standing, "out")?;
    returns.insert(LAYER_RETURN, out);

    Ok(Founded {
        complex,
        realization,
        returns,
    })
}

/// **The final deed**: the residual stream released by layer 41 enters as a standing, the final
/// normalization applies, and the tied output boundary contracts through `embed_tokens` read in the
/// other direction — the illicial potential section over the whole vocabulary, one row per token.
/// `final_logit_softcapping = 30` is a strictly monotone transformation of every coordinate, so the
/// order faces of this section are its order faces; it is reported, not enacted.
pub fn found_final(
    chart: Chart,
    sibling: &Intervention,
    scales_unused: &(DyadicEnclosure, DyadicEnclosure),
) -> Result<Founded, String> {
    let _ = scales_unused;
    let eps = Dyadic::of_binary64_bits(EPS_BITS).map_err(|e| e.to_string())?;
    let mut complex =
        PortedOperationComplex::new("Gemma-4-E4B final normalization and tied output boundary");
    let standing = complex.port("continuing standing, 2560");
    let vocabulary = complex.port("potential section, 262144");
    let mut realization = ResidentRealization::default();
    let mut returns = BTreeMap::new();
    let carried = law(
        &mut complex,
        "carried standing",
        OperationSpecies::Construction,
        vec![],
        vec![standing],
        None,
        vec![
            implementation("Gemma4TextModel.forward (hidden_states = decoder_layer()"),
            implementation(
                "Gemma4TextModel.forward (for i, decoder_layer in enumerate(self.layers[: self.config.num_hidden_layers]):)",
            ),
        ],
    )?;
    realization.bind(
        carried,
        Standing {
            name: CARRIED_STANDING.to_owned(),
        },
    );
    let normed = law(
        &mut complex,
        "final rebase",
        OperationSpecies::Transport,
        vec![standing],
        vec![standing],
        Some(FINAL_NORM.to_owned()),
        rebase_testimony(
            "Gemma4TextModel.forward (hidden_states = self.norm(hidden_states))",
            FINAL_NORM,
            HIDDEN,
        ),
    )?;
    realization.bind(
        normed,
        RmsRebase {
            group: HIDDEN,
            gain: Some(FINAL_NORM.to_owned()),
            eps,
        },
    );
    bond(&mut complex, "final rebases", standing, carried, normed, 0)?;
    let normed = seal(
        chart,
        &mut complex,
        &mut realization,
        normed,
        standing,
        "final normed",
    )?;
    returns.insert(FINAL_NORMED, normed);
    let normed = if let Intervention::WithdrawFinalSpan { from, span } = sibling {
        let w = law(
            &mut complex,
            "final normed span withdrawn (intervention)",
            OperationSpecies::Quotient,
            vec![standing],
            vec![standing],
            None,
            vec![intervention(&intervention_statement(
                "output boundary",
                &format!(
                    "columns {from}..{} of the final normed standing withdrawn before the tied boundary",
                    from + span
                ),
            ))],
        )?;
        realization.bind(
            w,
            WithdrawColumns {
                from: *from,
                span: *span,
            },
        );
        bond(&mut complex, "final span withdrawn", standing, normed, w, 0)?;
        w
    } else {
        normed
    };
    let potential = law(
        &mut complex,
        "tied output boundary",
        OperationSpecies::Transport,
        vec![standing],
        vec![vocabulary],
        Some(EMBED.to_owned()),
        vec![
            implementation(
                "Gemma4ForConditionalGeneration.forward (logits = self.lm_head(hidden_states[:, slice_indices, :]))",
            ),
            implementation(
                "Gemma4ForConditionalGeneration._tied_weights_keys (_tied_weights_keys = {\"lm_head.weight\": \"model.language_model.embed_tokens.weight\"})",
            ),
            configuration("vocab_size", "262144"),
            shape(EMBED, &[VOCABULARY, HIDDEN]),
        ],
    )?;
    realization.bind(
        potential,
        Contract {
            population: EMBED.to_owned(),
        },
    );
    bond(
        &mut complex,
        "tied boundary",
        standing,
        normed,
        potential,
        0,
    )?;
    returns.insert(POTENTIAL, potential);
    Ok(Founded {
        complex,
        realization,
        returns,
    })
}
