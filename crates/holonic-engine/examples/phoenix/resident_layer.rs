//! **The layer-zero source diagram of Gemma-4-E4B, bound as one deed** — the per-layer input
//! predecessor and the layer proper in one `PortedOperationComplex` — with every binding's testimony
//! naming the authoritative implementation by symbol AND verbatim slice, every configuration field
//! by name and exact value, every stored population by declared shape and content region, and the
//! two interventions typed as interventions.
//!
//! Contract:
//! `research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`
//! §3 (the source-authenticated bindings) and §4 (the ports and laws). Plan: the Gemma instance
//! blueprint §6, *one honest Gemma pathway is enacted before the tower is generalized*.
//!
//! This is a site, not a library owner: it binds one source instance and never becomes internal
//! anatomy. It declares no operation the front passage does not own and computes no standing.
//!
//! # One deed, not two
//!
//! The first form founded the per-layer input and the layer as two diagrams so the certificate's
//! factorial replay would stay small; the predecessor then executed before the layer was priced.
//! Independence is now derived from footprints, so there is no factorial to keep small, and the
//! whole passage is one diagram: the predecessor's six fronts lie co-present with the layer's
//! opening fronts, so the thirty-five occurrences lay as twenty-three fronts (measured by
//! `closure().fronts`), priced and admitted before the first launch.
//!
//! # Every binding names testimony that resolves
//!
//! Every law carries `SourceTestimony::Implementation { locator, symbol }` where `symbol` is
//! `Class.method (verbatim source line)`; `holonic_engine::source_occurrence` resolves the path in the
//! authenticated file and requires the slice to occur in that scope. A fabricated symbol, a drifted
//! configuration value, or a wrong declared shape refuses at compile. The matched sibling's
//! withdrawal and the collapse control carry `SourceTestimony::Intervention` and are admissible
//! only on their quotient-species bindings.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fs::File;

use holonic_engine::causal::EventId;
use holonic_engine::category::BoundaryId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use holonic_engine::foreign_map::{manifest_safetensors, ForeignContainer};
use holonic_engine::front_passage::{Chronology, CollapseControl, Contact, Contract, Enter, EnteringRows, GeluTanh, Hadamard, MaterialPlan, MountedPopulation, ReEntry, ResidentMaterial, ResidentRealization, RmsRebase, Scale, WithdrawColumns};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use holonic_engine::resident_section::{Dyadic, DyadicEnclosure, SeriesAperture};
use holonic_engine::source_occurrence::{AssetDeclaration, AuthenticatedContainer, AuthenticatedText, RegionIdentity, SourceOccurrence};
use num_bigint::BigInt;
use relational_geometry::Rat;
use sha2::{Digest, Sha256};

/// The authoritative implementation this site's testimony cites, and its content as measured on
/// 2026-08-18. If the file drifts the passage refuses to compile rather than binding to a law that
/// is no longer the one read.
pub const IMPLEMENTATION: &str = "/home/b/scratch/huggingface/.venv/lib/python3.13/site-packages/transformers/models/gemma4/modeling_gemma4.py";
pub const IMPLEMENTATION_PACKAGE_INIT: &str = "/home/b/scratch/huggingface/.venv/lib/python3.13/site-packages/transformers/__init__.py";
pub const IMPLEMENTATION_SHA256: &str = "64ecac478c7d11b9a6993ea194bdf98ce867d0e6d361295d976140e0ded53933";

pub const LAYER: usize = 0;
pub const HIDDEN: usize = 2560;
pub const HEADS: usize = 8;
pub const KV_HEADS: usize = 2;
pub const HEAD_WIDTH: usize = 256;
pub const PLE_WIDTH: usize = 256;
pub const FFN: usize = 10240;
pub const SLIDING_WINDOW: usize = 512;
/// `bf16(sqrt(2560))`: the source's `Gemma4TextScaledWordEmbedding` casts its scale to the weight
/// dtype, and its own comment says why. `0x424a` = 50.5 = 101·2^-1.
pub const EMBED_SCALE: Dyadic = Dyadic { significand: 101, exponent: -1 };
/// `sqrt(256)` = 16, exact.
pub const PLE_EMBED_SCALE: Dyadic = Dyadic { significand: 16, exponent: 0 };
/// `rms_norm_eps = 1e-06` as the `binary64` word `0x3eb0c6f7a0b5ed8d`: exact dyadic.
pub const EPS_BITS: u64 = 0x3eb0c6f7a0b5ed8d;
/// `gelu_pytorch_tanh`'s `sqrt(2/pi)` and `0.044715` as the `binary64` words the implementation
/// computes with.
pub const GELU_SCALE_BITS: u64 = 0x3fe9884533d43651;
pub const GELU_CUBIC_BITS: u64 = 0x3fa6e4e26d4801f7;
/// The sliding-attention `rope_theta` and the grain the band elements are carried at.
pub const ROPE_THETA: u64 = 10_000;
pub const BAND_GRAIN: u32 = 60;
pub const BAND_TERMS: usize = 40;

pub const BANDS: &str = "layer 0 sliding band elements";
pub const ENTERING: &str = "entering rows";
pub const PLE_ENTERING: &str = "per-layer entering rows";

/// The named returns of the deed a receiver may declare as its terminal.
pub const X0: &str = "x0";
pub const PLE: &str = "ple";
pub const INPUT_REBASE: &str = "input-rebase";
pub const RECEIVER_PROJECTION: &str = "receiver-projection";
pub const CONTACT: &str = "contact";
pub const FIRST_RE_ENTRY: &str = "first-re-entry";
pub const SECOND_RE_ENTRY: &str = "second-re-entry";
pub const LAYER_RETURN: &str = "layer";

pub fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{LAYER}.{suffix}")
}

pub fn implementation(symbol: &str) -> SourceTestimony {
    SourceTestimony::Implementation { locator: IMPLEMENTATION.to_owned(), symbol: symbol.to_owned() }
}

pub fn configuration(field: &str, value: &str) -> SourceTestimony {
    SourceTestimony::Configuration { field: field.to_owned(), value: value.to_owned() }
}

pub fn shape(population: &str, shape: &[usize]) -> SourceTestimony {
    SourceTestimony::DeclaredShape { population: population.to_owned(), shape: shape.to_vec() }
}

pub fn intervention(statement: &str) -> SourceTestimony {
    SourceTestimony::Intervention { statement: statement.to_owned() }
}

// ---------------------------------------------------------------------------------------------
// material
// ---------------------------------------------------------------------------------------------

/// The container, opened once. Paths are apparatus addresses and never identities.
pub struct Source {
    pub root: String,
    pub file: File,
    pub container: ForeignContainer,
}

impl Source {
    pub fn open(root: &str) -> Result<Self, String> {
        let (file, container) = manifest_safetensors(&format!("{root}/model.safetensors")).map_err(|error| error.to_string())?;
        Ok(Self { root: root.to_owned(), file, container })
    }

    pub fn whole(&mut self, population: &str) -> Result<(Vec<u16>, Vec<usize>), String> {
        let shape = self.container.tensor(population).map_err(|error| error.to_string())?.shape.clone();
        let words = self.container.read_bf16_whole(&mut self.file, population).map_err(|error| error.to_string())?;
        Ok((words, shape))
    }

    pub fn rows(&mut self, population: &str, from: usize, count: usize) -> Result<(Vec<u16>, usize), String> {
        self.container.read_rows_bf16(&mut self.file, population, from, count).map_err(|error| error.to_string())
    }

    /// The region identity of a declared population from the header, without a content digest.
    pub fn region(&self, population: &str, sha256: Option<String>) -> Result<RegionIdentity, String> {
        let tensor = self.container.tensor(population).map_err(|error| error.to_string())?;
        Ok(RegionIdentity {
            population: population.to_owned(),
            dtype: format!("{:?}", tensor.dtype),
            shape: tensor.shape.clone(),
            start: tensor.start,
            end: tensor.end,
            sha256,
        })
    }
}

pub fn digest_words(words: &[u16]) -> String {
    let mut hasher = Sha256::new();
    for word in words {
        hasher.update(word.to_le_bytes());
    }
    hasher.finalize().iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Every population layer zero's deed names, and nothing else. Mounted once; the mounted maps stay
/// resident across every deed the caller conducts.
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
pub const PLE_MODEL_PROJECTION: &str = "model.language_model.per_layer_model_projection.weight";
pub const PLE_PROJECTION_NORM: &str = "model.language_model.per_layer_projection_norm.weight";
pub const EMBED: &str = "model.language_model.embed_tokens.weight";
pub const PLE_EMBED: &str = "model.language_model.embed_tokens_per_layer.weight";

/// What mounting cost and identified, so the driver can show that a later deed re-uploaded nothing
/// and so the source occurrence carries every region the deed reads.
#[derive(Debug, Default)]
pub struct MountReceipt {
    pub populations: usize,
    pub stored_octets: u64,
    pub resident_octets: u64,
    pub layer_scalar: Option<Dyadic>,
    pub regions: BTreeMap<String, RegionIdentity>,
}

/// **The material plan, from the header alone**: every map the deed will mount with its rows and
/// width as the container declares them, plus the band elements and positions — so the material
/// deed can be predicted and admitted before one octet of weight is read.
pub fn material_plan(source: &Source, tokens: usize) -> Result<MaterialPlan, String> {
    let mut maps: Vec<(String, usize, usize)> = Vec::new();
    for suffix in POPULATIONS.iter().chain(GAINS.iter()) {
        let name = named(suffix);
        let shape = source.container.tensor(&name).map_err(|error| error.to_string())?.shape.clone();
        let dim = *shape.last().ok_or_else(|| format!("{name} has no shape"))?;
        let rows: usize = shape.iter().take(shape.len() - 1).product::<usize>().max(1);
        maps.push((name, rows, dim));
    }
    let projection = source.container.tensor(PLE_MODEL_PROJECTION).map_err(|error| error.to_string())?.shape.clone();
    maps.push((PLE_MODEL_PROJECTION.to_owned(), PLE_WIDTH, projection[1]));
    let norm = source.container.tensor(PLE_PROJECTION_NORM).map_err(|error| error.to_string())?.shape.clone();
    maps.push((PLE_PROJECTION_NORM.to_owned(), 1, norm[0]));
    Ok(MaterialPlan { maps, band_elements: HEAD_WIDTH / 2, positions: tokens })
}

/// Mount every stored population the deed names. Weights cross once and stay; every region read is
/// hashed as it is read.
pub fn mount<'chart>(source: &mut Source, readout: &'chart ResidentReadout, material: &mut ResidentMaterial<'chart>) -> Result<MountReceipt, String> {
    let mut receipt = MountReceipt::default();
    fn mount_one<'chart>(
        readout: &'chart ResidentReadout,
        material: &mut ResidentMaterial<'chart>,
        receipt: &mut MountReceipt,
        name: String,
        words: Vec<u16>,
        dim: usize,
    ) -> Result<(), String> {
        let mounted = readout.mount_bfloat16(&words, dim).map_err(|error| format!("{error:?}"))?;
        let masses = mounted.absolute_row_mass().map_err(|error| format!("{error:?}"))?;
        let widest = masses.iter().map(|m| m.unsigned_abs()).max().unwrap_or(0);
        let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
        receipt.populations += 1;
        receipt.stored_octets += (words.len() * 2) as u64;
        receipt.resident_octets += mounted.resident_octets() as u64;
        material.populations.insert(name, MountedPopulation { readout: mounted, mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0) });
        Ok(())
    }
    for suffix in POPULATIONS.iter().chain(GAINS.iter()) {
        let name = named(suffix);
        if material.populations.contains_key(&name) {
            continue;
        }
        let (words, shape) = source.whole(&name)?;
        let dim = *shape.last().ok_or_else(|| format!("{name} has no shape"))?;
        receipt.regions.insert(name.clone(), source.region(&name, Some(digest_words(&words)))?);
        mount_one(readout, material, &mut receipt, name, words, dim)?;
    }
    // The layer's slice of the per-layer model projection: rows [256·layer, 256·layer + 256). The
    // whole tensor is identified from the header; the slice read is hashed under its own name.
    let (words, dim) = source.rows(PLE_MODEL_PROJECTION, PLE_WIDTH * LAYER, PLE_WIDTH)?;
    receipt.regions.insert(PLE_MODEL_PROJECTION.to_owned(), source.region(PLE_MODEL_PROJECTION, None)?);
    let mut slice = source.region(PLE_MODEL_PROJECTION, Some(digest_words(&words)))?;
    slice.population = format!("{PLE_MODEL_PROJECTION} rows {}..{}", PLE_WIDTH * LAYER, PLE_WIDTH * (LAYER + 1));
    slice.shape = vec![PLE_WIDTH, dim];
    slice.start += (PLE_WIDTH * LAYER * dim * 2) as u64;
    slice.end = slice.start + (PLE_WIDTH * dim * 2) as u64;
    receipt.regions.insert(slice.population.clone(), slice);
    mount_one(readout, material, &mut receipt, PLE_MODEL_PROJECTION.to_owned(), words, dim)?;
    let (words, shape) = source.whole(PLE_PROJECTION_NORM)?;
    receipt.regions.insert(PLE_PROJECTION_NORM.to_owned(), source.region(PLE_PROJECTION_NORM, Some(digest_words(&words)))?);
    mount_one(readout, material, &mut receipt, PLE_PROJECTION_NORM.to_owned(), words, shape[0])?;
    // The layer scalar: one stored word, read as an exact dyadic.
    let (scalar, _) = source.whole(&named("layer_scalar"))?;
    receipt.regions.insert(named("layer_scalar"), source.region(&named("layer_scalar"), Some(digest_words(&scalar)))?);
    let word = *scalar.first().ok_or("layer_scalar is empty")?;
    receipt.layer_scalar = Some(Dyadic::of_bfloat16_bits(word).map_err(|error| error.to_string())?);
    // The two entering tables: identified from the header; their content is covered by the
    // whole-container digest, and the rows read at runtime are the material, not the map.
    receipt.regions.insert(EMBED.to_owned(), source.region(EMBED, None)?);
    receipt.regions.insert(PLE_EMBED.to_owned(), source.region(PLE_EMBED, None)?);
    Ok(receipt)
}

/// **The runtime-supplied material**: token identities read as rows of the two embedding tables.
/// Nothing about the tokens is compiled into any diagram.
pub fn enter(source: &mut Source, tokens: &[usize], material: &mut ResidentMaterial<'_>) -> Result<(), String> {
    let mut entering = Vec::with_capacity(tokens.len() * HIDDEN);
    let mut per_layer = Vec::with_capacity(tokens.len() * PLE_WIDTH);
    for token in tokens {
        let (row, width) = source.rows(EMBED, *token, 1)?;
        if width != HIDDEN {
            return Err(format!("{EMBED} is {width} wide"));
        }
        entering.extend(row);
        let (row, width) = source.rows(PLE_EMBED, *token, 1)?;
        let from = LAYER * PLE_WIDTH;
        if width < from + PLE_WIDTH {
            return Err(format!("{PLE_EMBED} is {width} wide"));
        }
        per_layer.extend_from_slice(&row[from..from + PLE_WIDTH]);
    }
    material.entering.insert(ENTERING.to_owned(), EnteringRows { words: entering, rows: tokens.len(), width: HIDDEN });
    material.entering.insert(PLE_ENTERING.to_owned(), EnteringRows { words: per_layer, rows: tokens.len(), width: PLE_WIDTH });
    Ok(())
}

/// The band group elements of the sliding chronology: `(cos θ_b, sin θ_b)` for
/// `θ_b = 10000^{-2b/256}`, `b = 0..128`, each a certified enclosure over the whole angle interval,
/// carried at `2^-60`. Founded once on the serial chart; the position is spent on the card.
pub fn found_bands(terms: usize) -> Result<Vec<((i64, i64), (i64, i64))>, String> {
    let bands = HEAD_WIDTH / 2;
    let ratio = AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(ROPE_THETA)), bands as u32, 64)
        .map_err(|error| format!("{error:?}"))?
        .enclosure()
        .reciprocal()
        .map_err(|error| format!("{error:?}"))?;
    let mut angle = ExactInterval::point(Rat::from_integer(BigInt::from(1)));
    let mut elements = Vec::with_capacity(bands);
    for _ in 0..bands {
        let (cos_low, sin_low) = CertifiedSeries::circular_series(&angle.lower, terms).map_err(|e| format!("{e:?}"))?;
        let (cos_high, sin_high) = CertifiedSeries::circular_series(&angle.upper, terms).map_err(|e| format!("{e:?}"))?;
        let cos = ExactInterval::new(
            cos_high.enclosure().lower.clone().min(cos_low.enclosure().lower.clone()),
            cos_low.enclosure().upper.clone().max(cos_high.enclosure().upper.clone()),
        )
        .map_err(|e| format!("{e:?}"))?;
        let sin = ExactInterval::new(
            sin_low.enclosure().lower.clone().min(sin_high.enclosure().lower.clone()),
            sin_high.enclosure().upper.clone().max(sin_low.enclosure().upper.clone()),
        )
        .map_err(|e| format!("{e:?}"))?;
        let cos = DyadicEnclosure::of_interval(&cos, BAND_GRAIN).map_err(|e| e.to_string())?;
        let sin = DyadicEnclosure::of_interval(&sin, BAND_GRAIN).map_err(|e| e.to_string())?;
        elements.push(((cos.lo, cos.hi), (sin.lo, sin.hi)));
        angle = angle.times(&ratio).map_err(|e| format!("{e:?}"))?.round_out(64).map_err(|e| format!("{e:?}"))?;
    }
    Ok(elements)
}

/// `2560^{-1/2}` and `2^{-1/2}` as certified enclosures at the band grain — the source's two
/// irrational scales, never floats.
pub fn algebraic_scales() -> Result<(DyadicEnclosure, DyadicEnclosure), String> {
    let projection = AlgebraicRoot::reciprocal_square_root(&Rat::from_integer(BigInt::from(HIDDEN as u64)), 64).map_err(|e| format!("{e:?}"))?;
    let half = AlgebraicRoot::reciprocal_square_root(&Rat::from_integer(BigInt::from(2)), 64).map_err(|e| format!("{e:?}"))?;
    Ok((
        DyadicEnclosure::of_interval(projection.enclosure(), BAND_GRAIN).map_err(|e| e.to_string())?,
        DyadicEnclosure::of_interval(half.enclosure(), BAND_GRAIN).map_err(|e| e.to_string())?,
    ))
}

// ---------------------------------------------------------------------------------------------
// the source occurrence
// ---------------------------------------------------------------------------------------------

/// The exterior version string of the implementation package, read from its own `__init__.py`.
pub fn implementation_version() -> Option<String> {
    let text = std::fs::read_to_string(IMPLEMENTATION_PACKAGE_INIT).ok()?;
    text.lines().find_map(|line| line.strip_prefix("__version__ = ").map(|v| format!("transformers {}", v.trim().trim_matches('"'))))
}

/// **Build the source occurrence** the deed's testimony is validated against: the implementation
/// text (refusing if its content is not the content the bindings were read against), the
/// configuration, the container's header and whole-content digests, every region the mount
/// identified, and the sibling assets declared unused by this aperture.
pub fn source_occurrence(root: &str, regions: BTreeMap<String, RegionIdentity>, content_sha256: Option<String>) -> Result<SourceOccurrence, String> {
    let implementation = AuthenticatedText::read(IMPLEMENTATION, implementation_version().as_deref()).map_err(|e| e.to_string())?;
    if implementation.sha256 != IMPLEMENTATION_SHA256 {
        return Err(format!("the implementation at {IMPLEMENTATION} hashes to {} and this site's bindings were read against {IMPLEMENTATION_SHA256}", implementation.sha256));
    }
    let configuration = AuthenticatedText::read(&format!("{root}/config.json"), None).map_err(|e| e.to_string())?;
    let locator = format!("{root}/model.safetensors");
    let (octets, header_octets, header_sha256) = AuthenticatedContainer::read_header(&locator).map_err(|e| e.to_string())?;
    let mut assets = Vec::new();
    for (role, file) in [
        ("tokenizer", "tokenizer.json"),
        ("tokenizer configuration", "tokenizer_config.json"),
        ("processor configuration", "processor_config.json"),
        ("chat template", "chat_template.jinja"),
        ("generation configuration", "generation_config.json"),
    ] {
        let path = format!("{root}/{file}");
        let sha256 = std::fs::read(&path).ok().map(|bytes| Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect::<String>());
        // This aperture takes token identities at runtime and emits no text: none of these is used.
        assets.push(AssetDeclaration { role: role.to_owned(), locator: path, sha256, used: false });
    }
    Ok(SourceOccurrence {
        implementation,
        configuration,
        configuration_scope: vec!["text_config".to_owned()],
        container: AuthenticatedContainer { identity: holonic_engine::foreign_map::FileIdentity::at(&locator).ok(), locator, octets, header_octets, header_sha256, content_sha256, regions },
        assets,
    })
}

// ---------------------------------------------------------------------------------------------
// the deed diagram
// ---------------------------------------------------------------------------------------------

/// A founded diagram with its realization and the occurrences a caller reads.
pub struct Founded {
    pub complex: PortedOperationComplex,
    pub realization: ResidentRealization,
    /// The named returns a caller may declare as terminal.
    pub returns: BTreeMap<&'static str, EventId>,
}

pub fn law(complex: &mut PortedOperationComplex, name: &str, species: OperationSpecies, inputs: Vec<BoundaryId>, outputs: Vec<BoundaryId>, carrier: Option<String>, testimony: Vec<SourceTestimony>) -> Result<EventId, String> {
    let law = complex.bind_operation(name, species, inputs, outputs, carrier, testimony).map_err(|e| e.to_string())?;
    complex.occur(law).map_err(|e| e.to_string())
}

pub fn bond(complex: &mut PortedOperationComplex, name: &str, port: BoundaryId, from: EventId, to: EventId, input: usize) -> Result<(), String> {
    complex.carries_precedence(name, port, OccurrencePort::output(from, 0), OccurrencePort::input(to, input)).map_err(|e| e.to_string())
}

/// Which K/V family, if any, a matched-sibling run withdraws after the head norms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sibling {
    Base,
    WithdrawFamily(usize),
    /// **A control, unsound by construction**: the input rebase's enclosure collapsed to midpoints
    /// before the projections, so the terminal face shows the remainder was load-bearing.
    CollapseAfterInputRebase,
}

/// The RMS rebase's testimony: the source law, its epsilon, and the gain's declared shape.
pub fn rebase_testimony(site: &str, population: &str, group: usize) -> Vec<SourceTestimony> {
    vec![
        implementation(site),
        implementation("Gemma4RMSNorm._norm (mean_squared = hidden_states.pow(2).mean(-1, keepdim=True) + self.eps)"),
        implementation("Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))"),
        implementation("Gemma4RMSNorm.forward (normed_output = normed_output * self.weight.float())"),
        configuration("rms_norm_eps", "1e-06"),
        shape(population, &[group]),
    ]
}

/// **The deed**: the per-layer input predecessor and layer zero, one diagram.
pub fn found_deed(scales: &(DyadicEnclosure, DyadicEnclosure), terms: SeriesAperture, layer_scalar: Dyadic, sibling: Sibling) -> Result<Founded, String> {
    let eps = Dyadic::of_binary64_bits(EPS_BITS).map_err(|e| e.to_string())?;
    let c1 = Dyadic::of_binary64_bits(GELU_SCALE_BITS).map_err(|e| e.to_string())?;
    let c2 = Dyadic::of_binary64_bits(GELU_CUBIC_BITS).map_err(|e| e.to_string())?;
    let mut complex = PortedOperationComplex::new("Gemma-4-E4B layer 0 with its per-layer input, sliding attention");
    let standing = complex.port("continuing standing, 2560");
    let ple = complex.port("per-layer section, 256");
    let receivers = complex.port("receiver chart, 8 heads x 256");
    let families = complex.port("presented/carried chart, 2 families x 256");
    let passage = complex.port("gated passage chart, 10240");
    let mut realization = ResidentRealization::default();
    let mut returns = BTreeMap::new();

    // --- the per-layer input predecessor ---
    let x0 = law(&mut complex, "entering standing", OperationSpecies::Construction, vec![], vec![standing], Some(EMBED.to_owned()), vec![
        implementation("Gemma4TextScaledWordEmbedding.forward (return super().forward(input_ids) * self.embed_scale.to(self.weight.dtype))"),
        implementation("Gemma4TextModel.__init__ (embed_scale=self.config.hidden_size**0.5)"),
        configuration("hidden_size", "2560"),
        shape(EMBED, &[262_144, HIDDEN]),
    ])?;
    realization.bind(x0, Enter { population: ENTERING.to_owned(), scale: EMBED_SCALE });
    returns.insert(X0, x0);

    let projected = law(&mut complex, "per-layer model projection", OperationSpecies::Transport, vec![standing], vec![ple], Some(PLE_MODEL_PROJECTION.to_owned()), vec![
        implementation("Gemma4TextModel.project_per_layer_inputs (per_layer_projection = self.per_layer_model_projection(inputs_embeds) * self.per_layer_model_projection_scale)"),
        configuration("hidden_size_per_layer_input", "256"),
        configuration("num_hidden_layers", "42"),
        shape(PLE_MODEL_PROJECTION, &[42 * PLE_WIDTH, HIDDEN]),
    ])?;
    realization.bind(projected, Contract { population: PLE_MODEL_PROJECTION.to_owned() });
    bond(&mut complex, "x0 projects", standing, x0, projected, 0)?;

    let scaled = law(&mut complex, "per-layer projection scale 2560^-1/2", OperationSpecies::Transport, vec![ple], vec![ple], None, vec![
        implementation("Gemma4TextModel.__init__ (self.per_layer_model_projection_scale = config.hidden_size**-0.5)"),
        configuration("hidden_size", "2560"),
    ])?;
    realization.bind(scaled, Scale { by: scales.0 });
    bond(&mut complex, "projection scales", ple, projected, scaled, 0)?;

    let normed = law(&mut complex, "per-layer projection norm", OperationSpecies::Transport, vec![ple], vec![ple], Some(PLE_PROJECTION_NORM.to_owned()),
        rebase_testimony("Gemma4TextModel.project_per_layer_inputs (per_layer_projection = self.per_layer_projection_norm(per_layer_projection))", PLE_PROJECTION_NORM, PLE_WIDTH))?;
    realization.bind(normed, RmsRebase { group: PLE_WIDTH, gain: Some(PLE_PROJECTION_NORM.to_owned()), eps });
    bond(&mut complex, "projection norms", ple, scaled, normed, 0)?;

    let token = law(&mut complex, "per-layer token identity", OperationSpecies::Construction, vec![], vec![ple], Some(PLE_EMBED.to_owned()), vec![
        implementation("Gemma4TextModel.get_per_layer_inputs (return self.embed_tokens_per_layer(input_ids).reshape()"),
        implementation("Gemma4TextModel.__init__ (embed_scale=config.hidden_size_per_layer_input**0.5,)"),
        configuration("hidden_size_per_layer_input", "256"),
        shape(PLE_EMBED, &[262_144, 42 * PLE_WIDTH]),
    ])?;
    realization.bind(token, Enter { population: PLE_ENTERING.to_owned(), scale: PLE_EMBED_SCALE });

    let joined = law(&mut complex, "per-layer join", OperationSpecies::Construction, vec![ple, ple], vec![ple], None, vec![
        implementation("Gemma4TextModel.project_per_layer_inputs (return (per_layer_projection + per_layer_inputs) * self.per_layer_input_scale)"),
    ])?;
    realization.bind(joined, ReEntry);
    bond(&mut complex, "join projection", ple, normed, joined, 0)?;
    bond(&mut complex, "join token", ple, token, joined, 1)?;

    let halved = law(&mut complex, "per-layer input scale 2^-1/2", OperationSpecies::Transport, vec![ple], vec![ple], None, vec![
        implementation("Gemma4TextModel.__init__ (self.per_layer_input_scale = 2.0**-0.5)"),
    ])?;
    realization.bind(halved, Scale { by: scales.1 });
    bond(&mut complex, "join scales", ple, joined, halved, 0)?;
    returns.insert(PLE, halved);

    // --- the layer ---
    let decoder = "Gemma4TextDecoderLayer.forward";
    let rebased = law(&mut complex, "input rebase", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("input_layernorm.weight")),
        rebase_testimony("Gemma4TextDecoderLayer.forward (hidden_states = self.input_layernorm(hidden_states))", &named("input_layernorm.weight"), HIDDEN))?;
    realization.bind(rebased, RmsRebase { group: HIDDEN, gain: Some(named("input_layernorm.weight")), eps });
    bond(&mut complex, "x0 rebases", standing, x0, rebased, 0)?;
    returns.insert(INPUT_REBASE, rebased);
    let h = if sibling == Sibling::CollapseAfterInputRebase {
        let collapsed = law(&mut complex, "input rebase collapsed (control)", OperationSpecies::Quotient, vec![standing], vec![standing], None,
            vec![intervention("control: the remainder removed at this site; the enclosure collapsed to its midpoint; not a source law")])?;
        realization.bind(collapsed, CollapseControl);
        bond(&mut complex, "collapse", standing, rebased, collapsed, 0)?;
        collapsed
    } else {
        rebased
    };

    let mut projections = Vec::new();
    for (what, suffix, port, out, slice) in [
        ("receiver projection", "self_attn.q_proj.weight", receivers, HEADS * HEAD_WIDTH, "Gemma4TextAttention.forward (query_states = self.q_proj(hidden_states).view(hidden_shape))"),
        ("presented projection", "self_attn.k_proj.weight", families, KV_HEADS * HEAD_WIDTH, "Gemma4TextAttention.forward (key_states = self.k_proj(hidden_states).view(hidden_shape))"),
        ("carried projection", "self_attn.v_proj.weight", families, KV_HEADS * HEAD_WIDTH, "Gemma4TextAttention.forward (value_states = self.v_proj(hidden_states).view(hidden_shape) if self.v_proj is not None else key_states)"),
    ] {
        let event = law(&mut complex, what, OperationSpecies::Transport, vec![standing], vec![port], Some(named(suffix)), vec![
            implementation(slice),
            implementation("Gemma4TextAttention.__init__ (self.head_dim = config.global_head_dim if not self.is_sliding and config.global_head_dim else config.head_dim)"),
            configuration("num_attention_heads", "8"),
            configuration("num_key_value_heads", "2"),
            configuration("head_dim", "256"),
            shape(&named(suffix), &[out, HIDDEN]),
        ])?;
        realization.bind(event, Contract { population: named(suffix) });
        bond(&mut complex, what, standing, h, event, 0)?;
        projections.push(event);
    }
    returns.insert(RECEIVER_PROJECTION, projections[0]);
    let qn = law(&mut complex, "receiver head rebase", OperationSpecies::Transport, vec![receivers], vec![receivers], Some(named("self_attn.q_norm.weight")), {
        let mut t = rebase_testimony("Gemma4TextAttention.forward (query_states = self.q_norm(query_states))", &named("self_attn.q_norm.weight"), HEAD_WIDTH);
        t.push(implementation("Gemma4TextAttention.__init__ (self.q_norm = Gemma4RMSNorm(dim=self.head_dim, eps=config.rms_norm_eps))"));
        t
    })?;
    realization.bind(qn, RmsRebase { group: HEAD_WIDTH, gain: Some(named("self_attn.q_norm.weight")), eps });
    bond(&mut complex, "q rebases", receivers, projections[0], qn, 0)?;
    let kn = law(&mut complex, "presented head rebase", OperationSpecies::Transport, vec![families], vec![families], Some(named("self_attn.k_norm.weight")), {
        let mut t = rebase_testimony("Gemma4TextAttention.forward (key_states = self.k_norm(key_states))", &named("self_attn.k_norm.weight"), HEAD_WIDTH);
        t.push(implementation("Gemma4TextAttention.__init__ (self.k_norm = Gemma4RMSNorm(dim=self.head_dim, eps=config.rms_norm_eps))"));
        t
    })?;
    realization.bind(kn, RmsRebase { group: HEAD_WIDTH, gain: Some(named("self_attn.k_norm.weight")), eps });
    bond(&mut complex, "k rebases", families, projections[1], kn, 0)?;
    let vn = law(&mut complex, "carried head rebase, no gain", OperationSpecies::Transport, vec![families], vec![families], None, vec![
        implementation("Gemma4TextAttention.forward (value_states = self.v_norm(value_states))"),
        implementation("Gemma4TextAttention.__init__ (self.v_norm = Gemma4RMSNorm(self.head_dim, eps=config.rms_norm_eps, with_scale=False))"),
        implementation("Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))"),
        configuration("rms_norm_eps", "1e-06"),
        configuration("head_dim", "256"),
    ])?;
    realization.bind(vn, RmsRebase { group: HEAD_WIDTH, gain: None, eps });
    bond(&mut complex, "v rebases", families, projections[2], vn, 0)?;

    // The matched sibling: withdraw one K/V family after the head rebases, before the chronology.
    let (k_source, v_source) = match sibling {
        Sibling::Base | Sibling::CollapseAfterInputRebase => (kn, vn),
        Sibling::WithdrawFamily(family) => {
            let ka = law(&mut complex, "presented family withdrawn", OperationSpecies::Quotient, vec![families], vec![families], None,
                vec![intervention(&format!("matched sibling: presented family {family} withdrawn after its head rebase; not a source law"))])?;
            realization.bind(ka, WithdrawColumns { from: family * HEAD_WIDTH, span: HEAD_WIDTH });
            bond(&mut complex, "k withdrawn", families, kn, ka, 0)?;
            let va = law(&mut complex, "carried family withdrawn", OperationSpecies::Quotient, vec![families], vec![families], None,
                vec![intervention(&format!("matched sibling: carried family {family} withdrawn after its head rebase; not a source law"))])?;
            realization.bind(va, WithdrawColumns { from: family * HEAD_WIDTH, span: HEAD_WIDTH });
            bond(&mut complex, "v withdrawn", families, vn, va, 0)?;
            (ka, va)
        }
    };

    let chronology_testimony = |site: &str| {
        vec![
            implementation(site),
            implementation("apply_rotary_pos_emb (return (x * cos) + (rotate_half(x) * sin))"),
            implementation("rotate_half (return torch.cat((-x2, x1), dim=-1))"),
            implementation("Gemma4TextRotaryEmbedding.compute_default_rope_parameters (base ** (torch.arange(0, dim, 2, dtype=torch.int64))"),
            implementation("Gemma4TextRotaryEmbedding.forward (emb = torch.cat((freqs, freqs), dim=-1))"),
            configuration("rope_parameters.sliding_attention.rope_type", "default"),
            configuration("rope_parameters.sliding_attention.rope_theta", "10000.0"),
            configuration("layer_types[0]", "sliding_attention"),
            configuration("num_attention_heads", "8"),
            configuration("num_key_value_heads", "2"),
            configuration("head_dim", "256"),
        ]
    };
    let qr = law(&mut complex, "receiver chronology", OperationSpecies::Transport, vec![receivers], vec![receivers], None,
        chronology_testimony("Gemma4TextAttention.forward (query_states = apply_rotary_pos_emb(query_states, cos, sin, unsqueeze_dim=2))"))?;
    realization.bind(qr, Chronology { bands: BANDS.to_owned(), heads: HEADS, head_width: HEAD_WIDTH });
    bond(&mut complex, "q turns", receivers, qn, qr, 0)?;
    let kr = law(&mut complex, "presented chronology", OperationSpecies::Transport, vec![families], vec![families], None,
        chronology_testimony("Gemma4TextAttention.forward (key_states = apply_rotary_pos_emb(key_states, cos, sin, unsqueeze_dim=2))"))?;
    realization.bind(kr, Chronology { bands: BANDS.to_owned(), heads: KV_HEADS, head_width: HEAD_WIDTH });
    bond(&mut complex, "k turns", families, k_source, kr, 0)?;

    let contact = law(&mut complex, "contact and carried construction", OperationSpecies::Construction, vec![receivers, families, families], vec![receivers], None, vec![
        implementation("eager_attention_forward (attn_weights = torch.matmul(query, key_states.transpose(2, 3)) * scaling)"),
        implementation("eager_attention_forward (attn_weights = nn.functional.softmax(attn_weights, dim=-1, dtype=torch.float32).to(query.dtype))"),
        implementation("eager_attention_forward (attn_output = torch.matmul(attn_weights, value_states))"),
        implementation("Gemma4TextAttention.__init__ (self.scaling = 1.0)"),
        implementation("Gemma4TextAttention.__init__ (self.sliding_window = config.sliding_window if self.is_sliding else None)"),
        implementation("Gemma4TextAttention.__init__ (self.num_key_value_groups = config.num_attention_heads // num_key_value_heads)"),
        implementation("repeat_kv (hidden_states = hidden_states[:, :, None, :, :].expand(batch, num_key_value_heads, n_rep, slen, head_dim))"),
        configuration("sliding_window", "512"),
        configuration("num_attention_heads", "8"),
        configuration("num_key_value_heads", "2"),
        configuration("head_dim", "256"),
    ])?;
    realization.bind(contact, Contact { heads: HEADS, kv_heads: KV_HEADS, head_width: HEAD_WIDTH, window: SLIDING_WINDOW, terms });
    bond(&mut complex, "contact receiver", receivers, qr, contact, 0)?;
    bond(&mut complex, "contact presented", families, kr, contact, 1)?;
    bond(&mut complex, "contact carried", families, v_source, contact, 2)?;
    returns.insert(CONTACT, contact);

    let o = law(&mut complex, "contact returns", OperationSpecies::Transport, vec![receivers], vec![standing], Some(named("self_attn.o_proj.weight")), vec![
        implementation("Gemma4TextAttention.forward (attn_output = self.o_proj(attn_output))"),
        shape(&named("self_attn.o_proj.weight"), &[HIDDEN, HEADS * HEAD_WIDTH]),
    ])?;
    realization.bind(o, Contract { population: named("self_attn.o_proj.weight") });
    bond(&mut complex, "contact projects back", receivers, contact, o, 0)?;
    let on = law(&mut complex, "post-attention rebase", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("post_attention_layernorm.weight")),
        rebase_testimony("Gemma4TextDecoderLayer.forward (hidden_states = self.post_attention_layernorm(hidden_states))", &named("post_attention_layernorm.weight"), HIDDEN))?;
    realization.bind(on, RmsRebase { group: HIDDEN, gain: Some(named("post_attention_layernorm.weight")), eps });
    bond(&mut complex, "return rebases", standing, o, on, 0)?;
    let r1 = law(&mut complex, "first re-entry", OperationSpecies::Construction, vec![standing, standing], vec![standing], None,
        vec![implementation(&format!("{decoder} (hidden_states = residual + hidden_states)"))])?;
    realization.bind(r1, ReEntry);
    bond(&mut complex, "re-entry retains x0", standing, x0, r1, 0)?;
    bond(&mut complex, "re-entry returns", standing, on, r1, 1)?;
    returns.insert(FIRST_RE_ENTRY, r1);

    let h2 = law(&mut complex, "pre-feedforward rebase", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("pre_feedforward_layernorm.weight")),
        rebase_testimony("Gemma4TextDecoderLayer.forward (hidden_states = self.pre_feedforward_layernorm(hidden_states))", &named("pre_feedforward_layernorm.weight"), HIDDEN))?;
    realization.bind(h2, RmsRebase { group: HIDDEN, gain: Some(named("pre_feedforward_layernorm.weight")), eps });
    bond(&mut complex, "r1 rebases", standing, r1, h2, 0)?;
    let mut branches = Vec::new();
    for (what, suffix) in [("gate", "mlp.gate_proj.weight"), ("up", "mlp.up_proj.weight")] {
        let event = law(&mut complex, what, OperationSpecies::Transport, vec![standing], vec![passage], Some(named(suffix)), vec![
            implementation("Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))"),
            configuration("intermediate_size", "10240"),
            shape(&named(suffix), &[FFN, HIDDEN]),
        ])?;
        realization.bind(event, Contract { population: named(suffix) });
        bond(&mut complex, what, standing, h2, event, 0)?;
        branches.push(event);
    }
    let gated = law(&mut complex, "gate turns", OperationSpecies::Transport, vec![passage], vec![passage], None, vec![
        implementation("Gemma4TextMLP.__init__ (self.act_fn = ACT2FN[config.hidden_activation])"),
        implementation("Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))"),
        configuration("hidden_activation", "gelu_pytorch_tanh"),
    ])?;
    realization.bind(gated, GeluTanh { c1, c2, terms });
    bond(&mut complex, "gate turns", passage, branches[0], gated, 0)?;
    let admitted = law(&mut complex, "gate admits", OperationSpecies::Construction, vec![passage, passage], vec![passage], None, vec![
        implementation("Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))"),
    ])?;
    realization.bind(admitted, Hadamard);
    bond(&mut complex, "admits gate", passage, gated, admitted, 0)?;
    bond(&mut complex, "admits up", passage, branches[1], admitted, 1)?;
    let down = law(&mut complex, "passage returns", OperationSpecies::Transport, vec![passage], vec![standing], Some(named("mlp.down_proj.weight")), vec![
        implementation("Gemma4TextMLP.forward (down_proj = self.down_proj(self.act_fn(self.gate_proj(x)) * self.up_proj(x)))"),
        shape(&named("mlp.down_proj.weight"), &[HIDDEN, FFN]),
    ])?;
    realization.bind(down, Contract { population: named("mlp.down_proj.weight") });
    bond(&mut complex, "passage returns", passage, admitted, down, 0)?;
    let dn = law(&mut complex, "post-feedforward rebase", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("post_feedforward_layernorm.weight")),
        rebase_testimony("Gemma4TextDecoderLayer.forward (hidden_states = self.post_feedforward_layernorm(hidden_states))", &named("post_feedforward_layernorm.weight"), HIDDEN))?;
    realization.bind(dn, RmsRebase { group: HIDDEN, gain: Some(named("post_feedforward_layernorm.weight")), eps });
    bond(&mut complex, "down rebases", standing, down, dn, 0)?;
    let r2 = law(&mut complex, "second re-entry", OperationSpecies::Construction, vec![standing, standing], vec![standing], None,
        vec![implementation(&format!("{decoder} (hidden_states = residual + hidden_states)"))])?;
    realization.bind(r2, ReEntry);
    bond(&mut complex, "second re-entry retains", standing, r1, r2, 0)?;
    bond(&mut complex, "second re-entry returns", standing, dn, r2, 1)?;
    returns.insert(SECOND_RE_ENTRY, r2);

    // The PLE branch, in the source's own order.
    let pg = law(&mut complex, "per-layer input gate", OperationSpecies::Transport, vec![standing], vec![ple], Some(named("per_layer_input_gate.weight")), vec![
        implementation(&format!("{decoder} (hidden_states = self.per_layer_input_gate(hidden_states))")),
        shape(&named("per_layer_input_gate.weight"), &[PLE_WIDTH, HIDDEN]),
    ])?;
    realization.bind(pg, Contract { population: named("per_layer_input_gate.weight") });
    bond(&mut complex, "r2 gates", standing, r2, pg, 0)?;
    let pga = law(&mut complex, "per-layer gate turns", OperationSpecies::Transport, vec![ple], vec![ple], None, vec![
        implementation(&format!("{decoder} (hidden_states = self.act_fn(hidden_states))")),
        implementation("Gemma4TextDecoderLayer.__init__ (self.act_fn = ACT2FN[config.hidden_activation])"),
        configuration("hidden_activation", "gelu_pytorch_tanh"),
    ])?;
    realization.bind(pga, GeluTanh { c1, c2, terms });
    bond(&mut complex, "per-layer gate turns", ple, pg, pga, 0)?;
    let pm = law(&mut complex, "per-layer gate admits the input", OperationSpecies::Construction, vec![ple, ple], vec![ple], None,
        vec![implementation(&format!("{decoder} (hidden_states = hidden_states * per_layer_input)"))])?;
    realization.bind(pm, Hadamard);
    bond(&mut complex, "admits gate", ple, pga, pm, 0)?;
    bond(&mut complex, "admits per-layer input", ple, halved, pm, 1)?;
    let pp = law(&mut complex, "per-layer projection", OperationSpecies::Transport, vec![ple], vec![standing], Some(named("per_layer_projection.weight")), vec![
        implementation(&format!("{decoder} (hidden_states = self.per_layer_projection(hidden_states))")),
        shape(&named("per_layer_projection.weight"), &[HIDDEN, PLE_WIDTH]),
    ])?;
    realization.bind(pp, Contract { population: named("per_layer_projection.weight") });
    bond(&mut complex, "per-layer projects", ple, pm, pp, 0)?;
    let ppn = law(&mut complex, "post per-layer input rebase", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("post_per_layer_input_norm.weight")),
        rebase_testimony("Gemma4TextDecoderLayer.forward (hidden_states = self.post_per_layer_input_norm(hidden_states))", &named("post_per_layer_input_norm.weight"), HIDDEN))?;
    realization.bind(ppn, RmsRebase { group: HIDDEN, gain: Some(named("post_per_layer_input_norm.weight")), eps });
    bond(&mut complex, "per-layer rebases", standing, pp, ppn, 0)?;
    let r3 = law(&mut complex, "third re-entry", OperationSpecies::Construction, vec![standing, standing], vec![standing], None,
        vec![implementation(&format!("{decoder} (hidden_states = residual + hidden_states)"))])?;
    realization.bind(r3, ReEntry);
    bond(&mut complex, "third re-entry retains", standing, r2, r3, 0)?;
    bond(&mut complex, "third re-entry returns", standing, ppn, r3, 1)?;
    let out = law(&mut complex, "layer scalar", OperationSpecies::Transport, vec![standing], vec![standing], Some(named("layer_scalar")), vec![
        implementation(&format!("{decoder} (hidden_states *= self.layer_scalar)")),
        shape(&named("layer_scalar"), &[1]),
    ])?;
    realization.bind(out, Scale { by: point_enclosure(layer_scalar) });
    bond(&mut complex, "layer scales", standing, r3, out, 0)?;
    returns.insert(LAYER_RETURN, out);

    Ok(Founded { complex, realization, returns })
}

/// An exact dyadic as a point enclosure at its own grain.
pub fn point_enclosure(dyadic: Dyadic) -> DyadicEnclosure {
    if dyadic.exponent >= 0 {
        let value = dyadic.significand << dyadic.exponent;
        DyadicEnclosure { lo: value, hi: value, grain: 0 }
    } else {
        DyadicEnclosure { lo: dyadic.significand, hi: dyadic.significand, grain: (-dyadic.exponent) as u32 }
    }
}
