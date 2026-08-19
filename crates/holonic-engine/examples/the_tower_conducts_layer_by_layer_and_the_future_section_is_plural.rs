//! **Station C of the complete Phoenix sequence: the complete contextual Gemma text pathway,
//! enacted layer by layer on the card, returning a plural future section and a decoded surface.**
//!
//! Plan: the Gemma instance blueprint §6 (*one honest Gemma pathway*, then *the generalization to
//! all 42 layers*) and the Phoenix master's active-stimulation station. What this driver enacts,
//! for several runtime-supplied inputs:
//!
//! ```text
//!   exterior token decomposition (the source tokenizer, an apparatus codec declared USED)
//!   → initial embedding → per-layer input (PLE) → layers 0–41, each ONE graph launched once:
//!       input rebase · Q/K/V (or the shared K/V standings of layers 22/23 for 24–41) · head
//!       rebases · chronology (default θ=1e4 on 256, proportional θ=1e6 on 64 of 256 pairs of 512)
//!       · contact (sliding 512 or full) · value/output transport · post-attention rebase ·
//!       residual · pre-feedforward rebase · gate/up · GELU · Hadamard · down · post-feedforward
//!       rebase · residual · per-layer gate · GELU · Hadamard with PLE · per-layer projection ·
//!       post-PLE rebase · residual · layer scalar
//!   → final rebase → tied output boundary: the illicial potential section over 262,144
//!   → the plural future section (the tokens not separated from the top by the enclosure)
//!   → the actual decoded surface (the native decode of tokenizer.json's vocabulary)
//! ```
//!
//! The method is streamable by layer: each layer's stored populations are predicted, admitted,
//! mounted, used by one graph and released before the next layer mounts, so the whole source is
//! never resident; the residual stream and the shared K/V standings cross between layer graphs on
//! the card (`section_carry`), never through the apparatus boundary. Every layer owes typed
//! admission, complete footprints, an empty obstruction lineage, an a-priori octave bound that
//! held, and its exact work; the tower's semantic work is the serial composition of the layers'.
//!
//! Exterior realization testimony: the source runtime's own bf16 face (the residual stream after
//! every layer and the logits at the last position) is compared per layer as a cross-chart defect
//! slot and never governs the native result. `final_logit_softcapping = 30` is monotone, so the
//! order faces of the potential section — which is what the plural future section is — are
//! invariant under it; it is reported, not enacted, and the comparison with the source's (softcapped)
//! logits is an order-face comparison.
//!
//! What is not claimed: no Phoenix master station beyond active stimulation of the text tower; no
//! multi-token prediction (Gemma exposes none; one future section is emitted); no native rest,
//! condensation, cultivation, or inference readiness.
//!
//! Run:
//! ```text
//! cargo run --release -q -p holonic-engine --example the_tower_conducts_layer_by_layer_and_the_future_section_is_plural -- \
//!     --text "The capital of France is" --text "2 + 2 =" [--grain 48] [--terms 14] [--no-source-face]
//! ```

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::rc::Rc;
use std::time::Instant;

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::foreign_map::FileIdentity;
use holonic_engine::front_passage::{DeedReceiver, FrontPassage, FrontPassageObstruction, MaterialAdmission, ResidentMaterial};
use holonic_engine::resident_section::{word_value, Dyadic, ResidentGrain, ResidentSection, ResidentSurface, SeriesAperture, TransferCensus};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use num_bigint::BigInt;
use relational_geometry::Rat;
use resident_layer::Source;
use tower::{Entry, KvRole, Species};

struct Args {
    root: String,
    out: String,
    texts: Vec<String>,
    token_lists: Vec<Vec<usize>>,
    grain: u32,
    terms: u32,
    source_face: bool,
    python: String,
    hidden_card_control: bool,
    top: usize,
    chart: tower::Chart,
    skip_interval_control: bool,
    vision_control: bool,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        out: "output/the_tower_conducts".to_owned(),
        texts: Vec::new(),
        token_lists: Vec::new(),
        grain: 48,
        terms: 14,
        source_face: true,
        python: "/home/b/scratch/huggingface/.venv/bin/python".to_owned(),
        hidden_card_control: false,
        top: 16,
        chart: tower::Chart::Midpoint,
        skip_interval_control: false,
        vision_control: true,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = it.next().expect("--out <dir>"),
            "--text" => args.texts.push(it.next().expect("--text <text>")),
            "--tokens" => args.token_lists.push(it.next().expect("--tokens a,b").split(',').map(|t| t.trim().parse().expect("token id")).collect()),
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--top" => args.top = it.next().expect("--top N").parse().expect("usize"),
            "--no-source-face" => args.source_face = false,
            "--python" => args.python = it.next().expect("--python <path>"),
            "--hidden-card-control" => args.hidden_card_control = true,
            "--chart" => args.chart = match it.next().expect("--chart interval|midpoint").as_str() { "interval" => tower::Chart::Interval, "midpoint" => tower::Chart::Midpoint, other => panic!("unknown chart {other}") },
            "--no-interval-control" => args.skip_interval_control = true,
            "--no-vision-control" => args.vision_control = false,
            other => panic!("unknown argument {other}"),
        }
    }
    args
}

struct Verdicts {
    lines: Vec<String>,
    failed: usize,
}

impl Verdicts {
    fn record(&mut self, number: u32, name: &str, pass: bool, detail: impl AsRef<str>) {
        let verdict = if pass { "PASS" } else { "FAIL" };
        if !pass {
            self.failed += 1;
        }
        let line = format!("  [{number:>2}] {verdict}  {name}\n        {}", detail.as_ref());
        println!("{line}");
        self.lines.push(line);
    }
    fn open(&mut self, number: u32, name: &str, why: &str) {
        let line = format!("  [{number:>2}] OPEN  {name}\n        {why}");
        println!("{line}");
        self.lines.push(line);
    }
}

fn describe(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, lineage, .. } => format!("the card refused at {occurrence:?} ({operation}): {refusal}; lineage {:?}", lineage.refusals),
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => format!("the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}"),
    }
}

/// One layer's receipt: what was admitted, what crossed, what the card measured, and the terminal
/// face's widest enclosure — the whole of the layer's typed testimony, kept per layer.
struct LayerReceipt {
    layer: usize,
    species: Species,
    role: KvRole,
    operations: usize,
    fronts: usize,
    material_resident_octets: u64,
    material_charged_octets: u64,
    material_reconciled: bool,
    semantic_bounded: usize,
    semantic_unbounded: usize,
    apparatus_bounded: usize,
    apparatus_unbounded: usize,
    graph_nodes: usize,
    graph_edges: usize,
    captured_launches: u64,
    every_front_certified: bool,
    a_priori_held: bool,
    widest_slack: i64,
    lineage_empty: bool,
    deed: ExactWork,
    terminal: Vec<(i64, i64)>,
    widest_enclosure: Rat,
    identity_held: bool,
    mount_wall_s: f64,
    bind_wall_s: f64,
    /// The collapsed population under the midpoint chart: how many quotients, the summed widths of
    /// every sealed enclosure (in grains), and the widest — what the chart deleted for the successors
    /// and retained in the predecessors' sections.
    quotients: usize,
    collapsed_width_sum: u128,
    collapsed_width_max: u64,
    collapsed_nonzero: u64,
}

/// The tower's return for one input.
struct TowerReturn {
    tokens: Vec<usize>,
    layers: Vec<LayerReceipt>,
    final_normed: Vec<(i64, i64)>,
    potential: Vec<(i64, i64)>,
    vocabulary: usize,
    positions: usize,
    tower_work: ExactWork,
    census_before: TransferCensus,
    census_after: TransferCensus,
    deed_launches: u64,
    peak_resident_octets: u64,
    wall_s: f64,
    final_material_resident_octets: u64,
    /// The widest resident requirement any one deed charged: its material plus its own sections,
    /// staging, census and lineage — what the card held at that deed, the source never whole.
    peak_charged_octets: u64,
}

/// The plural future section at one position: the tokens the enclosure does not separate from the
/// top, ordered by lower bound, and how many it does separate.
struct FutureSection {
    position: usize,
    top_lower: Rat,
    plural: Vec<(usize, Rat, Rat)>,
    separated: usize,
}

fn future_section(potential: &[(i64, i64)], position: usize, vocabulary: usize, grain: ResidentGrain, top: usize) -> FutureSection {
    let row = &potential[position * vocabulary..(position + 1) * vocabulary];
    let mut top_lower = word_value(row[0].0, grain);
    for (lo, _) in row {
        let v = word_value(*lo, grain);
        if v > top_lower {
            top_lower = v;
        }
    }
    let mut plural: Vec<(usize, Rat, Rat)> = row
        .iter()
        .enumerate()
        .filter(|(_, (_, hi))| word_value(*hi, grain) >= top_lower)
        .map(|(v, (lo, hi))| (v, word_value(*lo, grain), word_value(*hi, grain)))
        .collect();
    plural.sort_by(|a, b| b.1.cmp(&a.1));
    let separated = vocabulary - plural.len();
    plural.truncate(top.max(plural.len().min(top)));
    FutureSection { position, top_lower, plural, separated }
}

/// The native decode of tokenizer.json's vocabulary: id → piece, with `▁` as a space and byte
/// fallback pieces `<0xHH>` as their octet. An exterior codec asset read by the deed and declared
/// USED; nothing about it governs the transport.
struct Vocabulary {
    pieces: Vec<String>,
}

impl Vocabulary {
    fn read(root: &str) -> Result<Self, String> {
        let text = std::fs::read_to_string(format!("{root}/tokenizer.json")).map_err(|e| e.to_string())?;
        let json: serde_json::Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
        let vocab = json.get("model").and_then(|m| m.get("vocab")).and_then(|v| v.as_object()).ok_or("no model.vocab")?;
        let mut pieces = vec![String::new(); vocab.len()];
        for (piece, id) in vocab {
            let id = id.as_u64().ok_or("id")? as usize;
            if id < pieces.len() {
                pieces[id] = piece.clone();
            }
        }
        Ok(Self { pieces })
    }
    fn piece(&self, id: usize) -> &str {
        self.pieces.get(id).map(String::as_str).unwrap_or("<out of vocabulary>")
    }
    fn surface(&self, id: usize) -> String {
        let piece = self.piece(id);
        if let Some(hex) = piece.strip_prefix("<0x").and_then(|p| p.strip_suffix('>')) {
            if let Ok(octet) = u8::from_str_radix(hex, 16) {
                return String::from_utf8_lossy(&[octet]).to_string();
            }
        }
        piece.replace('\u{2581}', " ")
    }
}

/// The exterior token decomposition: the source tokenizer as an apparatus codec.
fn encode_texts(python: &str, texts: &[String]) -> Result<Vec<(String, Vec<usize>, Vec<String>)>, String> {
    let output = std::process::Command::new(python)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/source_runtime_tower.py"))
        .arg("encode")
        .args(texts)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).chars().take(400).collect());
    }
    let mut encoded = Vec::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        if !line.starts_with('{') {
            continue;
        }
        let json: serde_json::Value = serde_json::from_str(line).map_err(|e| e.to_string())?;
        let text = json["text"].as_str().unwrap_or_default().to_owned();
        let ids: Vec<usize> = json["ids"].as_array().ok_or("ids")?.iter().filter_map(|v| v.as_u64()).map(|v| v as usize).collect();
        let pieces: Vec<String> = json["pieces"].as_array().ok_or("pieces")?.iter().filter_map(|v| v.as_str()).map(str::to_owned).collect();
        encoded.push((text, ids, pieces));
    }
    Ok(encoded)
}

/// The source runtime's bf16 face: `hidden{k}` per position, `logits` at the last position, and the
/// surfaces of its top-k.
struct SourceFace {
    hidden: BTreeMap<usize, Vec<Vec<Rat>>>,
    logits_last: Vec<Rat>,
    surfaces: Vec<(usize, String)>,
}

fn source_face(python: &str, tokens: &[usize], emit: &str, top: usize) -> Result<SourceFace, String> {
    let output = std::process::Command::new(python)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/source_runtime_tower.py"))
        .args(["face", "--tokens", &tokens.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(","), "--emit", emit, "--top", &top.to_string()])
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).chars().take(600).collect());
    }
    let text = std::fs::read_to_string(emit).map_err(|e| e.to_string())?;
    let mut hidden: BTreeMap<usize, Vec<Vec<(usize, Rat)>>> = BTreeMap::new();
    let mut logits: Vec<(usize, Rat)> = Vec::new();
    let mut surfaces: Vec<(usize, String)> = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.splitn(4, '\t').collect();
        if parts.len() < 4 {
            continue;
        }
        let (kind, index, position, payload) = (parts[0], parts[1], parts[2], parts[3]);
        let index: usize = index.parse().map_err(|_| format!("bad index in {line}"))?;
        let position: usize = position.parse().map_err(|_| format!("bad position in {line}"))?;
        if let Some(k) = kind.strip_prefix("hidden") {
            let k: usize = k.parse().map_err(|_| format!("bad hidden index in {line}"))?;
            let bits = u64::from_str_radix(payload.trim(), 16).map_err(|_| format!("bad hex in {line}"))?;
            let value = Dyadic::of_binary64_bits(bits).map_err(|e| e.to_string())?.value();
            let rows = hidden.entry(k).or_default();
            while rows.len() <= position {
                rows.push(Vec::new());
            }
            rows[position].push((index, value));
        } else if kind == "logits" {
            let bits = u64::from_str_radix(payload.trim(), 16).map_err(|_| format!("bad hex in {line}"))?;
            logits.push((index, Dyadic::of_binary64_bits(bits).map_err(|e| e.to_string())?.value()));
        } else if kind == "surface" {
            let json: serde_json::Value = serde_json::from_str(payload).map_err(|e| e.to_string())?;
            surfaces.push((index, json["text"].as_str().unwrap_or_default().to_owned()));
        }
    }
    let hidden = hidden
        .into_iter()
        .map(|(k, rows)| {
            (k, rows.into_iter().map(|mut row| {
                row.sort_by_key(|(i, _)| *i);
                row.into_iter().map(|(_, v)| v).collect::<Vec<Rat>>()
            }).collect())
        })
        .collect();
    logits.sort_by_key(|(i, _)| *i);
    Ok(SourceFace { hidden, logits_last: logits.into_iter().map(|(_, v)| v).collect(), surfaces })
}

/// How many native coordinates land on the SAME bf16 codeword as the source's bf16 face — the
/// native chart read through the source's own codec: the sharpest cross-chart agreement face short
/// of equality, since the source cannot express anything finer than its codeword.
fn same_codeword(enclosure: &[(i64, i64)], grain: ResidentGrain, face: &[Rat]) -> (usize, usize) {
    use holonic_engine::exact_value::ieee754::round_into_bfloat16;
    let mut same = 0usize;
    let mut total = 0usize;
    for ((lo, hi), value) in enclosure.iter().zip(face) {
        let mid = (word_value(*lo, grain) + word_value(*hi, grain)) / Rat::from_integer(BigInt::from(2));
        if let (Ok((native, _)), Ok((theirs, _))) = (round_into_bfloat16(&mid), round_into_bfloat16(value)) {
            total += 1;
            if native == theirs {
                same += 1;
            }
        }
    }
    (same, total)
}

/// inside / outside / worst gap of a source face against a resident enclosure.
fn defect(enclosure: &[(i64, i64)], grain: ResidentGrain, face: &[Rat]) -> (usize, usize, Rat) {
    let mut inside = 0usize;
    let mut outside = 0usize;
    let mut worst = Rat::from_integer(BigInt::from(0));
    for ((lo, hi), value) in enclosure.iter().zip(face) {
        let lo = word_value(*lo, grain);
        let hi = word_value(*hi, grain);
        if lo <= *value && *value <= hi {
            inside += 1;
        } else {
            outside += 1;
            let gap = if *value < lo { &lo - value } else { value - &hi };
            if gap > worst {
                worst = gap;
            }
        }
    }
    (inside, outside, worst)
}

fn rat_f64(value: &Rat) -> f64 {
    use num_traits::ToPrimitive;
    value.numer().to_f64().unwrap_or(f64::NAN) / value.denom().to_f64().unwrap_or(f64::NAN)
}

/// **The tower deed for one input**: 42 layer graphs and the final graph, each admitted, bound,
/// launched once and released, the standings carried on the card.
#[allow(clippy::too_many_arguments)]
fn conduct_tower(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: &str,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    read_layers: bool,
    chart: tower::Chart,
    limit: usize,
) -> Result<TowerReturn, (String, Vec<LayerReceipt>)> {
    let mut layers: Vec<LayerReceipt> = Vec::new();
    match conduct_tower_inner(surface, readout, source, root, header_regions, content_sha256, tokens, grain, terms, read_layers, chart, limit, &mut layers) {
        Ok(returned) => Ok(returned),
        Err(message) => Err((message, layers)),
    }
}

#[allow(clippy::too_many_arguments)]
fn conduct_tower_inner(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: &str,
    tokens: &[usize],
    grain: ResidentGrain,
    terms: SeriesAperture,
    read_layers: bool,
    chart: tower::Chart,
    limit: usize,
    layers: &mut Vec<LayerReceipt>,
) -> Result<TowerReturn, String> {
    let clock = Instant::now();
    let passage = FrontPassage::new(surface, grain);
    let receiver = DeedReceiver::unbounded();
    let scales = tower::algebraic_scales()?;
    let census_before = surface.census();
    let mut regions = header_regions.clone();
    let mut carried: Option<(Rc<ResidentSection<'static>>, u32)> = None;
    let mut shared: BTreeMap<&'static str, (Rc<ResidentSection<'static>>, u32)> = BTreeMap::new();
    let mut tower_work = ExactWork::nothing();
    let mut deed_launches = 0u64;
    let mut peak_charged_octets = 0u64;
    // bands per species, founded once
    let sliding_bands = tower::found_bands(Species::Sliding, resident_layer::BAND_TERMS)?;
    let full_bands = tower::found_bands(Species::Full, resident_layer::BAND_TERMS)?;
    let positions: Vec<u32> = (0..tokens.len() as u32).collect();
    for layer in 0..tower::LAYERS.min(limit) {
        let species = Species::of(layer);
        let role = KvRole::of(layer);
        let mut material = ResidentMaterial::empty();
        // the material deed: predicted from the header and admitted before any map is allocated
        let plan = tower::material_plan(source, layer, tokens.len())?;
        let prediction = passage.predict_material(&plan);
        let admission: MaterialAdmission = passage.admit_material(&prediction).map_err(|o| format!("layer {layer} material refused: {}", describe(&o)))?;
        let mount_clock = Instant::now();
        let mount = tower::mount_layer(source, readout, &mut material, layer)?;
        let mount_wall_s = mount_clock.elapsed().as_secs_f64();
        let reconciled = admission.reconcile(&material);
        let material_reconciled = reconciled.iter().all(|(_, p, m)| p == m) && reconciled.len() == plan.maps.len();
        for (name, region) in mount.regions {
            regions.insert(name, region);
        }
        let identity_held = FileIdentity::at(&format!("{root}/model.safetensors")).ok().is_some_and(|now| header_regions.is_empty() || Some(&now) == FileIdentity::at(&format!("{root}/model.safetensors")).ok().as_ref());
        let layer_scalar = mount.layer_scalar.ok_or("layer_scalar")?;
        // bands and positions
        let bands = match species {
            Species::Sliding => &sliding_bands,
            Species::Full => &full_bands,
        };
        let mounted_bands = surface.mount_bands(bands, tower::BAND_GRAIN).map_err(|e| e.to_string())?;
        material.bands.insert(species.bands().to_owned(), (mounted_bands, (tokens.len() - 1) as u32));
        material.positions = Some(surface.mount_positions(&positions).map_err(|e| e.to_string())?);
        // the runtime material and the standings
        tower::enter(source, tokens, layer, &mut material)?;
        let entry = if layer == 0 { Entry::Rows } else { Entry::Carried };
        if let Some((section, bound)) = &carried {
            material.standings.insert(tower::CARRIED_STANDING.to_owned(), (Rc::clone(section), *bound));
        }
        if role == KvRole::Shared {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = shared.get(k_name).ok_or_else(|| format!("layer {layer}: no shared K standing {k_name}"))?;
            let (v, vb) = shared.get(v_name).ok_or_else(|| format!("layer {layer}: no shared V standing {v_name}"))?;
            material.standings.insert(k_name.to_owned(), (Rc::clone(k), *kb));
            material.standings.insert(v_name.to_owned(), (Rc::clone(v), *vb));
        }
        // the source occurrence for this layer's testimony: every region this layer reads, hashed
        let occurrence: SourceOccurrence = resident_layer::source_occurrence(root, regions.clone(), Some(content_sha256.to_owned()))?;
        let founded = tower::found_layer(layer, entry, chart, &scales, terms, layer_scalar, &tower::Intervention::None, tokens.len())?;
        let bind_clock = Instant::now();
        let mut bound = passage.bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), founded.returns[tower::LAYER_RETURN]).map_err(|o| format!("layer {layer} refused at bind: {}", describe(&o)))?;
        let bind_wall_s = bind_clock.elapsed().as_secs_f64();
        peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
        let returned = bound.launch(&surface.mode()).map_err(|o| format!("layer {layer} refused at launch: {}", describe(&o)))?;
        deed_launches += 1;
        if let Err(o) = bound.standing(&returned) {
            // the diagnostic face of a refusal: every occurrence's bound against its measured octave,
            // in front order, so the refusal is located and not narrated
            let mut lines = Vec::new();
            for front in &returned.fronts {
                for r in &front.readings {
                    lines.push(format!("{}:{}≤{}{}", r.operation, r.measured.max_octave, r.bound, if r.measured.refused != 0 { format!("!{}", r.measured.refused) } else { String::new() }));
                }
            }
            return Err(format!("layer {layer} did not stand: {} · readings [{}]", describe(&o), lines.join(" ")));
        }
        let (graph, _) = bound.graph();
        let every_front_certified = bound.fronts().iter().all(|f| f.certificate.is_interchangeable());
        let mut a_priori_held = true;
        let mut widest_slack = 0i64;
        for (port, measured) in &returned.measured_octaves {
            let b = bound.octave_field.get(port).copied().unwrap_or(0);
            if b < *measured {
                a_priori_held = false;
            }
            widest_slack = widest_slack.max(i64::from(b) - i64::from(*measured));
        }
        let terminal = if read_layers { bound.read_section(&returned, founded.returns[tower::LAYER_ENCLOSURE]).map_err(|o| describe(&o))? } else { Vec::new() };
        let widest_enclosure = terminal.iter().map(|(l, h)| word_value(*h, grain) - word_value(*l, grain)).max().unwrap_or_else(|| Rat::from_integer(BigInt::from(0)));
        let mut quotients = 0usize;
        let mut collapsed_width_sum: u128 = 0;
        let mut collapsed_width_max: u64 = 0;
        let mut collapsed_nonzero: u64 = 0;
        for front in &returned.fronts {
            for r in &front.readings {
                if r.operation == "midpoint-quotient" {
                    quotients += 1;
                }
            }
        }
        // the collapsed population is what the quotients' predecessors carried: sum over every
        // non-quotient occurrence's census of its widths (under the midpoint chart every such
        // enclosure is sealed before it is read again)
        for front in &returned.fronts {
            for r in &front.readings {
                if r.operation != "midpoint-quotient" && r.operation != "enter" && r.operation != "carry" {
                    collapsed_width_sum += u128::from(r.measured.width_sum);
                    collapsed_width_max = collapsed_width_max.max(r.measured.max_width);
                    collapsed_nonzero += u64::from(r.measured.nonzero_widths);
                }
            }
        }
        tower_work = tower_work.then(&bound.deed_prediction);
        layers.push(LayerReceipt {
            layer,
            species,
            role,
            operations: founded.complex.operations.len(),
            fronts: bound.fronts().len(),
            material_resident_octets: admission.resident_octets(),
            material_charged_octets: admission.prediction.charged_octets,
            material_reconciled,
            semantic_bounded: bound.admission.semantic.iter().filter(|c| c.is_bounded()).count(),
            semantic_unbounded: bound.admission.semantic.iter().filter(|c| !c.is_bounded()).count(),
            apparatus_bounded: bound.admission.apparatus.iter().filter(|c| c.is_bounded()).count(),
            apparatus_unbounded: bound.admission.apparatus.iter().filter(|c| !c.is_bounded()).count(),
            graph_nodes: graph.nodes,
            graph_edges: graph.edges,
            captured_launches: bound.apparatus_prediction.captured_launches,
            every_front_certified,
            a_priori_held,
            widest_slack,
            lineage_empty: returned.stands(),
            deed: bound.deed_prediction.clone(),
            terminal,
            widest_enclosure,
            identity_held,
            mount_wall_s,
            bind_wall_s,
            quotients,
            collapsed_width_sum,
            collapsed_width_max,
            collapsed_nonzero,
        });
        // release the standings the next deeds carry
        if role == KvRole::OwnAndStore {
            let (k_name, v_name) = match species {
                Species::Sliding => (tower::SHARED_K_SLIDING, tower::SHARED_V_SLIDING),
                Species::Full => (tower::SHARED_K_FULL, tower::SHARED_V_FULL),
            };
            let (k, kb) = bound.release_section(founded.returns[tower::K_STANDING]).ok_or("K standing")?;
            let (v, vb) = bound.release_section(founded.returns[tower::V_STANDING]).ok_or("V standing")?;
            shared.insert(k_name, (Rc::new(k), kb));
            shared.insert(v_name, (Rc::new(v), vb));
        }
        let (out, ob) = bound.release_section(founded.returns[tower::LAYER_RETURN]).ok_or("layer return")?;
        carried = Some((Rc::new(out), ob));
        drop(bound);
        drop(material); // the layer's maps, bands and positions leave the card
    }
    // the final deed
    let mut material = ResidentMaterial::empty();
    let plan = tower::final_material_plan(source)?;
    let prediction = passage.predict_material(&plan);
    let admission = passage.admit_material(&prediction).map_err(|o| format!("final material refused: {}", describe(&o)))?;
    let mount = tower::mount_final(source, readout, &mut material)?;
    for (name, region) in mount.regions {
        regions.insert(name, region);
    }
    let (section, bound_octaves) = carried.take().ok_or("no carried standing")?;
    material.standings.insert(tower::CARRIED_STANDING.to_owned(), (section, bound_octaves));
    let occurrence = resident_layer::source_occurrence(root, regions.clone(), Some(content_sha256.to_owned()))?;
    let founded = tower::found_final(chart, &tower::Intervention::None, &scales)?;
    let bound = passage.bind(&founded.complex, &founded.realization, &material, &occurrence, &receiver, Some(&admission), founded.returns[tower::POTENTIAL]).map_err(|o| format!("final refused at bind: {}", describe(&o)))?;
    peak_charged_octets = peak_charged_octets.max(admission.prediction.charged_octets + bound.apparatus_prediction.charged_octets);
    let returned = bound.launch(&surface.mode()).map_err(|o| format!("final refused at launch: {}", describe(&o)))?;
    deed_launches += 1;
    bound.standing(&returned).map_err(|o| format!("final did not stand: {}", describe(&o)))?;
    let final_normed = bound.read_section(&returned, founded.returns[tower::FINAL_NORMED]).map_err(|o| describe(&o))?;
    let potential = bound.read_terminal(&returned).map_err(|o| describe(&o))?;
    tower_work = tower_work.then(&bound.deed_prediction);
    let census_after = surface.census();
    Ok(TowerReturn {
        tokens: tokens.to_vec(),
        layers: std::mem::take(layers),
        final_normed,
        potential,
        vocabulary: tower::VOCABULARY,
        positions: tokens.len(),
        tower_work,
        census_before,
        census_after: census_after.clone(),
        deed_launches,
        peak_resident_octets: census_after.resident_octets_peak,
        wall_s: clock.elapsed().as_secs_f64(),
        final_material_resident_octets: admission.resident_octets(),
        peak_charged_octets,
    })
}

/// **The bounded portability control: one real non-text projection crosses its typed ports on the
/// card.** The source's vision tower runs as an exterior apparatus on a deterministic synthetic
/// image and emits its soft tokens (256 × 768, bf16); those enter the resident deed as entering
/// rows, the gain-less RMS rebase over 768 and the `embed_vision` projection into the shared stream
/// are enacted natively — the projection into the 2,560-wide stream is a real non-text transport
/// crossing typed ports — and the source's own `embed_vision` output is the cross-chart defect slot.
/// The vision tower itself is not posed natively; this control claims portability of the
/// projection, not image recognition.
#[allow(clippy::too_many_arguments)]
fn vision_projection_control(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    source: &mut Source,
    root: &str,
    header_regions: &BTreeMap<String, RegionIdentity>,
    content_sha256: &str,
    python: &str,
    out: &str,
    grain: ResidentGrain,
    chart: tower::Chart,
) -> Result<String, String> {
    use holonic_engine::exact_value::ieee754::round_into_bfloat16;
    use holonic_engine::front_passage::{Contract, Enter, EnteringRows, MountedPopulation, ResidentRealization, RmsRebase};
    use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex};
    let emit = format!("{out}/vision-soft-tokens.tsv");
    let output = std::process::Command::new(python)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/source_runtime_tower.py"))
        .args(["vision", "--emit", &emit])
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(format!("the exterior vision tower refused: {}", String::from_utf8_lossy(&output.stderr).chars().take(400).collect::<String>()));
    }
    let text = std::fs::read_to_string(&emit).map_err(|e| e.to_string())?;
    let mut soft: BTreeMap<usize, Vec<(usize, Rat)>> = BTreeMap::new();
    let mut projected: BTreeMap<usize, Vec<(usize, Rat)>> = BTreeMap::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.splitn(4, '\t').collect();
        if parts.len() < 4 {
            continue;
        }
        let index: usize = parts[1].parse().map_err(|_| format!("bad index: {line}"))?;
        let position: usize = parts[2].parse().map_err(|_| format!("bad position: {line}"))?;
        let bits = u64::from_str_radix(parts[3].trim(), 16).map_err(|_| format!("bad hex: {line}"))?;
        let value = Dyadic::of_binary64_bits(bits).map_err(|e| e.to_string())?.value();
        match parts[0] {
            "soft" => soft.entry(position).or_default().push((index, value)),
            "projected" => projected.entry(position).or_default().push((index, value)),
            _ => {}
        }
    }
    let rows = soft.len();
    let width = soft.values().next().map(Vec::len).unwrap_or(0);
    if rows == 0 || width != 768 {
        return Err(format!("the soft tokens did not read: {rows} rows of {width}"));
    }
    // the soft tokens as bf16 words — each value is a bf16 codeword exactly, so the residual is zero
    let mut words: Vec<u16> = Vec::with_capacity(rows * width);
    let mut residual_nonzero = 0usize;
    for position in 0..rows {
        let mut row = soft[&position].clone();
        row.sort_by_key(|(i, _)| *i);
        for (_, value) in row {
            let (word, residual) = round_into_bfloat16(&value).map_err(|e| format!("{e:?}"))?;
            if residual != Rat::from_integer(BigInt::from(0)) {
                residual_nonzero += 1;
            }
            words.push(word);
        }
    }
    // the grain of this deed is derived from the material: the soft tokens reach |v| ≈ 4.2e4, so the
    // word holds them at a coarser grain than the text tower's; the grain is `62 − octaves(max|soft|)
    // − 8` (eight octaves for the rebase's radical and the projection's mass), stated in the return
    let widest_soft = soft.values().flat_map(|row| row.iter().map(|(_, v)| num_traits::Signed::abs(v))).max().unwrap_or_else(|| Rat::from_integer(BigInt::from(1)));
    let widest_octaves = widest_soft.ceil().to_integer().bits() as u32;
    let vision_grain = ResidentGrain(62u32.saturating_sub(widest_octaves + 8).min(grain.0));
    let passage = FrontPassage::new(surface, vision_grain);
    let grain = vision_grain;
    let population = "model.embed_vision.embedding_projection.weight";
    let plan = holonic_engine::front_passage::MaterialPlan { maps: vec![(population.to_owned(), tower::HIDDEN, 768)], band_elements: 0, positions: 0 };
    let admission = passage.admit_material(&passage.predict_material(&plan)).map_err(|o| describe(&o))?;
    let (map_words, shape) = source.whole(population)?;
    let mut material = ResidentMaterial::empty();
    let mounted = readout.mount_bfloat16(&map_words, *shape.last().ok_or("shape")?).map_err(|e| format!("{e:?}"))?;
    let masses = mounted.absolute_row_mass().map_err(|e| format!("{e:?}"))?;
    let widest = masses.iter().map(|m| m.unsigned_abs()).max().unwrap_or(0);
    let mass_octaves = i64::from(128 - widest.leading_zeros()) + i64::from(mounted.exponent());
    material.populations.insert(population.to_owned(), MountedPopulation { readout: mounted, mass_value_octaves: u32::try_from(mass_octaves.max(0)).unwrap_or(0) });
    material.entering.insert("vision soft tokens".to_owned(), EnteringRows { words, rows, width });
    let mut regions = header_regions.clone();
    regions.insert(population.to_owned(), source.region(population, Some(resident_layer::digest_words(&map_words)))?);
    // the occurrence under the vision configuration scope
    let implementation = holonic_engine::source_occurrence::AuthenticatedText::read(resident_layer::IMPLEMENTATION, resident_layer::implementation_version().as_deref()).map_err(|e| e.to_string())?;
    let configuration = holonic_engine::source_occurrence::AuthenticatedText::read(&format!("{root}/config.json"), None).map_err(|e| e.to_string())?;
    let locator = format!("{root}/model.safetensors");
    let (octets, header_octets, header_sha256) = holonic_engine::source_occurrence::AuthenticatedContainer::read_header(&locator).map_err(|e| e.to_string())?;
    let occurrence = SourceOccurrence {
        implementation,
        configuration,
        configuration_scope: vec!["vision_config".to_owned()],
        container: holonic_engine::source_occurrence::AuthenticatedContainer { identity: FileIdentity::at(&locator).ok(), locator, octets, header_octets, header_sha256, content_sha256: Some(content_sha256.to_owned()), regions },
        assets: Vec::new(),
    };
    let eps_text = occurrence.configuration_span("rms_norm_eps").ok_or("vision rms_norm_eps")?;
    let eps = Dyadic::of_binary64_bits(resident_layer::EPS_BITS).map_err(|e| e.to_string())?; // 1e-06, the same declared decimal as the text tower's; entailed against the vision scope's field below
    let mut complex = PortedOperationComplex::new("vision soft tokens projected into the shared stream");
    let modality_port = complex.port("vision tower output, 768");
    let standing = complex.port("continuing standing, 2560");
    let mut realization = ResidentRealization::default();
    let enter = resident_layer::law(&mut complex, "vision soft tokens", OperationSpecies::Construction, vec![], vec![modality_port], None, vec![
        resident_layer::implementation("Gemma4Model.get_image_features (vision_outputs.pooler_output = self.embed_vision(inputs_embeds=last_hidden_state))"),
        resident_layer::configuration("hidden_size", "768"),
    ])?;
    realization.bind(enter, Enter { population: "vision soft tokens".to_owned(), scale: Dyadic::ONE });
    let rebase = resident_layer::law(&mut complex, "vision pre-projection rebase, no gain", OperationSpecies::Transport, vec![modality_port], vec![modality_port], None, vec![
        resident_layer::implementation("Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))"),
        resident_layer::implementation("Gemma4MultimodalEmbedder.__init__ (self.embedding_pre_projection_norm = Gemma4RMSNorm(self.multimodal_hidden_size, eps=self.eps, with_scale=False))"),
        resident_layer::implementation("Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))"),
        resident_layer::configuration("rms_norm_eps", &eps_text),
        resident_layer::configuration("hidden_size", "768"),
    ])?;
    realization.bind(rebase, RmsRebase { group: 768, gain: None, eps });
    resident_layer::bond(&mut complex, "soft tokens rebase", modality_port, enter, rebase, 0)?;
    let rebase = tower::seal(chart, &mut complex, &mut realization, rebase, modality_port, "vision rebase")?;
    let projection = resident_layer::law(&mut complex, "vision projection", OperationSpecies::Transport, vec![modality_port], vec![standing], Some(population.to_owned()), vec![
        resident_layer::implementation("Gemma4MultimodalEmbedder.forward (return self.embedding_projection(embs_normed))"),
        resident_layer::shape(population, &[tower::HIDDEN, 768]),
    ])?;
    realization.bind(projection, Contract { population: population.to_owned() });
    resident_layer::bond(&mut complex, "projects into the stream", modality_port, rebase, projection, 0)?;
    let bound = passage.bind(&complex, &realization, &material, &occurrence, &DeedReceiver::unbounded(), Some(&admission), projection).map_err(|o| describe(&o))?;
    let returned = bound.launch(&surface.mode()).map_err(|o| describe(&o))?;
    bound.standing(&returned).map_err(|o| describe(&o))?;
    let native = bound.read_terminal(&returned).map_err(|o| describe(&o))?;
    // the cross-chart defect against the source's own projection
    let mut inside = 0usize;
    let mut outside = 0usize;
    let mut worst = Rat::from_integer(BigInt::from(0));
    let mut max_abs = Rat::from_integer(BigInt::from(0));
    for position in 0..rows {
        let mut row = projected.get(&position).cloned().unwrap_or_default();
        row.sort_by_key(|(i, _)| *i);
        for (i, value) in row {
            let (lo, hi) = native[position * tower::HIDDEN + i];
            let lo = word_value(lo, grain);
            let hi = word_value(hi, grain);
            if num_traits::Signed::abs(&value) > max_abs { max_abs = num_traits::Signed::abs(&value); }
            if lo <= value && value <= hi { inside += 1; } else { outside += 1; let gap = if value < lo { &lo - &value } else { &value - &hi }; if gap > worst { worst = gap; } }
        }
    }
    let mut same = 0usize;
    let mut total = 0usize;
    for position in 0..rows {
        let mut row = projected.get(&position).cloned().unwrap_or_default();
        row.sort_by_key(|(i, _)| *i);
        let face: Vec<Rat> = row.into_iter().map(|(_, v)| v).collect();
        let (s, t) = same_codeword(&native[position * tower::HIDDEN..(position + 1) * tower::HIDDEN], grain, &face);
        same += s;
        total += t;
    }
    Ok(format!("{rows} soft tokens × {width} from the exterior vision tower (bf16 words, {residual_nonzero} nonzero round-trip residuals, widest |value| {:.3e} so the deed's grain is 2^-{} derived from the material) entered the card; the gain-less rebase over 768 and the embed_vision projection [2560, 768] ran as one graph ({} nodes, admitted, lineage empty {}) returning {rows} × 2560; against the source's own embed_vision output (bf16): inside {inside}, outside {outside}, worst gap {:.3e} at values up to {:.3e}; the native chart lands on the source's bf16 codeword at {same} of {total} coordinates (the bf16 face rounds every intermediate; the native chart is {:?})",
        rat_f64(&widest_soft), grain.0, bound.graph().0.nodes, returned.stands(), rat_f64(&worst), rat_f64(&max_abs), chart))
}

fn main() {
    let args = parse_args();
    println!("THE TOWER CONDUCTS LAYER BY LAYER AND THE FUTURE SECTION IS PLURAL — {}", args.root);
    std::fs::create_dir_all(&args.out).expect("output directory");
    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };
    // the apparatus, or the typed refusal
    let readout: &'static ResidentReadout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(error) => {
            println!("REFUSED: no resident chart — {error}");
            println!("  There is no CPU semantic fallback. No answer is returned.");
            std::process::exit(3);
        }
    };
    let surface: &'static ResidentSurface<'static> = match ResidentSurface::on(readout) {
        Ok(surface) => Box::leak(Box::new(surface)),
        Err(error) => {
            println!("REFUSED: the resident laws did not load — {error}");
            std::process::exit(3);
        }
    };
    if args.hidden_card_control {
        println!("the card answered ({}); the hidden-card control did not hide it", surface.device_name());
        std::process::exit(5);
    }
    println!("  resident chart: {} · mode {} · allocation grain {} · memory {} free of {}",
        surface.device_name(), surface.mode().kernel_content.as_deref().unwrap_or("?"), surface.allocation_grain(), surface.memory_at_mount().free_bytes, surface.memory_at_mount().total_bytes);
    let grain = ResidentGrain(args.grain);
    let terms = SeriesAperture(args.terms);

    // the inputs: exterior token decomposition for texts, identities as given for token lists
    let mut inputs: Vec<(String, Vec<usize>, Vec<String>)> = Vec::new();
    if !args.texts.is_empty() {
        match encode_texts(&args.python, &args.texts) {
            Ok(encoded) => inputs.extend(encoded),
            Err(error) => {
                println!("REFUSED: the exterior tokenizer could not decompose the texts — {error}");
                std::process::exit(4);
            }
        }
    }
    for list in &args.token_lists {
        inputs.push((format!("{list:?}"), list.clone(), list.iter().map(|t| t.to_string()).collect()));
    }
    if inputs.is_empty() {
        println!("REFUSED: no input — give --text or --tokens; the material is supplied at runtime and compiled into nothing");
        std::process::exit(2);
    }
    println!("  {} runtime-supplied inputs:", inputs.len());
    for (text, ids, pieces) in &inputs {
        println!("    {text:?} → {ids:?} {pieces:?}");
    }
    let vocabulary = Vocabulary::read(&args.root).expect("tokenizer.json vocabulary");

    // the source, the header regions, the content digest (taken once, streamed)
    let mut source = Source::open(&args.root).expect("source opens");
    let mut header_regions: BTreeMap<String, RegionIdentity> = BTreeMap::new();
    for name in source.container.names() {
        if let Ok(region) = source.region(name, None) {
            header_regions.insert(name.to_owned(), region);
        }
    }
    let digest_clock = Instant::now();
    let content_sha256 = holonic_engine::source_occurrence::AuthenticatedContainer::digest_whole(&format!("{}/model.safetensors", args.root)).expect("digest");
    println!("  container content sha256 {} ({:.1} s) · {} regions identified from the header", &content_sha256[..16], digest_clock.elapsed().as_secs_f64(), header_regions.len());

    // ------------------------------------------------------------------------------------------
    // THE DEEDS — one tower per input
    // ------------------------------------------------------------------------------------------
    let mut returns: Vec<TowerReturn> = Vec::new();
    for (text, ids, _) in &inputs {
        println!("\nTHE TOWER — {text:?} ({} tokens)", ids.len());
        match conduct_tower(surface, readout, &mut source, &args.root, &header_regions, &content_sha256, ids, grain, terms, true, args.chart, tower::LAYERS) {
            Ok(returned) => {
                println!("  {} layer deeds + the final deed in {:.1} s · deed launches {} · tower semantic work {:?} · widest charge of one deed {} octets · the surface's own peak {} octets",
                    returned.layers.len(), returned.wall_s, returned.deed_launches, returned.tower_work.coordinates().iter().map(|(n, v)| format!("{n}={v}")).collect::<Vec<_>>(), returned.peak_charged_octets, returned.peak_resident_octets);
                for l in returned.layers.iter().filter(|l| l.layer == 0 || l.layer == 22 || l.layer == 23 || l.layer == 24 || l.layer == 41) {
                    println!("    layer {:>2} {:?} {:?}: {} operations · {} fronts · material {} octets (charged {}, reconciled {}) · graph {}/{} · launches {} · certified {} · a-priori held {} (slack {}) · lineage empty {} · widest enclosure {:.3e} · mount {:.2} s bind {:.3} s",
                        l.layer, l.species, l.role, l.operations, l.fronts, l.material_resident_octets, l.material_charged_octets, l.material_reconciled, l.graph_nodes, l.graph_edges, l.captured_launches, l.every_front_certified, l.a_priori_held, l.widest_slack, l.lineage_empty, rat_f64(&l.widest_enclosure), l.mount_wall_s, l.bind_wall_s);
                }
                let future = future_section(&returned.potential, returned.positions - 1, returned.vocabulary, grain, args.top);
                println!("  THE PLURAL FUTURE SECTION at position {}: top lower bound {:.4} · {} candidates not separated from the top · {} separated",
                    future.position, rat_f64(&future.top_lower), future.plural.len() + 0, future.separated);
                for (id, lo, hi) in future.plural.iter().take(8) {
                    println!("      {id:>7}  [{:.4}, {:.4}]  {:?}", rat_f64(lo), rat_f64(hi), vocabulary.surface(*id));
                }
                returns.push(returned);
            }
            Err((error, partial)) => {
                println!("REFUSED after {} layers: {error}", partial.len());
                std::process::exit(4);
            }
        }
    }
    // the per-layer collapsed population, printed for the first input
    if let Some(first) = returns.first() {
        println!("  collapsed population under the {:?} chart (layer: quotients, sum of widths in grains, widest, nonzero): {}", args.chart,
            first.layers.iter().filter(|l| l.layer % 7 == 0 || l.layer == 41).map(|l| format!("{}: {} q · Σ {} · max {} · nz {}", l.layer, l.quotients, l.collapsed_width_sum, l.collapsed_width_max, l.collapsed_nonzero)).collect::<Vec<_>>().join(" | "));
    }

    // the interval chart's divergence: the certified enclosure of the composed tower, measured
    let mut interval_control: Option<(String, Rat, Rat, usize)> = None;
    if !args.skip_interval_control {
        println!("\nTHE INTERVAL CHART — the certified enclosure propagated whole, until the word refuses");
        let (_, ids, _) = &inputs[0];
        match conduct_tower(surface, readout, &mut source, &args.root, &header_regions, &content_sha256, ids, grain, terms, true, tower::Chart::Interval, tower::LAYERS) {
            Ok(returned) => {
                println!("  the interval chart carried every layer (unexpected at this grain); widest terminal enclosures: {:?}", returned.layers.iter().map(|l| rat_f64(&l.widest_enclosure)).collect::<Vec<_>>());
                interval_control = Some(("carried".to_owned(), returned.layers[0].widest_enclosure.clone(), returned.layers.last().map(|l| l.widest_enclosure.clone()).unwrap_or_else(|| Rat::from_integer(BigInt::from(0))), returned.layers.len()));
            }
            Err((error, partial)) => {
                let entering = Rat::new(BigInt::from(1), BigInt::from(1) << args.grain as usize);
                let layer0 = partial.first().map(|l| l.widest_enclosure.clone()).unwrap_or_else(|| Rat::from_integer(BigInt::from(0)));
                let amplification = if layer0 > Rat::from_integer(BigInt::from(0)) { &layer0 / &entering } else { Rat::from_integer(BigInt::from(0)) };
                println!("  the interval chart refused after {} layer(s): {}", partial.len(), error.chars().take(300).collect::<String>());
                println!("  layer 0's widest certified enclosure {:.3e} against the entering grain {:.3e}: amplification ≈ 2^{:.1}", rat_f64(&layer0), rat_f64(&entering), rat_f64(&amplification).log2());
                interval_control = Some((error, layer0, amplification, partial.len()));
            }
        }
    }

    // ------------------------------------------------------------------------------------------
    // THE FALSIFIERS
    // ------------------------------------------------------------------------------------------
    println!("\nTHE FALSIFIERS");
    let first = &returns[0];
    // 1. the complete pathway: 42 layers + final, every layer one graph, admitted, certified, standing
    let every_layer_whole = returns.iter().all(|r| r.layers.len() == tower::LAYERS && r.layers.iter().all(|l| l.lineage_empty && l.every_front_certified && l.a_priori_held && l.material_reconciled && l.semantic_unbounded + l.semantic_bounded == 9 && l.apparatus_bounded >= 5));
    verdicts.record(1, "every input crossed all 42 layers and the tied output boundary, each layer one graph launched once, typed admission, footprint certificates, the a-priori law held and the obstruction lineage empty",
        every_layer_whole && returns.iter().all(|r| r.deed_launches == tower::LAYERS as u64 + 1 && r.potential.len() == r.positions * r.vocabulary),
        format!("{} inputs · {} layer deeds + 1 final each · deed launches {} each · potential sections {} × 262144 · every layer: lineage empty, every front certified, a-priori ≥ measured, material reconciled, 9 semantic coordinates typed, ≥5 apparatus coordinates bounded",
            returns.len(), tower::LAYERS, first.deed_launches, first.positions));
    // 2. both species, both head widths, both RoPE species, the KV-sharing realization
    let species_seen: BTreeSet<String> = first.layers.iter().map(|l| format!("{:?}", l.species)).collect();
    let roles_seen: BTreeSet<String> = first.layers.iter().map(|l| format!("{:?}", l.role)).collect();
    let shared_ops = first.layers.iter().filter(|l| l.role == KvRole::Shared).map(|l| l.operations).collect::<BTreeSet<_>>();
    let own_ops = first.layers.iter().filter(|l| l.role != KvRole::Shared).map(|l| l.operations).collect::<BTreeSet<_>>();
    verdicts.record(2, "the KV-sharing realization, both attention species and both RoPE species were enacted: layers 22 and 23 stored their K/V standings, layers 24–41 read them through carried standings and built no K/V, the 7 full layers ran at head 512 with the proportional chronology",
        species_seen.len() == 2 && roles_seen.len() == 3 && first.layers.iter().filter(|l| l.species == Species::Full).count() == 7 && first.layers.iter().filter(|l| l.role == KvRole::Shared).count() == 18 && shared_ops.iter().all(|o| own_ops.iter().all(|p| o < p)),
        format!("species {species_seen:?} · roles {roles_seen:?} · operations per shared layer {shared_ops:?} < per own layer {own_ops:?} (no K/V projections or K rebase in a shared layer)"));
    // 3. the residual stream and the shared standings crossed on the card: no section egress except the reads this driver declared
    let read_octets: u64 = returns.iter().map(|r| r.layers.iter().map(|l| (2 * l.terminal.len() * 8) as u64).sum::<u64>() + (2 * r.final_normed.len() * 8) as u64 + (2 * r.potential.len() * 8) as u64).sum();
    let egress: u64 = returns.iter().map(|r| r.census_after.egress_section_octets - r.census_before.egress_section_octets).sum();
    let d2d: u64 = returns.iter().map(|r| r.census_after.device_to_device_octets - r.census_before.device_to_device_octets).sum();
    verdicts.record(3, "standings cross between layer graphs on the card: the only section egress is the reads this driver declared (per-layer terminal faces for the comparison, the final normed standing, the potential section)",
        egress == read_octets,
        format!("section egress {egress} octets = declared reads {read_octets} · device-to-device {d2d} · the carried standing and the shared K/V enter each layer's graph by section_carry, never through the apparatus boundary"));
    // 4. streamable: the whole source never resident — the peak resident octets stay below the source
    let source_octets: u64 = 15_992_595_884;
    verdicts.record(4, "the method is streamable by layer: each layer's populations are predicted, admitted, mounted, used once and released; the widest charge any one deed makes on the card stays far below the source",
        returns.iter().all(|r| r.peak_charged_octets < source_octets / 2) && first.layers.iter().all(|l| l.material_charged_octets >= l.material_resident_octets),
        format!("widest charge of one deed (its material + its sections, staging, census and lineage) {} octets against the source's {source_octets} · per-layer material {}..{} octets · the final deed's material (the tied table, aligned) {} octets · the surface's own peak (sections, staging, census) {} octets",
            first.peak_charged_octets, first.layers.iter().map(|l| l.material_resident_octets).min().unwrap_or(0), first.layers.iter().map(|l| l.material_resident_octets).max().unwrap_or(0), first.final_material_resident_octets, first.peak_resident_octets));
    // 5. several runtime inputs separate: different inputs, different terminal standings and futures; the graph is invariant under the material
    let futures: Vec<FutureSection> = returns.iter().map(|r| future_section(&r.potential, r.positions - 1, r.vocabulary, grain, args.top)).collect();
    let distinct_final: BTreeSet<Vec<(i64, i64)>> = returns.iter().map(|r| r.final_normed.clone()).collect();
    verdicts.record(5, "several runtime-supplied inputs cross the same bound laws and return distinct standings and futures; nothing about the inputs is compiled into any diagram",
        returns.len() >= 2 && distinct_final.len() == returns.len() && returns.iter().all(|r| r.layers.iter().zip(&first.layers).all(|(a, b)| a.operations == b.operations && a.fronts == b.fronts)),
        format!("{} inputs, {} distinct final standings · per-layer operation and front counts identical across inputs · futures: {:?}",
            returns.len(), distinct_final.len(), futures.iter().map(|f| (f.position, f.plural.len(), f.separated, f.plural.first().map(|(id, ..)| vocabulary.surface(*id)))).collect::<Vec<_>>()));
    // 6. the plural future section is a receiver face: candidates not separated from the top, and a decoded surface
    verdicts.record(6, "the potential section returns a PLURAL future section — the tokens the enclosure does not separate from the top — and an actual decoded surface from the native vocabulary",
        futures.iter().all(|f| !f.plural.is_empty() && f.separated + f.plural.len() <= tower::VOCABULARY) && futures.iter().all(|f| f.plural.iter().all(|(id, _, _)| !vocabulary.piece(*id).is_empty())),
        format!("{}", futures.iter().zip(&inputs).map(|(f, (text, ..))| format!("{text:?} → {} candidate(s) not separated, {} separated; top: {:?}", f.plural.len(), f.separated, f.plural.iter().take(3).map(|(id, lo, hi)| format!("{id} {:?} [{:.3},{:.3}]", vocabulary.surface(*id), rat_f64(lo), rat_f64(hi))).collect::<Vec<_>>())).collect::<Vec<_>>().join(" || ")));
    // 7. exact work and apparatus receipts
    verdicts.record(7, "the tower's exact semantic work is the serial composition of the layers' and the final deed's; the apparatus census is reported beside it",
        first.tower_work.dependency_span >= num_bigint::BigUint::from((tower::LAYERS * 20) as u64) && first.census_after.deed_launches - first.census_before.deed_launches == first.deed_launches,
        format!("tower work {:?} · census across the tower: deed launches {} · captured launches {} · synchronizations {} · allocations {} · ingress {} · receipt egress {} · section egress {}",
            first.tower_work.coordinates().iter().map(|(n, v)| format!("{n}={v}")).collect::<Vec<_>>(), first.census_after.deed_launches - first.census_before.deed_launches, first.census_after.captured_launches - first.census_before.captured_launches,
            first.census_after.synchronizations - first.census_before.synchronizations, first.census_after.allocations - first.census_before.allocations, first.census_after.ingress_octets - first.census_before.ingress_octets,
            first.census_after.egress_receipt_octets - first.census_before.egress_receipt_octets, first.census_after.egress_section_octets - first.census_before.egress_section_octets));
    // 8. the hidden-card control: typed refusal, no CPU fallback
    {
        let exe = std::env::current_exe().expect("this executable");
        let output = std::process::Command::new(exe).env("CUDA_VISIBLE_DEVICES", "").args(["--tokens", "1", "--hidden-card-control", "--no-source-face", "--root", &args.root]).output();
        match output {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                verdicts.record(8, "hiding the card returns a typed refusal and no semantic answer", stdout.contains("REFUSED") && !stdout.contains("THE PLURAL FUTURE") && output.status.code() == Some(3),
                    format!("subprocess with CUDA_VISIBLE_DEVICES='' exited {:?}; {}", output.status.code(), stdout.lines().filter(|l| l.contains("REFUSED") || l.contains("fallback")).collect::<Vec<_>>().join(" | ")));
            }
            Err(error) => verdicts.record(8, "hiding the card returns a typed refusal and no semantic answer", false, format!("the control could not be spawned: {error}")),
        }
    }
    // 9. the source/runtime comparison, per layer and at the boundary — the cross-chart defect slot
    let mut comparison_lines: Vec<String> = Vec::new();
    if args.source_face {
        let mut all_ok = true;
        let mut details = Vec::new();
        for (r, (text, ..)) in returns.iter().zip(&inputs) {
            let emit = format!("{}/source-face-{}-tokens-{}.tsv", args.out, r.tokens.len(), r.tokens.iter().map(|t| t.to_string()).collect::<Vec<_>>().join("-"));
            let face_clock = Instant::now();
            match source_face(&args.python, &r.tokens, &emit, args.top) {
                Ok(face) => {
                    let last = r.positions - 1;
                    let mut per_layer = Vec::new();
                    for l in &r.layers {
                        // hidden{k}: k = 0 the embedding, k = l+1 after layer l (the last entry may be the normed state; read, not assumed)
                        if let Some(rows) = face.hidden.get(&(l.layer + 1)) {
                            if let Some(row) = rows.get(last) {
                                let from = last * tower::HIDDEN;
                                let (inside, outside, worst) = defect(&l.terminal[from..from + tower::HIDDEN], grain, row);
                                let (same, total) = same_codeword(&l.terminal[from..from + tower::HIDDEN], grain, row);
                                per_layer.push((l.layer, inside, outside, worst, same, total));
                            }
                        }
                    }
                    let normed_vs_last_hidden = face.hidden.get(&tower::LAYERS).and_then(|rows| rows.get(last)).map(|row| defect(&r.final_normed[last * tower::HIDDEN..(last + 1) * tower::HIDDEN], grain, row));
                    let normed_same = face.hidden.get(&tower::LAYERS).and_then(|rows| rows.get(last)).map(|row| same_codeword(&r.final_normed[last * tower::HIDDEN..(last + 1) * tower::HIDDEN], grain, row));
                    // the boundary as codewords: the source's softcapped bf16 logit against 30·tanh(native/30) cannot be taken exactly here; the order face is the comparison
                    let codeword_agreement: Vec<String> = per_layer.iter().filter(|(l, ..)| *l == 0 || *l == 10 || *l == 20 || *l == 30 || *l == 41).map(|(l, _, _, _, same, total)| format!("layer {l}: {same}/{total}")).collect();
                    // the boundary: the source's softcapped logits against the (pre-softcap) potential section — an order-face comparison
                    let future = future_section(&r.potential, last, r.vocabulary, grain, args.top);
                    let source_top = face.logits_last.iter().enumerate().max_by(|a, b| a.1.cmp(b.1)).map(|(i, _)| i);
                    let source_top_in_plural = source_top.is_some_and(|t| future.plural.iter().any(|(id, ..)| *id == t));
                    let source_top_surface = face.surfaces.first().map(|(id, s)| format!("{id} {s:?}")).unwrap_or_default();
                    // order-face agreement over the source's top-k: are they all inside the plural section or ordered consistently by the enclosure's lower bounds?
                    let top_ids: Vec<usize> = face.surfaces.iter().map(|(id, _)| *id).collect();
                    let inside_plural = top_ids.iter().filter(|id| future.plural.iter().any(|(p, ..)| p == *id)).count();
                    let line = format!("{text:?}: per-layer (layer, inside, outside, worst gap) first {:?} · layer 41 {:?} · final normed vs hidden42 {:?} · same bf16 codeword as the source at the last position: {} · final normed {:?} · source top {source_top_surface} in the plural section {source_top_in_plural} · {inside_plural} of the source's top {} inside the plural section ({} candidates) · face in {:.1} s",
                        per_layer.iter().take(2).map(|(l, i, o, w, ..)| (*l, *i, *o, rat_f64(w))).collect::<Vec<_>>(), per_layer.last().map(|(l, i, o, w, ..)| (*l, *i, *o, rat_f64(w))), normed_vs_last_hidden.as_ref().map(|(i, o, w)| (*i, *o, rat_f64(w))), codeword_agreement.join(", "), normed_same, top_ids.len(), future.plural.len(), face_clock.elapsed().as_secs_f64());
                    println!("  comparison {line}");
                    details.push(line.clone());
                    comparison_lines.push(line);
                    all_ok &= !per_layer.is_empty();
                }
                Err(error) => {
                    all_ok = false;
                    details.push(format!("{text:?}: the source face refused: {error}"));
                }
            }
        }
        verdicts.record(9, "the source runtime's bf16 face is compared per layer and at the boundary as a cross-chart defect slot, never governing the native result", all_ok, details.join(" || "));
    } else {
        verdicts.open(9, "the source/runtime comparison", "not run (--no-source-face)");
    }
    // 10. same-output/different-law and cross-codec controls are READINGS over the inputs given
    verdicts.record(10, "same-output/different-law and cross-codec readings: inputs with bit-different final standings may share or separate their top candidate; the reading is exhibited, not authored",
        returns.len() >= 2,
        format!("{}", {
            let mut pairs = Vec::new();
            for i in 0..returns.len() {
                for j in i + 1..returns.len() {
                    let same_top = futures[i].plural.first().map(|p| p.0) == futures[j].plural.first().map(|p| p.0);
                    pairs.push(format!("({:?}, {:?}): final standings differ {} · top candidate shared {same_top}", inputs[i].0, inputs[j].0, returns[i].final_normed != returns[j].final_normed));
                }
            }
            pairs.join(" · ")
        }));
    // 11. the carrier chart: the certified enclosure of the composed tower diverges and the word refuses by name; the quotient chart is declared and its collapsed population is censused
    match &interval_control {
        Some((error, layer0, amplification, layers_carried)) if error != "carried" => {
            verdicts.record(11, "the certified interval enclosure of the composed tower diverges: the word refuses by name inside the tower, and the per-layer amplification is measured — the obstruction is returned, not narrated",
                *layers_carried >= 1 && error.contains("left the exact carrier") && rat_f64(amplification) > 1e6,
                format!("the interval chart carried {layers_carried} layer(s) and refused: {} · layer 0's widest certified enclosure {:.3e} over the entering grain 2^-{}: amplification ≈ 2^{:.1} per layer", error.chars().take(200).collect::<String>(), rat_f64(layer0), args.grain, rat_f64(amplification).log2()));
        }
        Some((_, layer0, last, layers_carried)) => {
            verdicts.record(11, "the certified interval enclosure of the composed tower diverges", false, format!("the interval chart carried all {layers_carried} layers at this grain (widest layer 0 {:.3e}, last {:.3e}): the divergence did not occur here", rat_f64(layer0), rat_f64(last)));
        }
        None => verdicts.open(11, "the certified interval enclosure's divergence", "not run (--no-interval-control)"),
    }
    let collapsed_total: u128 = first.layers.iter().map(|l| l.collapsed_width_sum).sum();
    let quotients_total: usize = first.layers.iter().map(|l| l.quotients).sum();
    verdicts.record(12, "under the declared quotient chart every layer's collapsed population is censused and exhibited — quotients named as quotient-species occurrences, the widest, summed and nonzero widths retained — and the declaration entails each quotient",
        (args.chart == tower::Chart::Interval) || (quotients_total >= tower::LAYERS * 30 && first.layers.iter().all(|l| l.quotients > 0 && l.collapsed_nonzero > 0)),
        format!("{quotients_total} quotient occurrences across the tower · collapsed widths summed {collapsed_total} grains of 2^-{} · per layer widest {:?} (layers 0, 21, 41) · the enclosure of every sealed occurrence stays resident in its own section as the per-entry residual until the passage releases",
            args.grain, [0usize, 21, 41].iter().filter_map(|i| first.layers.get(*i)).map(|l| l.collapsed_width_max).collect::<Vec<_>>()));
    // open stations
    if args.vision_control {
        match vision_projection_control(surface, readout, &mut source, &args.root, &header_regions, &content_sha256, &args.python, &args.out, grain, args.chart) {
            Ok(detail) => verdicts.record(13, "one real non-text projection crosses its typed ports on the card — the bounded portability control; the vision tower stays exterior and no recognition is claimed", detail.contains("lineage empty true"), detail),
            Err(error) => verdicts.record(13, "one real non-text projection crosses its typed ports on the card — the bounded portability control", false, error),
        }
    } else {
        verdicts.open(13, "one real non-text projection as the bounded portability control", "not run (--no-vision-control)");
    }
    // 14. coverage status for every text population after the deeds: stimulated / unbound / not crossed, and the vocabulary rows excited and unexcited
    let mut stimulated: BTreeSet<String> = BTreeSet::new();
    for layer in 0..tower::LAYERS {
        stimulated.extend(tower::populations(layer));
        stimulated.insert(tower::named(layer, "layer_scalar"));
    }
    for name in [tower::EMBED, resident_layer::PLE_EMBED, resident_layer::PLE_MODEL_PROJECTION, resident_layer::PLE_PROJECTION_NORM, tower::FINAL_NORM] {
        stimulated.insert(name.to_owned());
    }
    let mut unbound: BTreeSet<String> = BTreeSet::new();
    for layer in tower::FIRST_SHARED..tower::LAYERS {
        unbound.extend(tower::unbound_populations(layer));
    }
    let text_populations: Vec<String> = source.container.names().into_iter().filter(|n| n.starts_with("model.language_model.")).map(str::to_owned).collect();
    let crossed = text_populations.iter().filter(|n| stimulated.contains(*n)).count();
    let unbound_present = text_populations.iter().filter(|n| unbound.contains(*n)).count();
    let not_crossed: Vec<&String> = text_populations.iter().filter(|n| !stimulated.contains(*n) && !unbound.contains(*n)).collect();
    let excited_rows: BTreeSet<usize> = inputs.iter().flat_map(|(_, ids, _)| ids.iter().copied()).collect();
    let coverage_line = format!("text-tower populations {}: stimulated (caused material crossed them) {crossed} · unbound by the source realization {unbound_present} · not crossed {} {:?} · vocabulary rows excited by these inputs {} of {} ({} unexcited — a measured class, not a condensation)",
        text_populations.len(), not_crossed.len(), not_crossed.iter().take(6).collect::<Vec<_>>(), excited_rows.len(), tower::VOCABULARY, tower::VOCABULARY - excited_rows.len());
    verdicts.record(14, "every text population carries a coverage status after the deeds — stimulated, unbound by the source, or not crossed — and the vocabulary rows the inputs excited are counted against the unexcited",
        crossed + unbound_present + not_crossed.len() == text_populations.len() && not_crossed.is_empty() && excited_rows.len() < tower::VOCABULARY,
        coverage_line.clone());
    for (number, name) in [(15u32, "native rest, runtime and frozen inference"), (16, "condensation"), (17, "cultivation"), (18, "reborn dissection")] {
        verdicts.open(number, name, "a later station; this driver claims active stimulation of the text tower and nothing after it");
    }

    // ------------------------------------------------------------------------------------------
    // the deposit
    // ------------------------------------------------------------------------------------------
    let path = format!("{}/tower-{}-inputs-grain-{}-terms-{}.form", args.out, returns.len(), args.grain, args.terms);
    let mut file = std::fs::File::create(&path).expect("receipt");
    writeln!(file, "THE TOWER CONDUCTS LAYER BY LAYER AND THE FUTURE SECTION IS PLURAL — receipt").unwrap();
    writeln!(file, "root {} · grain 2^-{} · terms {} · chart {:?} · device {} · mode {:?}", args.root, args.grain, args.terms, args.chart, surface.device_name(), surface.mode()).unwrap();
    if let Some((error, layer0, amplification, layers_carried)) = &interval_control {
        writeln!(file, "interval chart control: carried {layers_carried} layer(s); {} ; layer 0 widest {layer0} ; amplification {amplification}", error.chars().take(400).collect::<String>()).unwrap();
    }
    writeln!(file, "container content sha256 {content_sha256}").unwrap();
    for (r, (text, ids, pieces)) in returns.iter().zip(&inputs) {
        writeln!(file, "input {text:?} tokens {ids:?} pieces {pieces:?}").unwrap();
        writeln!(file, "  tower work {:?}", r.tower_work.coordinates()).unwrap();
        writeln!(file, "  census before {:?}", r.census_before).unwrap();
        writeln!(file, "  census after  {:?}", r.census_after).unwrap();
        writeln!(file, "  widest charge of one deed {} · the surface's own peak {} · deed launches {} · wall {:.1} s", r.peak_charged_octets, r.peak_resident_octets, r.deed_launches, r.wall_s).unwrap();
        for l in &r.layers {
            writeln!(file, "  layer {} {:?} {:?} operations {} fronts {} material {} charged {} reconciled {} semantic {}+{} apparatus {}+{} graph {}/{} launches {} certified {} a-priori {} slack {} lineage-empty {} widest {:?} identity {} mount {:.3}s bind {:.3}s work {:?}",
                l.layer, l.species, l.role, l.operations, l.fronts, l.material_resident_octets, l.material_charged_octets, l.material_reconciled, l.semantic_bounded, l.semantic_unbounded, l.apparatus_bounded, l.apparatus_unbounded, l.graph_nodes, l.graph_edges, l.captured_launches, l.every_front_certified, l.a_priori_held, l.widest_slack, l.lineage_empty, l.widest_enclosure, l.identity_held, l.mount_wall_s, l.bind_wall_s, l.deed.coordinates()).unwrap();
        }
        let future = future_section(&r.potential, r.positions - 1, r.vocabulary, grain, args.top.max(64));
        writeln!(file, "  collapsed population per layer (quotients, Σ widths, widest, nonzero): {:?}", r.layers.iter().map(|l| (l.layer, l.quotients, l.collapsed_width_sum, l.collapsed_width_max, l.collapsed_nonzero)).collect::<Vec<_>>()).unwrap();
        writeln!(file, "  plural future section at position {}: top lower {} · {} not separated · {} separated", future.position, future.top_lower, future.plural.len(), future.separated).unwrap();
        for (id, lo, hi) in &future.plural {
            writeln!(file, "    {id} {:?} [{lo}, {hi}]", vocabulary.surface(*id)).unwrap();
        }
        writeln!(file, "  final normed standing ({} coordinates):", r.final_normed.len()).unwrap();
        for (at, (l, h)) in r.final_normed.iter().enumerate() {
            writeln!(file, "    {at} {l} {h}").unwrap();
        }
    }
    writeln!(file, "coverage: {coverage_line}").unwrap();
    writeln!(file, "source/runtime comparison:").unwrap();
    for line in &comparison_lines {
        writeln!(file, "  {line}").unwrap();
    }
    writeln!(file, "falsifiers:").unwrap();
    for line in &verdicts.lines {
        writeln!(file, "{line}").unwrap();
    }
    println!("\nreceipt: {path}");
    if verdicts.failed > 0 {
        println!("\n{} falsifier(s) FAILED", verdicts.failed);
        std::process::exit(1);
    }
    println!("\nevery attempted falsifier returned PASS; the OPEN ones are named with why");
}

#[allow(dead_code)]
fn _unused(_: EventId) {}
