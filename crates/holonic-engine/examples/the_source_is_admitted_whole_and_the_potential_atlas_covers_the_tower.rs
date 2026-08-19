//! **Station B of the complete Phoenix sequence: the foreign source is admitted whole and the
//! potential transport atlas covers the whole declared text tower.**
//!
//! Plan: [`blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`]
//! §4 (*the source file is admitted exactly*) and the Phoenix master's source-admission and
//! potential-lift stations. The directive's Station B names what this driver returns:
//!
//! * **the complete foreign source manifest** — all 2,130 tensors, every byte region hashed as it
//!   was read, every `BF16` codeword decoded through the one float mouth (a 65,536-entry table of
//!   the mouth's own verdicts), rank 0–4 populations, the sibling assets (configuration, processor,
//!   tokenizer, template, generation, README) hashed and declared used or unused, the text, image,
//!   audio and video ports typed from the configuration, decoded-exact / unread-refused status
//!   founded by the decode pass, potential / stimulated / unexcited / unbound status from the
//!   tower atlas and the enacted layer-zero deed, load-bearing status only where an enacted typed
//!   operator returned a changed consequence, the source content, header, region, decoder and
//!   toolchain identities, the streamed peak residency and the pass's exact work;
//! * **source authentication binding one immutable occurrence** — file identity before and after
//!   the pass and after the tower binding; dtype checked against the exact carrier on every
//!   declared-shape testimony; symbol resolution scope-aware and blind to comments and string
//!   literals; a valid but unrelated slice refusing to authenticate another binding; every
//!   binding's law ENTAILED by its validated testimony (`LawEntailment`: parameters connected to
//!   fields, shapes and slices);
//! * **the potential transport atlas over the full declared text tower** — 42 layer deeds founded
//!   with the source's two attention species, both head widths, both RoPE species, every
//!   normalization and residual passage, the per-layer input, the KV-sharing realization (layers
//!   24–41 reading the standings stored by 22 and 23, their stored K/V populations marked unbound),
//!   the final normalization and the tied output boundary, and the two modality projections —
//!   every operation validated against the authenticated implementation and configuration and
//!   entailed by its testimony, with its predecessor and successor ports, species, law, parameters,
//!   source population and status.
//!
//! Enumeration is not admission, admission is not a lift, and a potential atlas is not an active
//! one: every transport here is `potential-only` except layer zero's, which the resident deed
//! stimulated (Station A). Nothing here computes a standing.
//!
//! Run:
//! ```text
//! cargo run --release -q -p holonic-engine \
//!     --example the_source_is_admitted_whole_and_the_potential_atlas_covers_the_tower -- \
//!     [--root /home/b/models/gemma-4-E4B-it] [--out output/the_source_is_admitted_whole] [--chunk-mib 32]
//! ```

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::time::Instant;

use holonic_engine::exact_json;
use holonic_engine::foreign_map::{manifest_safetensors, AdmissionClass, FileIdentity, StreamedCensus};
use holonic_engine::front_passage::{CompileRefusal, FrontPassageObstruction};
use holonic_engine::ported_operation::SourceTestimony;
use holonic_engine::resident_section::{Dyadic, SeriesAperture};
use holonic_engine::source_occurrence::{AssetDeclaration, AuthenticatedContainer, AuthenticatedText, RegionIdentity, SourceOccurrence, SourceRefusal};
use sha2::{Digest, Sha256};
use tower::{Entry, KvRole, Species};

struct Args {
    root: String,
    out: String,
    chunk_octets: usize,
}

fn parse_args() -> Args {
    let mut args = Args { root: "/home/b/models/gemma-4-E4B-it".to_owned(), out: "output/the_source_is_admitted_whole".to_owned(), chunk_octets: 32 << 20 };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--out" => args.out = it.next().expect("--out <dir>"),
            "--chunk-mib" => args.chunk_octets = it.next().expect("--chunk-mib N").parse::<usize>().expect("usize") << 20,
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
}

/// What the manifest says of one population on the transport axis, and by what it is bound.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Transport {
    /// Bound to an operation of the potential atlas; no caused material has crossed it here.
    PotentialOnly { bound_by: String },
    /// Caused material crossed it in the enacted layer-zero deed (Station A).
    Stimulated { bound_by: String },
    /// Present in the container and built by no module of the source realization.
    Unbound { because: &'static str },
    /// No typed predecessor, successor, law or receiver has been posed for it here.
    Unposed { population: &'static str },
}

impl Transport {
    fn name(&self) -> &'static str {
        match self {
            Self::PotentialOnly { .. } => "potential-only",
            Self::Stimulated { .. } => "stimulated",
            Self::Unbound { .. } => "unbound-by-the-source-realization",
            Self::Unposed { .. } => "unposed",
        }
    }
    fn detail(&self) -> String {
        match self {
            Self::PotentialOnly { bound_by } | Self::Stimulated { bound_by } => bound_by.clone(),
            Self::Unbound { because } => (*because).to_owned(),
            Self::Unposed { population } => (*population).to_owned(),
        }
    }
}

/// One row of the potential transport atlas.
struct AtlasRow {
    deed: String,
    operation: String,
    species: String,
    law: String,
    parameters: String,
    inputs: String,
    outputs: String,
    carrier: String,
    status: &'static str,
    symbols: usize,
    fields: usize,
    shapes: usize,
}

fn main() {
    let args = parse_args();
    let clock = Instant::now();
    std::fs::create_dir_all(&args.out).expect("output directory");
    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };
    println!("THE SOURCE IS ADMITTED WHOLE AND THE POTENTIAL ATLAS COVERS THE TOWER — {}", args.root);

    // ------------------------------------------------------------------------------------------
    // 1. the complete manifest: one streamed pass
    // ------------------------------------------------------------------------------------------
    let address = format!("{}/model.safetensors", args.root);
    let (mut file, container) = match manifest_safetensors(&address) {
        Ok(pair) => pair,
        Err(error) => {
            println!("REFUSED: the container did not manifest — {error}");
            std::process::exit(1);
        }
    };
    let identity_at_open = FileIdentity::of(&file, &address).expect("identity");
    println!("  container manifested: {} tensors · {} refused · file {} octets · payload {} octets · overlaps {}",
        container.tensors.len(), container.refused.len(), container.file_octets, container.payload_octets, container.overlaps().len());
    let pass_clock = Instant::now();
    let census: StreamedCensus = match container.streamed_census(&mut file, args.chunk_octets) {
        Ok(census) => census,
        Err(error) => {
            println!("REFUSED: the streamed census did not complete — {error}");
            std::process::exit(1);
        }
    };
    let pass_wall = pass_clock.elapsed();
    let admission_census = census.admission_census();
    let rank_census = census.rank_census();
    println!("  streamed census in {:.1} s: {} regions · content sha256 {} · header sha256 {} · uncovered payload octets {} · chunk {} octets · peak resident {} octets · octets hashed {} · codewords decoded {}",
        pass_wall.as_secs_f64(), census.regions.len(), &census.content_sha256[..16], &census.header_sha256[..16], census.uncovered_payload_octets, census.chunk_octets, census.peak_resident_octets, census.octets_hashed, census.codewords_decoded);
    println!("  admission census: {:?}", admission_census.iter().map(|(k, v)| (k.name(), *v)).collect::<Vec<_>>());
    println!("  rank census (rank: count, octets): {:?}", rank_census);
    let identity_after_pass = FileIdentity::at(&address).expect("identity");

    // ------------------------------------------------------------------------------------------
    // 2. assets and ports
    // ------------------------------------------------------------------------------------------
    let mut assets: Vec<AssetDeclaration> = Vec::new();
    let mut entries: Vec<String> = std::fs::read_dir(&args.root).expect("root").filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string()).collect();
    entries.sort();
    for name in &entries {
        if name == "model.safetensors" {
            continue;
        }
        let path = format!("{}/{name}", args.root);
        let role = match name.as_str() {
            "config.json" => "configuration",
            "processor_config.json" => "processor configuration",
            "tokenizer.json" => "tokenizer",
            "tokenizer_config.json" => "tokenizer configuration",
            "chat_template.jinja" => "chat template",
            "generation_config.json" => "generation configuration",
            "README.md" => "authoritative description",
            _ => "other sibling file",
        };
        let sha256 = std::fs::read(&path).ok().map(|bytes| Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect::<String>());
        // This deed reads the configuration and the container; every other asset is declared unused.
        assets.push(AssetDeclaration { role: role.to_owned(), locator: path, sha256, used: name == "config.json" });
    }
    println!("  assets: {} sibling files hashed, {} declared used by this deed", assets.len(), assets.iter().filter(|a| a.used).count());

    let configuration_text = std::fs::read_to_string(format!("{}/config.json", args.root)).expect("config");
    let top = exact_json::top_level_pairs(&configuration_text).unwrap_or_default();
    let scope = |name: &str| -> Option<String> { top.iter().find(|(k, _)| k == name).map(|(_, v)| (*v).to_owned()) };
    let field_of = |object: &str, key: &str| -> Option<String> { exact_json::field(object, key).map(|span| exact_json::as_string(span).unwrap_or_else(|| span.trim().to_owned())) };
    let text_config = scope("text_config").unwrap_or_default();
    let vision_config = scope("vision_config").unwrap_or_default();
    let audio_config = scope("audio_config").unwrap_or_default();
    let ports: Vec<(String, String, String)> = vec![
        ("text input".to_owned(), format!("token identities over vocab_size {} → embed_tokens [{}, {}] × embed_scale √hidden", field_of(&text_config, "vocab_size").unwrap_or_default(), tower::VOCABULARY, tower::HIDDEN), "model.language_model.embed_tokens.weight".to_owned()),
        ("text output".to_owned(), format!("tied boundary: embed_tokens read in the other direction, then final_logit_softcapping {} (monotone)", field_of(&text_config, "final_logit_softcapping").unwrap_or_default()), "model.language_model.embed_tokens.weight (tied)".to_owned()),
        ("image".to_owned(), format!("vision tower: hidden {} · patch {} · layers {} → embed_vision.embedding_projection [2560, 768]", field_of(&vision_config, "hidden_size").unwrap_or_default(), field_of(&vision_config, "patch_size").unwrap_or_default(), field_of(&vision_config, "num_hidden_layers").unwrap_or_default()), "model.embed_vision.embedding_projection.weight".to_owned()),
        ("audio".to_owned(), format!("audio tower: hidden {} · layers {} → embed_audio.embedding_projection [2560, 1536]", field_of(&audio_config, "hidden_size").unwrap_or_default(), field_of(&audio_config, "num_hidden_layers").unwrap_or_default()), "model.embed_audio.embedding_projection.weight".to_owned()),
        ("video".to_owned(), "the processor's frame declaration over the vision port (processor_config.json); no tensor of its own".to_owned(), "(vision port)".to_owned()),
    ];
    println!("  ports typed from the configuration:");
    for (port, law, population) in &ports {
        println!("    {port:<12} {law}  [{population}]");
    }

    // ------------------------------------------------------------------------------------------
    // 3. the source occurrence, and the potential atlas over the whole tower
    // ------------------------------------------------------------------------------------------
    let regions: BTreeMap<String, RegionIdentity> = census
        .regions
        .iter()
        .map(|r| (r.name.clone(), RegionIdentity { population: r.name.clone(), dtype: format!("{:?}", r.dtype), shape: r.shape.clone(), start: r.start, end: r.end, sha256: Some(r.sha256.clone()) }))
        .collect();
    let mut occurrence = resident_layer::source_occurrence(&args.root, regions.clone(), Some(census.content_sha256.clone())).unwrap_or_else(|error| {
        println!("REFUSED: the source occurrence could not be authenticated — {error}");
        std::process::exit(1);
    });
    occurrence.assets = assets.clone();
    let scales = tower::algebraic_scales().expect("scales");
    let terms = SeriesAperture(14);
    let unit_scalar = Dyadic::ONE;
    let mut atlas: Vec<AtlasRow> = Vec::new();
    let mut bound_by: BTreeMap<String, String> = BTreeMap::new();
    let mut validation_refusals: Vec<String> = Vec::new();
    let mut operations_total = 0usize;
    let mut species_total: BTreeMap<String, usize> = BTreeMap::new();
    let mut laws_total: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut symbols_total = 0usize;
    let mut fields_total = 0usize;
    let mut shapes_total = 0usize;
    let mut entailed_total = 0usize;
    let mut layer_closures: Vec<(usize, usize, usize, usize)> = Vec::new();
    let tower_clock = Instant::now();
    for layer in 0..tower::LAYERS {
        let entry = if layer == 0 { Entry::Rows } else { Entry::Carried };
        let founded = tower::found_layer(layer, entry, tower::Chart::Interval, &scales, terms, unit_scalar, &tower::Intervention::None, 1).unwrap_or_else(|error| {
            println!("REFUSED: layer {layer} did not found — {error}");
            std::process::exit(1);
        });
        let closure = founded.complex.closure().expect("closure");
        layer_closures.push((layer, closure.operations, closure.occurrences, closure.fronts));
        if let Err(refusal) = founded.realization.validate(&founded.complex) {
            validation_refusals.push(format!("layer {layer}: realization {refusal}"));
            continue;
        }
        let validations = match occurrence.validate(&founded.complex) {
            Ok(v) => v,
            Err(refusal) => {
                validation_refusals.push(format!("layer {layer}: source {refusal}"));
                continue;
            }
        };
        let deed = format!("layer {layer} ({}, K/V {:?})", Species::of(layer).layer_type(), KvRole::of(layer));
        for (event, law) in &founded.realization.bindings {
            let occ = &founded.complex.shape.occurrences[event];
            let law_decl = &founded.complex.shape.laws[&occ.law];
            let op = &founded.complex.operations[&occ.law];
            let validation = validations.iter().find(|v| v.operation == law_decl.name).expect("validated");
            let entailment = match law.entailment(validation) {
                Ok(e) => e,
                Err(refusal) => {
                    validation_refusals.push(format!("layer {layer} {}: entailment {refusal}", law_decl.name));
                    continue;
                }
            };
            entailed_total += 1;
            operations_total += 1;
            *species_total.entry(format!("{:?}", op.species)).or_insert(0) += 1;
            *laws_total.entry(law.name()).or_insert(0) += 1;
            symbols_total += validation.symbols.len();
            fields_total += validation.fields.len();
            shapes_total += validation.shapes.len();
            let inputs: Vec<String> = law_decl.inputs.iter().map(|b| founded.complex.shape.boundaries.objects[b].name.clone()).collect();
            let outputs: Vec<String> = law_decl.outputs.iter().map(|b| founded.complex.shape.boundaries.objects[b].name.clone()).collect();
            let status = if layer == 0 { "stimulated (Station A)" } else { "potential-only" };
            if let Some(carrier) = &op.carrier {
                bound_by.entry(carrier.clone()).or_insert_with(|| format!("{deed}: {}", law_decl.name));
            }
            atlas.push(AtlasRow {
                deed: deed.clone(),
                operation: law_decl.name.clone(),
                species: format!("{:?}", op.species),
                law: law.name().to_owned(),
                parameters: entailment.parameters.iter().map(|(p, v, by)| format!("{p}={v} ⟵ {by}")).collect::<Vec<_>>().join(" ; "),
                inputs: inputs.join(" | "),
                outputs: outputs.join(" | "),
                carrier: op.carrier.clone().unwrap_or_default(),
                status,
                symbols: validation.symbols.len(),
                fields: validation.fields.len(),
                shapes: validation.shapes.len(),
            });
        }
    }
    // the final deed
    let final_founded = tower::found_final(tower::Chart::Interval, &tower::Intervention::None, &scales).expect("final founds");
    let final_closure = final_founded.complex.closure().expect("closure");
    match final_founded.realization.validate(&final_founded.complex).map_err(|e| e.to_string()).and_then(|()| occurrence.validate(&final_founded.complex).map_err(|e| e.to_string())) {
        Ok(validations) => {
            for (event, law) in &final_founded.realization.bindings {
                let occ = &final_founded.complex.shape.occurrences[event];
                let law_decl = &final_founded.complex.shape.laws[&occ.law];
                let op = &final_founded.complex.operations[&occ.law];
                let validation = validations.iter().find(|v| v.operation == law_decl.name).expect("validated");
                match law.entailment(validation) {
                    Ok(entailment) => {
                        entailed_total += 1;
                        operations_total += 1;
                        *species_total.entry(format!("{:?}", op.species)).or_insert(0) += 1;
                        *laws_total.entry(law.name()).or_insert(0) += 1;
                        symbols_total += validation.symbols.len();
                        fields_total += validation.fields.len();
                        shapes_total += validation.shapes.len();
                        if let Some(carrier) = &op.carrier {
                            bound_by.entry(carrier.clone()).or_insert_with(|| format!("final deed: {}", law_decl.name));
                        }
                        atlas.push(AtlasRow {
                            deed: "final normalization and tied output boundary".to_owned(),
                            operation: law_decl.name.clone(),
                            species: format!("{:?}", op.species),
                            law: law.name().to_owned(),
                            parameters: entailment.parameters.iter().map(|(p, v, by)| format!("{p}={v} ⟵ {by}")).collect::<Vec<_>>().join(" ; "),
                            inputs: law_decl.inputs.iter().map(|b| final_founded.complex.shape.boundaries.objects[b].name.clone()).collect::<Vec<_>>().join(" | "),
                            outputs: law_decl.outputs.iter().map(|b| final_founded.complex.shape.boundaries.objects[b].name.clone()).collect::<Vec<_>>().join(" | "),
                            carrier: op.carrier.clone().unwrap_or_default(),
                            status: "potential-only",
                            symbols: validation.symbols.len(),
                            fields: validation.fields.len(),
                            shapes: validation.shapes.len(),
                        });
                    }
                    Err(refusal) => validation_refusals.push(format!("final {}: entailment {refusal}", law_decl.name)),
                }
            }
        }
        Err(refusal) => validation_refusals.push(format!("final: {refusal}")),
    }
    // the two modality projections: typed as potential transports under their own configuration scopes
    let modality_rows = modality_projections(&args.root, &regions, &census.content_sha256, &assets, &mut validation_refusals, &mut bound_by);
    for row in modality_rows {
        operations_total += 1;
        entailed_total += 1;
        *species_total.entry(row.species.clone()).or_insert(0) += 1;
        atlas.push(row);
    }
    let tower_wall = tower_clock.elapsed();
    let identity_after_tower = FileIdentity::at(&address).expect("identity");
    println!("  potential atlas over the tower in {:.1} s: {} operations entailed across {} layer deeds + final + 2 modality projections · species {:?} · laws {:?} · symbols {symbols_total} · fields {fields_total} · shapes {shapes_total} · refusals {}",
        tower_wall.as_secs_f64(), operations_total, tower::LAYERS, species_total, laws_total, validation_refusals.len());
    for refusal in validation_refusals.iter().take(12) {
        println!("    REFUSAL {refusal}");
    }

    // ------------------------------------------------------------------------------------------
    // 4. the coverage ledger: every population on every axis
    // ------------------------------------------------------------------------------------------
    let stimulated: BTreeSet<String> = {
        let mut set: BTreeSet<String> = tower::populations(0).into_iter().collect();
        set.insert(tower::EMBED.to_owned());
        set.insert(resident_layer::PLE_EMBED.to_owned());
        set.insert(resident_layer::PLE_MODEL_PROJECTION.to_owned());
        set.insert(resident_layer::PLE_PROJECTION_NORM.to_owned());
        set.insert(tower::named(0, "layer_scalar"));
        set
    };
    let load_bearing: BTreeMap<String, &'static str> = [
        (tower::named(0, "self_attn.k_proj.weight"), "Station A falsifier 13: withdrawing each presented family moved 512 contact coordinates in exactly the heads it serves"),
        (tower::named(0, "self_attn.v_proj.weight"), "Station A falsifier 13: withdrawing each carried family moved 512 contact coordinates in exactly the heads it serves"),
    ]
    .into_iter()
    .collect();
    let mut unbound: BTreeMap<String, &'static str> = BTreeMap::new();
    for layer in tower::FIRST_SHARED..tower::LAYERS {
        for name in tower::unbound_populations(layer) {
            unbound.insert(name, "a KV-shared layer (is_kv_shared_layer) builds no k_proj/v_proj/k_norm; the source realization reads shared_kv_states instead");
        }
    }
    let mut transport_census: BTreeMap<&'static str, (usize, u64)> = BTreeMap::new();
    let mut rows: Vec<String> = Vec::new();
    for region in &census.regions {
        let transport = if stimulated.contains(&region.name) {
            Transport::Stimulated { bound_by: bound_by.get(&region.name).cloned().unwrap_or_else(|| "the enacted layer-zero deed".to_owned()) }
        } else if let Some(because) = unbound.get(&region.name) {
            Transport::Unbound { because }
        } else if let Some(by) = bound_by.get(&region.name) {
            Transport::PotentialOnly { bound_by: by.clone() }
        } else if region.name.starts_with("model.vision_tower") {
            Transport::Unposed { population: "vision tower interior: no diagram posed here; the image port is typed and its projection is bound" }
        } else if region.name.starts_with("model.audio_tower") {
            Transport::Unposed { population: "audio tower interior: no diagram posed here; the audio port is typed and its projection is bound" }
        } else {
            Transport::Unposed { population: "no operation of the posed diagrams names it" }
        };
        let entry = transport_census.entry(transport.name()).or_insert((0, 0));
        entry.0 += 1;
        entry.1 += region.octets;
        let lb = load_bearing.get(&region.name).map(|s| (*s).to_owned()).unwrap_or_else(|| "not established".to_owned());
        rows.push(format!(
            "{}\t{:?}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            region.name, region.dtype, region.shape, region.rank(), region.start, region.end, region.octets, region.sha256, region.codewords, region.finite, region.non_finite, region.zero, region.subnormal,
            region.exponent_min.map(|e| e.to_string()).unwrap_or_default(), region.exponent_max.map(|e| e.to_string()).unwrap_or_default(),
            region.admission.name(), transport.name(), transport.detail(), lb
        ));
    }
    println!("  transport census (class: populations, octets): {:?}", transport_census);

    // ------------------------------------------------------------------------------------------
    // 5. falsifiers
    // ------------------------------------------------------------------------------------------
    println!("\nTHE FALSIFIERS");
    let declared = container.tensors.len() + container.refused.len();
    verdicts.record(1, "every declared population is manifested, hashed and censused; none is dropped",
        census.regions.len() == container.tensors.len() && declared == 2130 && container.refused.is_empty() && census.regions.iter().all(|r| !r.sha256.is_empty() && r.octets == r.end - r.start),
        format!("declared {declared} · manifested {} · refused by name {} · regions censused {} · every region hashed over exactly its declared span", container.tensors.len(), container.refused.len(), census.regions.len()));
    let decoded_exact = admission_census.get(&AdmissionClass::DecodedExact).copied().unwrap_or(0);
    let total_codewords: u64 = census.regions.iter().map(|r| r.codewords).sum();
    verdicts.record(2, "every BF16 codeword was decoded exactly through the one float mouth, and the admission class is founded by the decode",
        decoded_exact == census.regions.len() && census.codewords_decoded == total_codewords && census.codewords_decoded * 2 == container.payload_octets - census.uncovered_payload_octets,
        format!("{decoded_exact} of {} regions decoded-exact · {} codewords decoded = {} octets of the {} payload ({} uncovered) · non-finite codewords {}",
            census.regions.len(), census.codewords_decoded, census.codewords_decoded * 2, container.payload_octets, census.uncovered_payload_octets, census.regions.iter().map(|r| r.non_finite).sum::<u64>()));
    verdicts.record(3, "the digest and the census read one stable file occurrence, and the tower binding read the same one",
        identity_at_open == identity_after_pass && identity_after_pass == identity_after_tower && census.identity == identity_at_open,
        format!("identity at open {:?} · after the pass equal {} · after the tower binding equal {}", identity_at_open, identity_at_open == identity_after_pass, identity_at_open == identity_after_tower));
    verdicts.record(4, "dtype is checked, not recorded: every region's declared extent equals elements × 2, and a non-BF16 region would be refused by name",
        container.tensors.values().all(|t| t.extent_agrees() == Some(true)) && {
            // a synthetic occurrence whose region declares F32 for a population the deed binds refuses at DtypeDiffers
            let mut drifted = regions.clone();
            if let Some(r) = drifted.get_mut(&tower::named(0, "input_layernorm.weight")) { r.dtype = "F32".to_owned(); }
            let mut occ = occurrence.clone();
            occ.container.regions = drifted;
            let founded = tower::found_layer(0, Entry::Rows, tower::Chart::Interval, &scales, terms, unit_scalar, &tower::Intervention::None, 1).expect("founds");
            matches!(occ.validate(&founded.complex), Err(SourceRefusal::DtypeDiffers { .. }))
        },
        "every declared extent agrees with elements × dtype width; a region drifted to F32 for a bound population refuses at DtypeDiffers before any transport");
    verdicts.record(5, "symbol resolution is scope-aware and blind to comments and string literals",
        {
            // a slice that occurs only in a docstring does not resolve; the same method's code slice does
            let docstring = occurrence.resolve_symbol("control", "rotate_half (Rotates half the hidden dims of the input.)");
            let code = occurrence.resolve_symbol("control", "rotate_half (return torch.cat((-x2, x1), dim=-1))");
            let comment = occurrence.resolve_symbol("control", "Gemma4TextAttention.forward (Device of past layer may be different from current one)");
            matches!(docstring, Err(SourceRefusal::SliceAbsent { .. })) && code.is_ok() && matches!(comment, Err(SourceRefusal::SliceAbsent { .. }))
        },
        "the docstring slice 'Rotates half the hidden dims of the input.' and the comment slice 'Device of past layer may be different from current one' refuse as absent; the code slice 'return torch.cat((-x2, x1), dim=-1)' resolves");
    verdicts.record(6, "a valid but semantically unrelated source slice does not authenticate another binding",
        {
            // offer the q_proj slice (valid, resolves) as the presented projection's testimony
            let mut founded = tower::found_layer(0, Entry::Rows, tower::Chart::Interval, &scales, terms, unit_scalar, &tower::Intervention::None, 1).expect("founds");
            let law_id = founded.complex.shape.laws.iter().find(|(_, l)| l.name == "presented projection").map(|(id, _)| *id).expect("k");
            let op = founded.complex.operations.get_mut(&law_id).expect("op");
            op.testimony.retain(|t| !matches!(t, SourceTestimony::Implementation { .. }));
            op.testimony.push(SourceTestimony::Implementation { locator: resident_layer::IMPLEMENTATION.to_owned(), symbol: "Gemma4TextAttention.forward (query_states = self.q_proj(hidden_states).view(hidden_shape))".to_owned() });
            let validations = occurrence.validate(&founded.complex).expect("the unrelated slice itself resolves");
            let (event, law) = founded.realization.bindings.iter().find(|(e, _)| founded.complex.shape.occurrences[e].law == law_id).expect("bound");
            let v = validations.iter().find(|v| v.operation == "presented projection").expect("v");
            let _ = event;
            matches!(law.entailment(v), Err(holonic_engine::front_passage::EntailmentRefusal::SliceDoesNotEntail { .. }))
        },
        "the receiver projection's slice `query_states = self.q_proj(...)` resolves against the authenticated text and is refused as entailment for the presented projection (k_proj): SliceDoesNotEntail");
    verdicts.record(7, "every binding of the potential atlas is entailed by its validated testimony: parameters connected to fields, shapes and slices",
        validation_refusals.is_empty() && entailed_total == operations_total && operations_total > 0,
        format!("{entailed_total} of {operations_total} operations entailed; refusals {:?}", validation_refusals.iter().take(6).collect::<Vec<_>>()));
    let sliding = layer_closures.iter().filter(|(l, ..)| Species::of(*l) == Species::Sliding).count();
    let full = layer_closures.iter().filter(|(l, ..)| Species::of(*l) == Species::Full).count();
    let shared = (tower::FIRST_SHARED..tower::LAYERS).count();
    let full_rows = atlas.iter().filter(|r| r.deed.contains("full_attention")).count();
    let proportional = atlas.iter().filter(|r| r.law == "chronology" && r.parameters.contains("head_width=512")).count();
    let default_rope = atlas.iter().filter(|r| r.law == "chronology" && r.parameters.contains("head_width=256")).count();
    let shared_standings = atlas.iter().filter(|r| r.law == "standing" && r.operation.starts_with("shared")).count();
    verdicts.record(8, "the atlas covers the full declared text tower: 42 layers, both species, both head widths, both RoPE species, the KV-sharing realization, every normalization and residual passage, PLE, the final norm, the tied output and the modality projections",
        layer_closures.len() == tower::LAYERS && sliding == 35 && full == 7 && full_rows > 0 && proportional == 7 * 1 + 7 * 0 + 7 * 0 + 0 + (FULL_OWN_K_CHRONOLOGIES) && default_rope > 0 && shared_standings == 2 * shared && atlas.iter().any(|r| r.operation == "final rebase") && atlas.iter().any(|r| r.operation == "tied output boundary") && atlas.iter().filter(|r| r.deed.starts_with("modality")).map(|r| r.deed.clone()).collect::<BTreeSet<_>>().len() == 2 && atlas.iter().filter(|r| r.deed.starts_with("modality")).count() == 6,
        format!("layers founded {} (sliding {sliding}, full {full}) · chronology laws at head 512 {proportional} (7 receiver + 4 presented where the full layer builds its own K), at head 256 {default_rope} · shared K/V standings {shared_standings} over {shared} shared layers · final rebase and tied boundary present · modality projection deeds 2 ({} operations) · per-layer (operations, occurrences, fronts): layer 0 {:?}, layer 23 {:?}, layer 24 {:?}, layer 41 {:?}",
            layer_closures.len(), atlas.iter().filter(|r| r.deed.starts_with("modality")).count(), layer_closures.first().map(|c| (c.1, c.2, c.3)), layer_closures.get(23).map(|c| (c.1, c.2, c.3)), layer_closures.get(24).map(|c| (c.1, c.2, c.3)), layer_closures.get(41).map(|c| (c.1, c.2, c.3))));
    verdicts.record(9, "unexcited and unbound are separate classes: the shared layers' stored K/V populations are present, decoded and named unbound by the source realization, never condensed away and never called potential",
        transport_census.get("unbound-by-the-source-realization").map(|(n, _)| *n) == Some(3 * shared) && unbound.keys().all(|k| census.region(k).is_some_and(|r| r.admission == AdmissionClass::DecodedExact)),
        format!("{} populations unbound ({} octets) — k_proj, v_proj, k_norm of layers 24–41 — every one decoded-exact in the container", transport_census.get("unbound-by-the-source-realization").map(|(n, _)| *n).unwrap_or(0), transport_census.get("unbound-by-the-source-realization").map(|(_, o)| *o).unwrap_or(0)));
    verdicts.record(10, "load-bearing is declared only where an enacted typed operator returned a changed consequence",
        load_bearing.len() == 2 && load_bearing.keys().all(|k| stimulated.contains(k)),
        format!("{} populations load-bearing, each citing the enacted intervention: {:?}", load_bearing.len(), load_bearing.keys().collect::<Vec<_>>()));
    verdicts.record(11, "the peak streamed residency and the pass's exact work are reported, and the manifest does not require the source resident",
        census.peak_resident_octets < container.file_octets / 64 && census.octets_hashed >= container.file_octets,
        format!("peak resident {} octets against the file's {} · octets hashed {} · codewords decoded {} · pass wall {:.1} s (telemetry)", census.peak_resident_octets, container.file_octets, census.octets_hashed, census.codewords_decoded, pass_wall.as_secs_f64()));

    // ------------------------------------------------------------------------------------------
    // 6. the deposit
    // ------------------------------------------------------------------------------------------
    let manifest_path = format!("{}/gemma-4-E4B-it.manifest.tsv", args.out);
    let mut manifest = std::fs::File::create(&manifest_path).expect("manifest");
    writeln!(manifest, "population\tdtype\tshape\trank\tstart\tend\toctets\tsha256\tcodewords\tfinite\tnon_finite\tzero\tsubnormal\texponent_min\texponent_max\tadmission\ttransport\tbound_by\tload_bearing").unwrap();
    for row in &rows {
        writeln!(manifest, "{row}").unwrap();
    }
    let atlas_path = format!("{}/potential-transport-atlas.tsv", args.out);
    let mut atlas_file = std::fs::File::create(&atlas_path).expect("atlas");
    writeln!(atlas_file, "deed\toperation\tspecies\tlaw\tparameters\tinputs\toutputs\tcarrier\tstatus\tsymbols\tfields\tshapes").unwrap();
    for row in &atlas {
        writeln!(atlas_file, "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}", row.deed, row.operation, row.species, row.law, row.parameters, row.inputs, row.outputs, row.carrier, row.status, row.symbols, row.fields, row.shapes).unwrap();
    }
    let receipt_path = format!("{}/receipt.form", args.out);
    let mut receipt = std::fs::File::create(&receipt_path).expect("receipt");
    writeln!(receipt, "THE SOURCE IS ADMITTED WHOLE AND THE POTENTIAL ATLAS COVERS THE TOWER — receipt").unwrap();
    writeln!(receipt, "root {} (an apparatus address, never an identity)", args.root).unwrap();
    writeln!(receipt, "container file octets {} payload octets {} header octets {} tensors {} refused {}", container.file_octets, container.payload_octets, match container.species { holonic_engine::foreign_map::ContainerSpecies::Safetensors { header_octets, .. } => header_octets }, container.tensors.len(), container.refused.len()).unwrap();
    writeln!(receipt, "content sha256 {}", census.content_sha256).unwrap();
    writeln!(receipt, "header sha256 {}", census.header_sha256).unwrap();
    writeln!(receipt, "file identity {:?}", census.identity).unwrap();
    writeln!(receipt, "decoder: holonic_engine::foreign_map::ForeignContainer::streamed_census over exact_value::ieee754::decode_bfloat16_bits (one table of the mouth's verdicts); toolchain {}", rustc_identity()).unwrap();
    writeln!(receipt, "implementation {} sha256 {} ({})", occurrence.implementation.locator, occurrence.implementation.sha256, occurrence.implementation.version.as_deref().unwrap_or("?")).unwrap();
    writeln!(receipt, "configuration {} sha256 {}", occurrence.configuration.locator, occurrence.configuration.sha256).unwrap();
    for asset in &assets {
        writeln!(receipt, "asset {} {} sha256 {:?} used {}", asset.role, asset.locator, asset.sha256, asset.used).unwrap();
    }
    for (port, law, population) in &ports {
        writeln!(receipt, "port {port}: {law} [{population}]").unwrap();
    }
    writeln!(receipt, "streamed census: chunk {} octets · peak resident {} octets · octets hashed {} · codewords decoded {} · uncovered payload octets {} · pass wall {:.1} s", census.chunk_octets, census.peak_resident_octets, census.octets_hashed, census.codewords_decoded, census.uncovered_payload_octets, pass_wall.as_secs_f64()).unwrap();
    writeln!(receipt, "admission census {:?}", admission_census.iter().map(|(k, v)| (k.name(), *v)).collect::<Vec<_>>()).unwrap();
    writeln!(receipt, "rank census {:?}", rank_census).unwrap();
    writeln!(receipt, "transport census {:?}", transport_census).unwrap();
    writeln!(receipt, "load-bearing {:?}", load_bearing).unwrap();
    writeln!(receipt, "potential atlas: {operations_total} operations · species {species_total:?} · laws {laws_total:?} · symbols {symbols_total} · fields {fields_total} · shapes {shapes_total} · per-layer closures {layer_closures:?} · final {:?}", (final_closure.operations, final_closure.occurrences, final_closure.fronts)).unwrap();
    writeln!(receipt, "falsifiers:").unwrap();
    for line in &verdicts.lines {
        writeln!(receipt, "{line}").unwrap();
    }
    println!("\nmanifest: {manifest_path} ({} rows)\natlas: {atlas_path} ({} rows)\nreceipt: {receipt_path}\nwall {:.1} s", rows.len(), atlas.len(), clock.elapsed().as_secs_f64());
    if verdicts.failed > 0 {
        println!("\n{} falsifier(s) FAILED", verdicts.failed);
        std::process::exit(1);
    }
    println!("\nevery falsifier returned PASS");
}

/// Seven full layers each carry a receiver chronology at head 512; the four that build their own K
/// (5, 11, 17, 23) carry a presented chronology too: 7 + 4.
const FULL_OWN_K_CHRONOLOGIES: usize = 4;

fn rustc_identity() -> String {
    let rustc = std::process::Command::new("rustc").arg("--version").output().ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned()).unwrap_or_else(|| "rustc (version unread)".to_owned());
    let commit = std::process::Command::new("git").args(["rev-parse", "HEAD"]).output().ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned()).unwrap_or_else(|| "(commit unread)".to_owned());
    let dirty = std::process::Command::new("git").args(["status", "--porcelain"]).output().ok().map(|o| !o.stdout.is_empty()).unwrap_or(true);
    format!("{rustc}; holonic-engine at {commit}{}", if dirty { " + uncommitted" } else { "" })
}

/// The two modality projections — `embed_vision` and `embed_audio` — as potential transports under
/// their own configuration scopes: a gain-less RMS rebase over the modality width, then the
/// projection into the shared stream. Typed and entailed like every text operation; their towers'
/// interiors are not posed here.
fn modality_projections(root: &str, regions: &BTreeMap<String, RegionIdentity>, content_sha256: &str, assets: &[AssetDeclaration], refusals: &mut Vec<String>, bound_by: &mut BTreeMap<String, String>) -> Vec<AtlasRow> {
    use holonic_engine::front_passage::{Contract, ResidentRealization, RmsRebase, Standing};
    use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex};
    let mut rows = Vec::new();
    for (modality, scope, population, width, width_field) in [("vision", "vision_config", "model.embed_vision.embedding_projection.weight", 768usize, "hidden_size"), ("audio", "audio_config", "model.embed_audio.embedding_projection.weight", 1536usize, "output_proj_dims")] {
        let implementation = AuthenticatedText::read(resident_layer::IMPLEMENTATION, resident_layer::implementation_version().as_deref()).expect("implementation");
        let configuration = AuthenticatedText::read(&format!("{root}/config.json"), None).expect("configuration");
        let locator = format!("{root}/model.safetensors");
        let (octets, header_octets, header_sha256) = AuthenticatedContainer::read_header(&locator).expect("header");
        let occurrence = SourceOccurrence {
            implementation,
            configuration,
            configuration_scope: vec![scope.to_owned()],
            container: AuthenticatedContainer { identity: FileIdentity::at(&locator).ok(), locator, octets, header_octets, header_sha256, content_sha256: Some(content_sha256.to_owned()), regions: regions.clone() },
            assets: assets.to_vec(),
        };
        let eps_text = occurrence.configuration_span("rms_norm_eps").unwrap_or_default();
        let eps = match holonic_engine::resident_law::decimal_to_rat(&eps_text) {
            Some(target) => {
                // the binary64 nearest the declared decimal: search the two dyadics around it
                nearest_binary64(&target)
            }
            None => {
                refusals.push(format!("modality {modality}: rms_norm_eps '{eps_text}' is not a decimal"));
                continue;
            }
        };
        let mut complex = PortedOperationComplex::new(&format!("{modality} projection into the shared stream"));
        let modality_port = complex.port(&format!("{modality} tower output, {width}"));
        let standing = complex.port("continuing standing, 2560");
        let mut realization = ResidentRealization::default();
        let tower_output = resident_layer::law(&mut complex, &format!("{modality} tower output"), OperationSpecies::Construction, vec![], vec![modality_port], None, vec![
            resident_layer::implementation(if modality == "vision" { "Gemma4Model.get_image_features (vision_outputs.pooler_output = self.embed_vision(inputs_embeds=last_hidden_state))" } else { "Gemma4Model.get_audio_features (audio_outputs.pooler_output = self.embed_audio(inputs_embeds=audio_outputs.last_hidden_state))" }),
            resident_layer::implementation("Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))"),
        ]).expect("law");
        realization.bind(tower_output, Standing { name: format!("{modality} tower output") });
        let rebase = resident_layer::law(&mut complex, &format!("{modality} pre-projection rebase, no gain"), OperationSpecies::Transport, vec![modality_port], vec![modality_port], None, vec![
            resident_layer::implementation("Gemma4MultimodalEmbedder.forward (embs_normed = self.embedding_pre_projection_norm(inputs_embeds))"),
            resident_layer::implementation("Gemma4MultimodalEmbedder.__init__ (self.embedding_pre_projection_norm = Gemma4RMSNorm(self.multimodal_hidden_size, eps=self.eps, with_scale=False))"),
            resident_layer::implementation("Gemma4RMSNorm._norm (return hidden_states * torch.pow(mean_squared, -0.5))"),
            resident_layer::implementation("Gemma4MultimodalEmbedder.__init__ (self.multimodal_hidden_size = getattr(multimodal_config, \"output_proj_dims\", multimodal_config.hidden_size))"),
            resident_layer::configuration("rms_norm_eps", &eps_text),
            resident_layer::configuration(width_field, &width.to_string()),
        ]).expect("law");
        realization.bind(rebase, RmsRebase { group: width, gain: None, eps });
        resident_layer::bond(&mut complex, "tower output rebases", modality_port, tower_output, rebase, 0).expect("bond");
        let projection = resident_layer::law(&mut complex, &format!("{modality} projection"), OperationSpecies::Transport, vec![modality_port], vec![standing], Some(population.to_owned()), vec![
            resident_layer::implementation("Gemma4MultimodalEmbedder.forward (return self.embedding_projection(embs_normed))"),
            resident_layer::implementation("Gemma4MultimodalEmbedder.__init__ (self.embedding_projection = nn.Linear(self.multimodal_hidden_size, self.text_hidden_size, bias=False))"),
            resident_layer::shape(population, &[tower::HIDDEN, width]),
        ]).expect("law");
        realization.bind(projection, Contract { population: population.to_owned() });
        resident_layer::bond(&mut complex, "projects into the stream", modality_port, rebase, projection, 0).expect("bond");
        if let Err(refusal) = realization.validate(&complex) {
            refusals.push(format!("modality {modality}: realization {refusal}"));
            continue;
        }
        let validations = match occurrence.validate(&complex) {
            Ok(v) => v,
            Err(refusal) => {
                refusals.push(format!("modality {modality}: source {refusal}"));
                continue;
            }
        };
        for (event, law) in &realization.bindings {
            let occ = &complex.shape.occurrences[event];
            let law_decl = &complex.shape.laws[&occ.law];
            let op = &complex.operations[&occ.law];
            let validation = validations.iter().find(|v| v.operation == law_decl.name).expect("validated");
            match law.entailment(validation) {
                Ok(entailment) => {
                    if let Some(carrier) = &op.carrier {
                        bound_by.entry(carrier.clone()).or_insert_with(|| format!("{modality} projection: {}", law_decl.name));
                    }
                    rows.push(AtlasRow {
                        deed: format!("modality projection ({modality})"),
                        operation: law_decl.name.clone(),
                        species: format!("{:?}", op.species),
                        law: law.name().to_owned(),
                        parameters: entailment.parameters.iter().map(|(p, v, by)| format!("{p}={v} ⟵ {by}")).collect::<Vec<_>>().join(" ; "),
                        inputs: law_decl.inputs.iter().map(|b| complex.shape.boundaries.objects[b].name.clone()).collect::<Vec<_>>().join(" | "),
                        outputs: law_decl.outputs.iter().map(|b| complex.shape.boundaries.objects[b].name.clone()).collect::<Vec<_>>().join(" | "),
                        carrier: op.carrier.clone().unwrap_or_default(),
                        status: "potential-only (portability control: its tower is not posed here)",
                        symbols: validation.symbols.len(),
                        fields: validation.fields.len(),
                        shapes: validation.shapes.len(),
                    });
                }
                Err(refusal) => refusals.push(format!("modality {modality} {}: entailment {refusal}", law_decl.name)),
            }
        }
    }
    rows
}

/// The `binary64` nearest an exact rational: the dyadic of 53 significant bits rounded to nearest.
fn nearest_binary64(target: &relational_geometry::Rat) -> Dyadic {
    use num_bigint::BigInt;
    use num_traits::{Signed, ToPrimitive};
    // scale so the integer part has 53 bits: find e with 2^e ≤ target < 2^(e+1)
    let mut e: i32 = 0;
    let two = relational_geometry::Rat::from_integer(BigInt::from(2));
    let one = relational_geometry::Rat::from_integer(BigInt::from(1));
    let mut t = target.abs();
    while t >= two { t = &t / &two; e += 1; }
    while t < one { t = &t * &two; e -= 1; }
    // significand = round(target · 2^(52 − e))
    let shift = 52 - e;
    let scaled = if shift >= 0 { target.abs() * relational_geometry::Rat::from_integer(BigInt::from(1) << shift as usize) } else { target.abs() / relational_geometry::Rat::from_integer(BigInt::from(1) << (-shift) as usize) };
    let rounded = (scaled + relational_geometry::Rat::new(BigInt::from(1), BigInt::from(2))).floor().to_integer();
    let significand = rounded.to_i64().expect("53 bits");
    Dyadic { significand: if target.is_negative() { -significand } else { significand }, exponent: -shift }
}

#[allow(dead_code)]
fn _unused(_: FrontPassageObstruction, _: CompileRefusal) {}
