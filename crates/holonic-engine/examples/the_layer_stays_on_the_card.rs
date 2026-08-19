//! **One complete source-authenticated Gemma-4-E4B layer-zero deed whose hot semantic chronology
//! is bound as one resident graph and launched once** — the per-layer input predecessor and the
//! layer as ONE diagram (the two diagrams' six plus twenty-three fronts lay as twenty-three fronts of
//! thirty-five occurrences once the predecessor is co-present with the layer's opening fronts),
//! priced and admitted whole before the first allocation, with both K/V
//! families, PLE, epsilon-aware normalization, chronology, contact, gating, residual joins, the
//! layer scalar, and the propagated remainder; the source bindings validated by symbol, slice,
//! field, shape and region; the source-runtime cross-chart defect carried as an artifact slot; and
//! every falsifier below carrying a predicate that can fail.
//!
//! Contract:
//! `research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`.
//! Plan: the Gemma instance blueprint §6 and the roadmap's Phoenix section, whose named gate is
//! *one complete source-authenticated layer with both K/V families, PLE, epsilon-aware
//! normalization, propagated remainder, GPU-owned semantic chronology, physical interchange,
//! mode-bound cover, complete work admitted before any predecessor launch, validated source
//! bindings, and non-vacuous controls.*
//!
//! # What this driver is, and what it is not
//!
//! It mounts the apparatus, reads the material the runtime names, founds the deed diagram of
//! `phoenix/resident_layer.rs`, and hands it to `front_passage::FrontPassage`. It computes no
//! standing. It reads out exactly one section per deed — the declared terminal — and it counts that
//! read in the census it prints. Every control below is a separate deed with its own terminal, or a
//! separate read of the one deed's other ports, said so.
//!
//! **It is not Phoenix inference, not a native model, not a rest and not an emission.** It is the
//! roadmap's immediate gate for one layer. `CONSTRUCTION_STATE.md` moves only when the roadmap's
//! Phoenix stations return, and this driver returns none of them.
//!
//! ```text
//!   cargo run --release -p holonic-engine --example the_layer_stays_on_the_card -- \
//!       --root /home/b/models/gemma-4-E4B-it --tokens 818,18740 --grain 48 --terms 14
//! ```
//!
//! `--work-ceiling N` declares the receiver's ceiling on width-weighted operations; without it the
//! receiver declares none and the deed is admitted on the carrier and the device alone, said so.
//! `--no-serial` skips the six-minute serial reference; `--no-source-face` skips the source
//! runtime; `--no-whole-digest` skips the sixteen-gigabyte container digest.

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/serial_reference.rs"]
mod serial_reference;

use std::collections::BTreeMap;
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::{WorkBudget, WorkMetric};
use holonic_engine::front_passage::{
    Ceiling, CompileRefusal, CompiledPassage, DeedReceiver, FrontPassage, FrontPassageObstruction, MaterialAdmission,
    PassageReturn, ResourceObstruction, ResidentMaterial,
};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::SourceTestimony;
use holonic_engine::resident_section::{
    production_cone_reaches_the_reference, word_value, Dyadic, ResidentGrain, ResidentSurface, SeriesAperture,
    REFUSED_MALFORMED,
};
use holonic_engine::source_occurrence::{AuthenticatedContainer, SourceOccurrence, SourceRefusal};
use num_bigint::BigInt;
use relational_geometry::Rat;
use resident_layer::{Founded, Sibling, Source};
use serial_reference::Serial;

struct Args {
    root: String,
    tokens: Vec<usize>,
    second_tokens: Vec<usize>,
    grain: u32,
    terms: u32,
    serial: bool,
    source_face: bool,
    whole_digest: bool,
    work_ceiling: Option<u64>,
    out: String,
    hidden_card_control: bool,
    python: String,
}

fn parse_args() -> Args {
    let mut args = Args {
        root: "/home/b/models/gemma-4-E4B-it".to_owned(),
        tokens: Vec::new(),
        second_tokens: vec![2, 6644],
        grain: 48,
        terms: 14,
        serial: true,
        source_face: true,
        whole_digest: true,
        work_ceiling: None,
        out: "output/the_layer_stays_on_the_card".to_owned(),
        hidden_card_control: false,
        python: "/home/b/scratch/huggingface/.venv/bin/python".to_owned(),
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--root" => args.root = it.next().expect("--root <dir>"),
            "--tokens" => args.tokens = it.next().expect("--tokens a,b").split(',').map(|t| t.trim().parse().expect("token id")).collect(),
            "--second-tokens" => args.second_tokens = it.next().expect("--second-tokens a,b").split(',').map(|t| t.trim().parse().expect("token id")).collect(),
            "--grain" => args.grain = it.next().expect("--grain F").parse().expect("u32"),
            "--terms" => args.terms = it.next().expect("--terms N").parse().expect("u32"),
            "--work-ceiling" => args.work_ceiling = Some(it.next().expect("--work-ceiling N").parse().expect("u64")),
            "--no-serial" => args.serial = false,
            "--no-source-face" => args.source_face = false,
            "--no-whole-digest" => args.whole_digest = false,
            "--out" => args.out = it.next().expect("--out dir"),
            "--python" => args.python = it.next().expect("--python <path>"),
            "--hidden-card-control" => args.hidden_card_control = true,
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

/// Process CPU time from `/proc/self/stat`, in clock ticks — apparatus telemetry, reported beside
/// the deed and never governing it.
fn cpu_ticks() -> u64 {
    std::fs::read_to_string("/proc/self/stat")
        .ok()
        .and_then(|stat| {
            let after = stat.rsplit(')').next()?;
            let fields: Vec<&str> = after.split_whitespace().collect();
            let utime: u64 = fields.get(11)?.parse().ok()?;
            let stime: u64 = fields.get(12)?.parse().ok()?;
            Some(utime + stime)
        })
        .unwrap_or(0)
}

/// Samples of the card's utilization while a deed runs, taken by `nvidia-smi` on another thread.
/// Telemetry only; it supports and never determines a grade.
fn sample_utilization(stop: Arc<AtomicBool>) -> std::thread::JoinHandle<Vec<u32>> {
    std::thread::spawn(move || {
        let mut samples = Vec::new();
        while !stop.load(Ordering::Relaxed) {
            if let Ok(output) = std::process::Command::new("nvidia-smi").args(["--query-gpu=utilization.gpu", "--format=csv,noheader,nounits"]).output() {
                if let Ok(text) = String::from_utf8(output.stdout) {
                    if let Ok(value) = text.trim().parse::<u32>() {
                        samples.push(value);
                    }
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(40));
        }
        samples
    })
}

fn describe_obstruction(obstruction: &FrontPassageObstruction) -> String {
    match obstruction {
        FrontPassageObstruction::Cover { front, barriers } => format!("CoverBarrier at front {front}: {barriers:?}"),
        FrontPassageObstruction::Interchange { front, because, .. } => format!("InterchangeRefusal at front {front}: {because:?}"),
        FrontPassageObstruction::Resource(resource) => format!("ResourceObstruction: {resource:?}"),
        FrontPassageObstruction::Compile(refusal) => format!("CompileRefusal: {refusal}"),
        FrontPassageObstruction::Refused { occurrence, operation, refusal, slot, lineage } => format!("the card refused at {occurrence:?} ({operation}): {refusal}; slot {slot:?}; complete obstruction lineage {:?}", lineage.refusals),
        FrontPassageObstruction::Sealed { occurrence, quotient, reopening } => format!("the section at {occurrence:?} was sealed away by the fused quotient {quotient:?}; {reopening}"),
    }
}

/// A deed of the whole diagram: bind under a sibling and a terminal, launch once, read the terminal.
struct Deed<'chart> {
    bound: CompiledPassage<'chart>,
    returned: PassageReturn,
    terminal: Vec<(i64, i64)>,
    /// The diagram the deed was founded from, retained so its returns outlive the bound passage.
    #[allow(dead_code)]
    founded: Founded,
}

#[allow(clippy::too_many_arguments)]
fn conduct<'chart>(
    passage: &FrontPassage<'chart>,
    material: &ResidentMaterial<'chart>,
    source: &SourceOccurrence,
    receiver: &DeedReceiver,
    material_admission: Option<&MaterialAdmission>,
    terms: SeriesAperture,
    layer_scalar: Dyadic,
    scales: &(holonic_engine::resident_section::DyadicEnclosure, holonic_engine::resident_section::DyadicEnclosure),
    sibling: Sibling,
    terminal: &'static str,
) -> Result<Deed<'chart>, FrontPassageObstruction> {
    let founded = resident_layer::found_deed(scales, terms, layer_scalar, sibling).map_err(|e| FrontPassageObstruction::Compile(CompileRefusal::Shape(e)))?;
    let terminal_event = founded.returns[terminal];
    let bound = passage.bind(&founded.complex, &founded.realization, material, source, receiver, material_admission, terminal_event)?;
    let returned = bound.launch(&passage.surface.mode())?;
    let terminal = bound.read_terminal(&returned)?;
    Ok(Deed { bound, returned, terminal, founded })
}

fn nested(coarse: &[(i64, i64)], coarse_grain: u32, fine: &[(i64, i64)], fine_grain: u32) -> (usize, usize) {
    let mut inside = 0usize;
    let mut outside = 0usize;
    for ((cl, ch), (fl, fh)) in coarse.iter().zip(fine) {
        let cl = word_value(*cl, ResidentGrain(coarse_grain));
        let ch = word_value(*ch, ResidentGrain(coarse_grain));
        let fl = word_value(*fl, ResidentGrain(fine_grain));
        let fh = word_value(*fh, ResidentGrain(fine_grain));
        if cl <= fl && fh <= ch {
            inside += 1;
        } else {
            outside += 1;
        }
    }
    (inside, outside)
}

fn moved(a: &[(i64, i64)], b: &[(i64, i64)]) -> usize {
    a.iter().zip(b).filter(|(x, y)| x != y).count()
}

/// The source runtime's face at one port in one dtype, decoded exactly through the float mouth.
struct SourceFace {
    values: Vec<Rat>,
}

/// One port's cross-chart defect against the resident enclosure: `chi_gamma = Phi_Y T_gamma −
/// S_gamma Phi_X` per coordinate, as the exact distance from the source value to the enclosure
/// (zero when inside), with the quantization fibre of the bf16 codeword beside it.
struct PortDefect {
    port: &'static str,
    dtype: &'static str,
    inside: usize,
    outside: usize,
    worst_gap: Rat,
    worst_at: Option<usize>,
    first_separating: Option<usize>,
    /// How many bf16 quantization fibres (the ulp interval around the codeword) meet the resident
    /// enclosure — the reconstruction fibre of the source's rounding.
    fibre_meets: usize,
    widest_enclosure: Rat,
}

fn read_faces(path: &str) -> Result<BTreeMap<(String, String), SourceFace>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut faces: BTreeMap<(String, String), Vec<(usize, Rat)>> = BTreeMap::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let (Some(port), Some(dtype), Some(index), Some(hex)) = (parts.next(), parts.next(), parts.next(), parts.next()) else { continue };
        let index: usize = index.parse().map_err(|_| format!("bad index in {line}"))?;
        let bits = u64::from_str_radix(hex, 16).map_err(|_| format!("bad hex in {line}"))?;
        let dyadic = Dyadic::of_binary64_bits(bits).map_err(|e| e.to_string())?;
        faces.entry((port.to_owned(), dtype.to_owned())).or_default().push((index, dyadic.value()));
    }
    Ok(faces
        .into_iter()
        .map(|(key, mut values)| {
            values.sort_by_key(|(index, _)| *index);
            (key, SourceFace { values: values.into_iter().map(|(_, v)| v).collect() })
        })
        .collect())
}

fn defect_of(port: &'static str, dtype: &'static str, enclosure: &[(i64, i64)], grain: ResidentGrain, face: &SourceFace) -> PortDefect {
    let mut inside = 0usize;
    let mut outside = 0usize;
    let mut worst_gap = Rat::from_integer(BigInt::from(0));
    let mut worst_at = None;
    let mut first_separating = None;
    let mut fibre_meets = 0usize;
    let mut widest = Rat::from_integer(BigInt::from(0));
    for (at, ((lo, hi), value)) in enclosure.iter().zip(&face.values).enumerate() {
        let lo = word_value(*lo, grain);
        let hi = word_value(*hi, grain);
        let width = &hi - &lo;
        if width > widest {
            widest = width;
        }
        if lo <= *value && *value <= hi {
            inside += 1;
        } else {
            outside += 1;
            let gap = if *value < lo { &lo - value } else { value - &hi };
            if gap > worst_gap {
                worst_gap = gap;
                worst_at = Some(at);
            }
            if first_separating.is_none() {
                first_separating = Some(at);
            }
        }
        // The bf16 quantization fibre: every real that rounds to this codeword — half an ulp
        // either side of the value, the ulp being 2^(exponent−7) for the value's binade.
        if dtype == "bf16" {
            let magnitude = if *value < Rat::from_integer(BigInt::from(0)) { -value.clone() } else { value.clone() };
            let ulp = bf16_ulp(&magnitude);
            let half = &ulp / Rat::from_integer(BigInt::from(2));
            let f_lo = value - &half;
            let f_hi = value + &half;
            if f_lo <= hi && lo <= f_hi {
                fibre_meets += 1;
            }
        }
    }
    PortDefect { port, dtype, inside, outside, worst_gap, worst_at, first_separating, fibre_meets, widest_enclosure: widest }
}

/// The unit in the last place of a bfloat16 codeword at a magnitude: `2^(e−7)` where `2^e ≤ m < 2^(e+1)`,
/// with the subnormal floor at `2^(−126−7)`.
fn bf16_ulp(magnitude: &Rat) -> Rat {
    let two = Rat::from_integer(BigInt::from(2));
    let mut e: i64 = 0;
    let mut power = Rat::from_integer(BigInt::from(1));
    if magnitude.numer() == &BigInt::from(0) {
        return Rat::new(BigInt::from(1), BigInt::from(1u128 << 100)) * Rat::new(BigInt::from(1), BigInt::from(1u64 << 33));
    }
    while &power * &two <= *magnitude {
        power = &power * &two;
        e += 1;
    }
    while power > *magnitude {
        power = &power / &two;
        e -= 1;
    }
    let e = e.max(-126);
    let shift = e - 7;
    if shift >= 0 {
        Rat::from_integer(BigInt::from(1) << shift as usize)
    } else {
        Rat::new(BigInt::from(1), BigInt::from(1) << (-shift) as usize)
    }
}

fn main() {
    let args = parse_args();
    if args.tokens.is_empty() {
        eprintln!("--tokens a,b,… is required: the material is supplied at runtime and compiled into nothing");
        std::process::exit(2);
    }
    println!("THE LAYER STAYS ON THE CARD — layer 0 of {}", args.root);
    println!("  tokens {:?}   grain 2^-{}   series aperture {}   second deed tokens {:?}", args.tokens, args.grain, args.terms, args.second_tokens);

    // ------------------------------------------------------------------------------------------
    // the apparatus, or the typed refusal
    // ------------------------------------------------------------------------------------------
    let readout = match ResidentReadout::new() {
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
    let declaration = surface.declaration().clone();
    let mode = surface.mode();
    println!("  resident chart: {} · {} multiprocessors · warp {} · {} threads/block · compute {}.{} · resident lanes {}",
        declaration.name, declaration.multiprocessors, declaration.warp_size, declaration.max_threads_per_block,
        declaration.capability_major, declaration.capability_minor, declaration.resident_lanes());
    println!("  mode: {} · {} · {} · kernel content {} · device {:?} · apparatus {}",
        mode.source_law, mode.abi, mode.kernel, mode.kernel_content.as_deref().unwrap_or("?"), mode.device, mode.apparatus);
    let memory = surface.memory_at_mount();
    println!("  device memory at mount: {} free of {} octets", memory.free_bytes, memory.total_bytes);

    // ------------------------------------------------------------------------------------------
    // the source occurrence and the material: mounted once
    // ------------------------------------------------------------------------------------------
    let container_locator = format!("{}/model.safetensors", args.root);
    let digest_thread = if args.whole_digest {
        let locator = container_locator.clone();
        Some(std::thread::spawn(move || {
            let clock = Instant::now();
            let digest = AuthenticatedContainer::digest_whole(&locator);
            (digest, clock.elapsed())
        }))
    } else {
        None
    };
    let mut source = Source::open(&args.root).expect("the source container opens");
    let mut material = ResidentMaterial::empty();
    let grain = ResidentGrain(args.grain);
    let passage = FrontPassage::new(surface, grain);
    // The material deed is predicted from the header and admitted before any map is allocated.
    let material_plan = resident_layer::material_plan(&source, args.tokens.len().max(args.second_tokens.len())).expect("the material plan reads from the header");
    let material_prediction = passage.predict_material(&material_plan);
    println!("  material deed predicted from the header: {} maps · {} resident octets · {} stored octets to cross · {} allocations · charged {} octets at the measured allocation grain {} · transient peak {} octets",
        material_prediction.maps.len(), material_prediction.resident_octets, material_prediction.ingress_octets, material_prediction.allocations, material_prediction.charged_octets, material_prediction.allocation_grain, material_prediction.transient_peak_octets);
    let material_admission = match passage.admit_material(&material_prediction) {
        Ok(admission) => admission,
        Err(obstruction) => {
            println!("REFUSED at material admission, before any map was allocated: {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    println!("  material admitted: {} coordinates, {} bounded, free {} octets at admission",
        material_admission.coordinates.len(), material_admission.coordinates.iter().filter(|c| c.is_bounded()).count(), material_admission.free_octets_at_admission);
    let clock = Instant::now();
    let mount = resident_layer::mount(&mut source, readout, &mut material).expect("the populations mount");
    let mount_ms = clock.elapsed().as_millis();
    let reconciled = material_admission.reconcile(&material);
    let material_reconciles = reconciled.iter().all(|(_, predicted, measured)| predicted == measured) && reconciled.len() == material_plan.maps.len();
    println!("  material reconciled: {} of {} maps measured exactly as predicted ({})",
        reconciled.iter().filter(|(_, p, m)| p == m).count(), reconciled.len(), if material_reconciles { "every prediction held" } else { "A PREDICTION WAS REFUTED" });
    let layer_scalar = mount.layer_scalar.expect("layer_scalar read");
    println!("  mounted {} populations · {} stored octets · {} resident octets · {} regions identified · layer_scalar {}·2^{} · {} ms",
        mount.populations, mount.stored_octets, mount.resident_octets, mount.regions.len(), layer_scalar.significand, layer_scalar.exponent, mount_ms);
    let bands = resident_layer::found_bands(resident_layer::BAND_TERMS).expect("bands found");
    let mounted_bands = surface.mount_bands(&bands, resident_layer::BAND_GRAIN).expect("bands mount");
    let max_position = (args.tokens.len().max(args.second_tokens.len()) - 1) as u32;
    material.bands.insert(resident_layer::BANDS.to_owned(), (mounted_bands, max_position));
    let positions: Vec<u32> = (0..args.tokens.len() as u32).collect();
    material.positions = Some(surface.mount_positions(&positions).expect("positions mount"));
    let scales = resident_layer::algebraic_scales().expect("scales");
    let content_sha256 = match digest_thread {
        Some(handle) => match handle.join().expect("digest thread") {
            (Ok(digest), elapsed) => {
                println!("  container content sha256 {digest} ({:.1} s, {} octets)", elapsed.as_secs_f64(), std::fs::metadata(&container_locator).map(|m| m.len()).unwrap_or(0));
                Some(digest)
            }
            (Err(error), _) => {
                println!("  container content digest refused: {error}");
                None
            }
        },
        None => {
            println!("  container content digest NOT taken (--no-whole-digest); the header and every mounted region are still identified");
            None
        }
    };
    let source_occurrence = match resident_layer::source_occurrence(&args.root, mount.regions.clone(), content_sha256) {
        Ok(occurrence) => occurrence,
        Err(error) => {
            println!("REFUSED: the source occurrence could not be authenticated — {error}");
            std::process::exit(3);
        }
    };
    println!("  source implementation {} sha256 {} ({})", source_occurrence.implementation.locator, source_occurrence.implementation.sha256, source_occurrence.implementation.version.as_deref().unwrap_or("version unread"));
    println!("  configuration {} sha256 {} · container header {} octets sha256 {} · {} assets declared ({} used)",
        source_occurrence.configuration.locator, source_occurrence.configuration.sha256, source_occurrence.container.header_octets, source_occurrence.container.header_sha256,
        source_occurrence.assets.len(), source_occurrence.assets.iter().filter(|a| a.used).count());
    let census_after_mount = surface.census();
    println!("  census after mount: ingress {} octets · allocations {} · resident {} octets", census_after_mount.ingress_octets, census_after_mount.allocations, census_after_mount.resident_octets_now);

    let enter_material = |material: &mut ResidentMaterial<'static>, source: &mut Source, tokens: &[usize]| {
        resident_layer::enter(source, tokens, material).expect("the entering rows read");
    };
    enter_material(&mut material, &mut source, &args.tokens);
    let terms = SeriesAperture(args.terms);
    let metric = WorkMetric::width_weighted();
    let receiver = match args.work_ceiling {
        Some(ceiling) => {
            println!("  the receiver declares the scalar metric {} with ceiling {ceiling}; every other semantic coordinate is exhibited as unbounded with what constrains it", metric.name);
            DeedReceiver::unbounded().with_scalar(WorkBudget::declared(metric.clone(), ceiling))
        }
        None => {
            println!("  the receiver declares NO ceiling on any semantic coordinate (--work-ceiling absent): every semantic coordinate is admitted as UNBOUNDED and exhibited with the apparatus limit that still constrains it; the apparatus coordinates are admitted against the mounted card; nothing is `None`");
            DeedReceiver::unbounded()
        }
    };
    let mut verdicts = Verdicts { lines: Vec::new(), failed: 0 };

    // ------------------------------------------------------------------------------------------
    // the diagram, the price of the whole deed, and the admission — before any allocation
    // ------------------------------------------------------------------------------------------
    println!("\nTHE DIAGRAM AND ITS PRICE, BEFORE ANY LAUNCH");
    let founded = resident_layer::found_deed(&scales, terms, layer_scalar, Sibling::Base).expect("deed founded");
    let plan = match passage.compile(&founded.complex, &founded.realization, &material, &source_occurrence, founded.returns[resident_layer::LAYER_RETURN]) {
        Ok(plan) => plan,
        Err(obstruction) => {
            println!("REFUSED at compile: {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    println!("  deed: {} ports · {} operations · {} occurrences · {} fronts · closed {} · species {:?}",
        plan.closure.ports, plan.closure.operations, plan.closure.occurrences, plan.closure.fronts, plan.closure.is_closed(), founded.complex.species_census());
    let widest_front = plan.fronts().iter().map(|f| f.breadth()).max().unwrap_or(0);
    println!("  widest front: {widest_front} members · source bindings validated: {} operations, {} symbols resolved, {} configuration fields matched, {} shapes matched, {} interventions typed",
        plan.source_bindings.len(),
        plan.source_bindings.iter().map(|b| b.symbols.len()).sum::<usize>(),
        plan.source_bindings.iter().map(|b| b.fields.len()).sum::<usize>(),
        plan.source_bindings.iter().map(|b| b.shapes.len()).sum::<usize>(),
        plan.source_bindings.iter().map(|b| b.interventions.len()).sum::<usize>());
    println!("  semantic work predicted a priori: {:?}", plan.deed_prediction.coordinates());
    println!("  apparatus predicted: {:?}", plan.apparatus_prediction);
    let admission = match passage.admit(&plan, &receiver, Some(&material_admission)) {
        Ok(admission) => admission,
        Err(obstruction) => {
            println!("REFUSED at admission: {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    println!("  admission (typed, product-ordered): admitted {} · {} semantic coordinates ({} bounded, {} unbounded) · {} apparatus coordinates ({} bounded, {} unbounded) · free {} octets at admission",
        admission.is_admitted(), admission.semantic.len(), admission.semantic.iter().filter(|c| c.is_bounded()).count(), admission.semantic.iter().filter(|c| !c.is_bounded()).count(),
        admission.apparatus.len(), admission.apparatus.iter().filter(|c| c.is_bounded()).count(), admission.apparatus.iter().filter(|c| !c.is_bounded()).count(), admission.free_octets_at_admission);
    for coordinate in admission.semantic.iter().chain(admission.apparatus.iter()) {
        match &coordinate.ceiling {
            Ceiling::Bounded { ceiling, declared_by } => println!("    {:<36} required {:>20} ≤ ceiling {:>20}  [{}]  {}", coordinate.name, coordinate.required, ceiling, if coordinate.admitted { "admitted" } else { "REFUSED" }, declared_by),
            Ceiling::Unbounded { because, constrained_by } => println!("    {:<36} required {:>20}   UNBOUNDED — {because}; constrained by {constrained_by:?}", coordinate.name, coordinate.required),
        }
    }
    let deed_price = metric.price(&plan.deed_prediction);
    let predicted_launches = plan.apparatus_prediction.captured_launches;
    let predicted_apparatus = plan.apparatus_prediction.clone();
    let predicted_entries_written = plan.deed_prediction.entries_written.clone();
    drop(plan);

    // ------------------------------------------------------------------------------------------
    // THE DEED — bound, launched once, read once
    // ------------------------------------------------------------------------------------------
    println!("\nTHE DEED — layer 0 with its per-layer input, {} tokens, terminal = the layer's return", args.tokens.len());
    let census_before_bind = surface.census();
    let bind_clock = Instant::now();
    let founded = resident_layer::found_deed(&scales, terms, layer_scalar, Sibling::Base).expect("deed founded");
    let bound = match passage.bind(&founded.complex, &founded.realization, &material, &source_occurrence, &receiver, Some(&material_admission), founded.returns[resident_layer::LAYER_RETURN]) {
        Ok(bound) => bound,
        Err(obstruction) => {
            println!("REFUSED at bind: {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    let bind_wall = bind_clock.elapsed();
    let census_after_bind = surface.census();
    let (graph, intended) = bound.graph();
    println!("  bound in {:.3} s: graph {} nodes / {} edges as the driver holds it · intended {:?} · kernel nodes {} · memset nodes {} · captured launches {} (predicted {})",
        bind_wall.as_secs_f64(), graph.nodes, graph.edges, intended, graph.kernel_nodes, graph.memset_nodes,
        census_after_bind.captured_launches - census_before_bind.captured_launches, predicted_launches);
    let census_before = surface.census();
    let ticks_before = cpu_ticks();
    let stop = Arc::new(AtomicBool::new(false));
    let sampler = sample_utilization(stop.clone());
    let clock = Instant::now();
    let returned = match bound.launch(&mode) {
        Ok(returned) => returned,
        Err(obstruction) => {
            stop.store(true, Ordering::Relaxed);
            println!("REFUSED during the deed: {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    let wall = clock.elapsed();
    stop.store(true, Ordering::Relaxed);
    let samples = sampler.join().unwrap_or_default();
    let ticks_after = cpu_ticks();
    let census_after = surface.census();
    let terminal = match bound.read_terminal(&returned) {
        Ok(terminal) => terminal,
        Err(obstruction) => {
            println!("REFUSED: the terminal did not stand — {}", describe_obstruction(&obstruction));
            std::process::exit(4);
        }
    };
    let census_after_read = surface.census();

    println!("  wall {:.3} s · CPU ticks {} · GPU utilization samples {:?} (telemetry, 40 ms aperture; supports, never grades)", wall.as_secs_f64(), ticks_after - ticks_before, samples);
    println!("  crossing census across the deed: deed launches {} → {} · captured launches {} → {} · synchronizations {} → {} · receipt egress {} → {} octets · section egress {} → {} · section read-outs {} → {} · ingress {} → {}",
        census_before.deed_launches, census_after.deed_launches, census_before.captured_launches, census_after.captured_launches,
        census_before.synchronizations, census_after.synchronizations, census_before.egress_receipt_octets, census_after.egress_receipt_octets,
        census_before.egress_section_octets, census_after.egress_section_octets, census_before.section_read_outs, census_after.section_read_outs,
        census_before.ingress_octets, census_after.ingress_octets);
    println!("  the terminal read afterwards: section egress {} → {} octets · read-outs {} → {}", census_after.egress_section_octets, census_after_read.egress_section_octets, census_after.section_read_outs, census_after_read.section_read_outs);
    println!("  resident octets now {} · peak {} · obstruction lineage: {} refusals (every occurrence stood: {})", census_after.resident_octets_now, census_after.resident_octets_peak, returned.obstruction.refusals.len(), returned.stands());

    println!("\nTHE FRONTS");
    let mut every_front_certified = true;
    let mut every_front_on_device = true;
    let mut every_coupling_ran = true;
    let mut contractions = 0usize;
    let mut reductions = 0usize;
    let mut couplings_total = 0usize;
    for (front, deed_front) in bound.fronts().iter().zip(&returned.fronts) {
        every_front_certified &= front.certificate.is_interchangeable();
        every_front_on_device &= front.cover.cpu_cells == 0 && front.cover.device_cells == front.members.len();
        couplings_total += deed_front.couplings.len();
        for coupling in &deed_front.couplings {
            every_coupling_ran &= coupling.written && coupling.refused == 0;
        }
        let names: Vec<&str> = front.members.iter().map(|(_, n)| *n).collect();
        let readings: Vec<String> = deed_front.readings.iter().map(|r| format!("{}:{}≤{}w{}", r.operation, r.measured.max_octave, r.bound, r.measured.max_width)).collect();
        println!("  depth {:>2}  {:<52} certified {:?} · device cells {} · lanes {} (idle {}) · couplings {} · [octave≤bound width] {:?}",
            front.depth, format!("{names:?}"), front.certificate.coherence, front.cover.device_cells, front.cover.occupied_lanes, front.cover.idle_lanes, deed_front.couplings.len(), readings);
        for (_, name) in &front.members {
            if *name == "contract" {
                contractions += 1;
            }
            if *name == "rms-rebase" || *name == "contact" {
                reductions += 1;
            }
        }
    }
    let mut a_priori_holds = true;
    let mut slack_max = 0i64;
    for (port, measured) in &returned.measured_octaves {
        let bound_octaves = bound.octave_field.get(port).copied().unwrap_or(0);
        if bound_octaves < *measured {
            a_priori_holds = false;
        }
        slack_max = slack_max.max(i64::from(bound_octaves) - i64::from(*measured));
    }
    println!("  contractions {contractions} · reductions {reductions} · couplings {couplings_total} (every one written and unrefused: {every_coupling_ran}) · a-priori bound ≥ measured on every port: {a_priori_holds} · widest slack {slack_max} octaves");
    println!("  traffic: resident lanes {} · per front (depth, lanes, idle, rounds) {:?}", bound.traffic.resident_lanes, bound.traffic.fronts);
    println!("           receiver_current over the diagram (earliest section, later arrivals deferred): the earliest section reaches the terminal at chronology {} with {} routes · {} later arrivals deferred (population {}) · {} reconvergent sites · traversible_chain junctions {} · composite (τ, Γ, T) {:?}",
        bound.traffic.earliest_arrival, bound.traffic.earliest_routes, bound.traffic.deferred_arrivals, bound.traffic.deferred_population,
        bound.traffic.reconvergent_sites, bound.traffic.junctions.len(),
        bound.traffic.composite.as_ref().map(|(t, r, p)| (t.to_string(), r.to_string(), p.to_string())));

    println!("\nTHE TERMINAL FACE — {} × 2560 enclosures at 2^-{}", args.tokens.len(), args.grain);
    let widest = terminal.iter().map(|(l, h)| h - l).max().unwrap_or(0);
    let zero_width = terminal.iter().filter(|(l, h)| l == h).count();
    println!("  widest enclosure {} grains · point enclosures {} of {}", widest, zero_width, terminal.len());
    for (at, (l, h)) in terminal.iter().enumerate().take(4) {
        println!("    [{at:>4}]  [{}, {}]", word_value(*l, grain), word_value(*h, grain));
    }

    // ------------------------------------------------------------------------------------------
    // THE FALSIFIERS
    // ------------------------------------------------------------------------------------------
    println!("\nTHE FALSIFIERS");
    // 1. the production cone: structural AND behavioural
    let cone = [
        ("resident_section.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/resident_section.rs")).unwrap_or_default()),
        ("front_passage.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/front_passage.rs")).unwrap_or_default()),
        ("resident_law.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/resident_law.rs")).unwrap_or_default()),
        ("source_occurrence.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/source_occurrence.rs")).unwrap_or_default()),
        ("phoenix/resident_layer.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/resident_layer.rs")).unwrap_or_default()),
        ("the_layer_stays_on_the_card.rs", std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/the_layer_stays_on_the_card.rs")).unwrap_or_default()),
    ];
    let scanned: Vec<(&str, String)> = cone
        .iter()
        .map(|(name, text)| {
            let body = text.split("#[cfg(test)]").next().unwrap_or("");
            let filtered: String = body.lines().filter(|line| !line.trim_start().starts_with('"')).collect::<Vec<_>>().join("\n");
            (*name, filtered)
        })
        .collect();
    let refs: Vec<(&str, &str)> = scanned.iter().map(|(n, t)| (*n, t.as_str())).collect();
    let reached = production_cone_reaches_the_reference(&refs);
    let no_launch_between = census_after.captured_launches == census_before.captured_launches
        && census_after.deed_launches == census_before.deed_launches + 1
        && census_after.synchronizations == census_before.synchronizations + 1
        && census_after.control_launches == census_before.control_launches;
    verdicts.record(1, "the production cone cannot reach the quarantined interpreter, and no launch is issued between the graph and its terminal",
        reached.is_empty() && no_launch_between,
        format!("structural scan over {} files: {reached:?} · behavioural: captured launches {} → {} (zero during the deed), deed launches {} → {}, synchronizations {} → {}, control launches {} → {}; a renamed dispatch loop would have to launch between the graph and the terminal and would move the census",
            cone.len(), census_before.captured_launches, census_after.captured_launches, census_before.deed_launches, census_after.deed_launches,
            census_before.synchronizations, census_after.synchronizations, census_before.control_launches, census_after.control_launches));

    // 2. the negative interval quotient, on the card, against the exact reference
    {
        let (results, flags) = surface.arithmetic_control(&[-2], &[1], &[1], &[1]).expect("control");
        let (q_lo, q_hi) = (results[0][6], results[0][7]);
        verdicts.record(2, "negative division: N=[-2,-1], D=[1,2] → [-2,-1/2] on the card",
            q_lo == -4 && q_hi == -1 && flags[0] == 0,
            format!("interval_quotient([-2,-1] lifted by one, [1,2]) on the card returned [{q_lo}, {q_hi}] at half-grain resolution = [{}, {}]; refusal word {}; the exact reference floor(-4/1) = -4 and ceil(-2/2) = -1",
                Rat::new(BigInt::from(q_lo), BigInt::from(2)), Rat::new(BigInt::from(q_hi), BigInt::from(2)), flags[0]));
    }

    // 3. GPU ownership: zero host semantic dispatch/decision boundaries
    verdicts.record(3, "the card owns the semantic chronology: zero host decision boundaries between the graph launch and the terminal",
        no_launch_between && every_front_certified && every_front_on_device && graph.edges == intended.1 && graph.nodes == intended.0 && returned.stands(),
        format!("one graph launch, one synchronize, one census read; graph nodes {} edges {} = intended {:?}; every front certified from footprints {every_front_certified}; every semantic cell on the device chart {every_front_on_device}; the obstruction lineage is empty; telemetry beside: CPU ticks {} over {:.3} s, utilization samples {:?}",
            graph.nodes, graph.edges, intended, ticks_after - ticks_before, wall.as_secs_f64(), samples));

    // 4. utilization telemetry supports and never determines: checked on this driver's own text —
    //    no verdict's predicate names the samples, the ticks, or a utilization threshold.
    {
        let own = &cone[5].1;
        let mut predicates_clean = true;
        let mut inspected = 0usize;
        let mut from = 0usize;
        while let Some(found) = own[from..].find("verdicts.record(") {
            let at = from + found;
            let end = own[at..].find("format!(").map(|e| at + e).unwrap_or(own.len());
            // The predicate slice, with string literals removed so a verdict's own name cannot
            // count against it.
            let mut stripped = String::new();
            let mut in_string = false;
            for character in own[at..end].chars() {
                if character == '"' {
                    in_string = !in_string;
                    continue;
                }
                if !in_string {
                    stripped.push(character);
                }
            }
            if stripped.contains("samples") || stripped.contains("ticks") || stripped.contains("utilization") {
                predicates_clean = false;
            }
            inspected += 1;
            from = end.max(at + 1);
        }
        verdicts.record(4, "utilization telemetry supports and never determines the grade",
            predicates_clean && inspected > 10,
            format!("{inspected} verdict predicates in this driver's own text inspected with their string literals removed: none names samples, ticks or utilization; the samples {:?} and CPU ticks {} stand beside the census that grades", samples, ticks_after - ticks_before));
    }

    // 5. the whole-deed admission: a semantic coordinate below requirement refuses before any
    //    allocation (scalar metric AND a named coordinate); an apparatus coordinate below
    //    requirement refuses likewise; the normal deed's admission is typed throughout;
    //    predicted and measured apparatus populations reconcile; the allocation grain moves the
    //    requirement lawfully; and no clock enters the admission.
    {
        let starved_scalar = DeedReceiver::unbounded().with_scalar(WorkBudget::declared(metric.clone(), u64::try_from(&deed_price).unwrap_or(u64::MAX).saturating_sub(1)));
        let written = u64::try_from(&predicted_entries_written).unwrap_or(u64::MAX);
        let starved_named = DeedReceiver::unbounded().with_ceiling("entries-written", written.saturating_sub(1));
        let narrow_apparatus = DeedReceiver::unbounded().with_apparatus_aperture("charged-resident-octets", predicted_apparatus.charged_octets.saturating_sub(1));
        let before = surface.census();
        let mut outcomes = Vec::new();
        for (what, rcv) in [("scalar", &starved_scalar), ("entries-written", &starved_named), ("charged-resident-octets", &narrow_apparatus)] {
            let founded_starved = resident_layer::found_deed(&scales, terms, layer_scalar, Sibling::Base).expect("deed founded");
            let outcome = passage.bind(&founded_starved.complex, &founded_starved.realization, &material, &source_occurrence, rcv, Some(&material_admission), founded_starved.returns[resident_layer::LAYER_RETURN]);
            let named = match &outcome {
                Err(FrontPassageObstruction::Resource(ResourceObstruction::Semantic { coordinate })) => format!("semantic refusal naming {} (required {} > ceiling)", coordinate.name, coordinate.required),
                Err(FrontPassageObstruction::Resource(ResourceObstruction::Apparatus { coordinate })) => format!("apparatus refusal naming {} (required {} > aperture)", coordinate.name, coordinate.required),
                Err(o) => format!("OTHER: {}", describe_obstruction(o).chars().take(120).collect::<String>()),
                Ok(_) => "BOUND (no refusal)".to_owned(),
            };
            let typed = match (what, &outcome) {
                ("scalar", Err(FrontPassageObstruction::Resource(ResourceObstruction::Semantic { coordinate }))) => coordinate.name == "scalar-price-under-declared-metric",
                ("entries-written", Err(FrontPassageObstruction::Resource(ResourceObstruction::Semantic { coordinate }))) => coordinate.name == "entries-written",
                ("charged-resident-octets", Err(FrontPassageObstruction::Resource(ResourceObstruction::Apparatus { coordinate }))) => coordinate.name == "charged-resident-octets",
                _ => false,
            };
            outcomes.push((what, typed, named));
        }
        let after = surface.census();
        let all_typed = outcomes.iter().all(|(_, typed, _)| *typed);
        verdicts.record(5, "a semantic coordinate, the scalar price, or an apparatus coordinate below requirement refuses before any allocation, naming the coordinate",
            all_typed && after.captured_launches == before.captured_launches && after.deed_launches == before.deed_launches && after.allocations == before.allocations && after.resident_octets_now == before.resident_octets_now,
            format!("{} · captured launches {} → {} · deed launches {} → {} · allocations {} → {} · resident octets {} → {}",
                outcomes.iter().map(|(w, _, n)| format!("{w}: {n}")).collect::<Vec<_>>().join(" · "), before.captured_launches, after.captured_launches, before.deed_launches, after.deed_launches, before.allocations, after.allocations, before.resident_octets_now, after.resident_octets_now));

        // 24. the actual deed's admission is typed throughout: every semantic coordinate bounded or
        //     unbounded-with-reason, every apparatus coordinate likewise, the material admission
        //     cited, and nothing `None`
        let semantic_names: Vec<&str> = bound.admission.semantic.iter().map(|c| c.name).collect();
        let every_unbounded_constrained = bound.admission.unbounded().all(|c| matches!(&c.ceiling, Ceiling::Unbounded { constrained_by, because } if !constrained_by.is_empty() && !because.is_empty()));
        let cited = bound.admission.apparatus.iter().find(|c| c.name == "source-standing-octets").map(|c| c.is_bounded() && c.admitted).unwrap_or(false);
        let bounded_apparatus: Vec<&str> = bound.admission.apparatus.iter().filter(|c| c.is_bounded()).map(|c| c.name).collect();
        verdicts.record(24, "the actual deed's admission is typed: every coordinate bounded or exhibited as unbounded with its reason and constraint; the material admission is cited; nothing is None",
            bound.admission.is_admitted() && bound.admission.semantic.len() == 9 && every_unbounded_constrained && cited && bound.admission.cited_material.is_some() && bounded_apparatus.contains(&"carrier-peak-octaves") && bounded_apparatus.contains(&"charged-resident-octets") && bounded_apparatus.contains(&"scratch-octets") && bounded_apparatus.contains(&"grid-extent"),
            format!("semantic coordinates {semantic_names:?}: {} bounded by the receiver, {} exhibited unbounded with their constraints; apparatus bounded {bounded_apparatus:?}, {} apparatus coordinates exhibited unbounded; source standing cited from the material admission ({} resident octets admitted against {} free)",
                bound.admission.semantic.iter().filter(|c| c.is_bounded()).count(), bound.admission.semantic.iter().filter(|c| !c.is_bounded()).count(), bound.admission.apparatus.iter().filter(|c| !c.is_bounded()).count(),
                material_admission.resident_octets(), material_admission.free_octets_at_admission));

        // 25. predicted and measured apparatus populations reconcile: launches, allocations,
        //     ingress, receipt egress, graph nodes and edges across the bind and the deed; and the
        //     material deed per map
        let captured = census_after_bind.captured_launches - census_before_bind.captured_launches;
        let allocations = census_after_bind.allocations - census_before_bind.allocations;
        let ingress = census_after_bind.ingress_octets - census_before_bind.ingress_octets;
        let receipt_egress = census_after.egress_receipt_octets - census_before.egress_receipt_octets;
        let reconciles = captured == predicted_apparatus.captured_launches
            && allocations == predicted_apparatus.allocations
            && ingress == predicted_apparatus.ingress_octets
            && receipt_egress == predicted_apparatus.egress_receipt_octets
            && graph.nodes as u64 == predicted_apparatus.graph_nodes
            && graph.edges as u64 == predicted_apparatus.graph_edges
            && census_after.deed_launches - census_before.deed_launches == predicted_apparatus.deed_launches
            && census_after.synchronizations - census_before.synchronizations == predicted_apparatus.synchronizations
            && material_reconciles;
        verdicts.record(25, "predicted and measured apparatus populations reconcile, for the deed and for the material",
            reconciles,
            format!("captured launches {captured} (predicted {}) · allocations {allocations} (predicted {}) · ingress {ingress} (predicted {}) · receipt egress {receipt_egress} (predicted {}) · graph nodes {} / edges {} (predicted {} / {}) · deed launches {} (predicted {}) · synchronizations {} (predicted {}) · material: {} of {} maps measured as predicted",
                predicted_apparatus.captured_launches, predicted_apparatus.allocations, predicted_apparatus.ingress_octets, predicted_apparatus.egress_receipt_octets, graph.nodes, graph.edges, predicted_apparatus.graph_nodes, predicted_apparatus.graph_edges,
                census_after.deed_launches - census_before.deed_launches, predicted_apparatus.deed_launches, census_after.synchronizations - census_before.synchronizations, predicted_apparatus.synchronizations,
                reconciled.iter().filter(|(_, p, m)| p == m).count(), reconciled.len()));

        // 26. the allocation grain changes the apparatus requirement lawfully
        let g = predicted_apparatus.allocation_grain;
        let under_one = predicted_apparatus.charged_under(1);
        let under_grain = predicted_apparatus.charged_under(g);
        let under_double = predicted_apparatus.charged_under(2 * g);
        let under_quad = predicted_apparatus.charged_under(4 * g);
        verdicts.record(26, "changing the allocation grain changes the apparatus requirement lawfully: the charge is the grain-rounded sum, monotone in the grain, equal to the words' sum at grain one and to the admitted charge at the measured grain",
            under_one == predicted_apparatus.deed_octets && under_grain == predicted_apparatus.charged_octets && under_grain >= under_one && under_double >= under_grain && under_quad >= under_double && under_double % (2 * g) == 0 && under_quad % (4 * g) == 0,
            format!("measured grain {g} octets (two probes, composing) · charge at grain 1 = {under_one} = words' sum {} · at {g} = {under_grain} = admitted charge {} · at {} = {under_double} · at {} = {under_quad}; {} allocations priced",
                predicted_apparatus.deed_octets, predicted_apparatus.charged_octets, 2 * g, 4 * g, predicted_apparatus.allocation_octets.len()));

        // 27. no wall-clock, utilization or scalar pressure chooses admission: the admission owner's
        //     own text, production bodies only
        let clock_tokens = ["Instant", "elapsed(", "SystemTime", "utilization", "nvidia-smi", "Duration"];
        let mut reached_clock: Vec<String> = Vec::new();
        for (name, text) in scanned.iter().take(4) {
            for token in clock_tokens {
                if text.contains(token) {
                    reached_clock.push(format!("{name}:{token}"));
                }
            }
        }
        verdicts.record(27, "no wall-clock, utilization or scalar pressure enters admission: the four owners' production bodies carry no clock token",
            reached_clock.is_empty(),
            format!("tokens {clock_tokens:?} scanned over resident_section.rs, front_passage.rs, resident_law.rs, source_occurrence.rs (tests and string literals removed): {reached_clock:?}; the admission compares counted and predicted coordinates against declared and measured ceilings only"));
    }

    // 6. source symbol / configuration / shape mutation refuses
    {
        let mutate = |f: &dyn Fn(&mut Vec<SourceTestimony>)| {
            let mut founded = resident_layer::found_deed(&scales, terms, layer_scalar, Sibling::Base).expect("deed");
            let law_id = founded.complex.shape.laws.iter().find(|(_, law)| law.name == "input rebase").map(|(id, _)| *id).expect("input rebase");
            let operation = founded.complex.operations.get_mut(&law_id).expect("bound");
            f(&mut operation.testimony);
            passage.compile(&founded.complex, &founded.realization, &material, &source_occurrence, founded.returns[resident_layer::LAYER_RETURN]).map(|_| ())
        };
        let symbol = mutate(&|t| t.push(SourceTestimony::Implementation { locator: resident_layer::IMPLEMENTATION.to_owned(), symbol: "Gemma4RMSNorm.forward_fabricated".to_owned() }));
        let slice = mutate(&|t| t.push(SourceTestimony::Implementation { locator: resident_layer::IMPLEMENTATION.to_owned(), symbol: "Gemma4RMSNorm.forward (normed_output = normed_output * self.weight.double())".to_owned() }));
        let field = mutate(&|t| t.push(SourceTestimony::Configuration { field: "rms_norm_eps".to_owned(), value: "1e-05".to_owned() }));
        let shape = mutate(&|t| t.push(SourceTestimony::DeclaredShape { population: resident_layer::named("input_layernorm.weight"), shape: vec![2561] }));
        let intervention = mutate(&|t| t.push(SourceTestimony::Intervention { statement: "an intervention offered as source law".to_owned() }));
        let refused = |o: &Result<(), FrontPassageObstruction>, want: &str| -> bool {
            matches!(o, Err(FrontPassageObstruction::Compile(CompileRefusal::Source(refusal))) if format!("{refusal:?}").starts_with(want))
        };
        verdicts.record(6, "a fabricated symbol, an absent slice, a drifted configuration value, a wrong shape, and an intervention on a source law refuse at compile",
            refused(&symbol, "SymbolUnresolved") && refused(&slice, "SliceAbsent") && refused(&field, "ConfigurationValueDiffers") && refused(&shape, "ShapeDiffers") && refused(&intervention, "InterventionOnSourceLaw"),
            format!("symbol → {} · slice → {} · field → {} · shape → {} · intervention → {}",
                symbol.err().map(|o| describe_obstruction(&o)).unwrap_or_else(|| "compiled".into()).chars().take(90).collect::<String>(),
                slice.err().map(|o| describe_obstruction(&o)).unwrap_or_else(|| "compiled".into()).chars().take(60).collect::<String>(),
                field.err().map(|o| describe_obstruction(&o)).unwrap_or_else(|| "compiled".into()).chars().take(110).collect::<String>(),
                shape.err().map(|o| describe_obstruction(&o)).unwrap_or_else(|| "compiled".into()).chars().take(110).collect::<String>(),
                intervention.err().map(|o| describe_obstruction(&o)).unwrap_or_else(|| "compiled".into()).chars().take(90).collect::<String>()));
    }

    // 7. cover / device / context / mode mismatch refuses
    {
        let before = surface.census();
        let mut foreign_device = mode.clone();
        foreign_device.device = Some("a device the surface did not mount".to_owned());
        let mut foreign_kernel = mode.clone();
        foreign_kernel.kernel_content = Some("00".repeat(32));
        let mut foreign_cover = mode.clone();
        foreign_cover.apparatus = "cpu".to_owned();
        let d = bound.launch(&foreign_device);
        let k = bound.launch(&foreign_kernel);
        let c = bound.launch(&foreign_cover);
        let after = surface.census();
        let is_mismatch = |o: &Result<PassageReturn, FrontPassageObstruction>| matches!(o, Err(FrontPassageObstruction::Resource(ResourceObstruction::Surface(holonic_engine::resident_section::ResidentRefusal::ModeMismatch { .. }))));
        verdicts.record(7, "a cover/device/kernel-content/mode mismatch refuses the launch without a deed",
            is_mismatch(&d) && is_mismatch(&k) && is_mismatch(&c) && after.deed_launches == before.deed_launches,
            format!("a foreign device, a foreign kernel content and a foreign apparatus chart each returned ModeMismatch; deed launches {} → {}; the surface's cover is built from the mounted device's attributes and the passage reads it there — no cover parameter exists to hand it a fiction",
                before.deed_launches, after.deed_launches));
    }

    // 8. signed-negative shift controls: the card against the exact reference
    {
        let cases: Vec<(i64, i64, i32, i64)> = vec![(i64::MIN, 3, 0, 0), (i64::MIN, 3, -1, 0), (i64::MIN, 3, 40, 0), (i64::MIN + 1, 7, -3, 0), (-7, 2, -1, 0), (-7, 2, 1, 0), (-1, 1, -70, 0), (0, 5, 60, 0), (5, 1, 126, 0), (5, 0, 0, 0), (-5, 3, 0, 4)];
        let a: Vec<i64> = cases.iter().map(|c| c.0).collect();
        let b: Vec<i64> = cases.iter().map(|c| c.1).collect();
        let s: Vec<i32> = cases.iter().map(|c| c.2).collect();
        let span: Vec<i64> = cases.iter().map(|c| c.3).collect();
        let (results, flags) = surface.arithmetic_control(&a, &b, &s, &span).expect("control");
        let mut agreed = 0usize;
        let mut lines = Vec::new();
        for (i, (av, _bv, sv, _)) in cases.iter().enumerate() {
            let a = BigInt::from(*av);
            let (expected_floor, expected_ceil, overflow) = if *sv >= 0 {
                let value = &a * (BigInt::from(1) << *sv as usize);
                let overflow = value.magnitude().bits() >= 128;
                (value.clone(), value, overflow)
            } else {
                let d = BigInt::from(1) << (-*sv) as usize;
                let q = &a / &d;
                let floor = if (&a % &d) != BigInt::from(0) && a < BigInt::from(0) { &q - 1 } else { q.clone() };
                let ceil = if (&a % &d) != BigInt::from(0) && a > BigInt::from(0) { &q + 1 } else { q };
                (floor, ceil, false)
            };
            let ok = if overflow { flags[i] & 1 != 0 } else { BigInt::from(results[i][0]) == expected_floor && BigInt::from(results[i][1]) == expected_ceil };
            let ok = ok && (cases[i].1 > 0 || flags[i] & REFUSED_MALFORMED != 0);
            if ok {
                agreed += 1;
            }
            lines.push(format!("({av},{sv}):{}", if ok { "agree" } else { "DISAGREE" }));
        }
        verdicts.record(8, "the signed-shift helpers on the card agree with the exact serial reference on the edge cases",
            agreed == cases.len(),
            format!("{agreed} of {} cases (signed minimum, its negation under shift, negative shifts both ways, a shift by the carrier width refusing, zero, a zero denominator refusing, a negative interval product): {}", cases.len(), lines.join(" ")));
    }

    // 9. physical concurrent completion preserves the complete receipt: co-present vs serialized
    //    vs serialized with every front opened in reverse
    println!("\n  — the serialized realizations");
    {
        let mut lines = Vec::new();
        let mut all_same = true;
        for (label, control) in [("serialized", FrontPassage::serialized(surface, grain)), ("serialized-reversed", FrontPassage::serialized_reversed(surface, grain))] {
            let deed = conduct(&control, &material, &source_occurrence, &receiver, Some(&material_admission), terms, layer_scalar, &scales, Sibling::Base, resident_layer::LAYER_RETURN)
                .unwrap_or_else(|o| { println!("REFUSED: {}", describe_obstruction(&o)); std::process::exit(4) });
            let (sgraph, sintended) = deed.bound.graph();
            let same_terminal = deed.terminal == terminal;
            let same_census = deed.returned.measured_octaves == returned.measured_octaves
                && deed.returned.fronts.iter().zip(&returned.fronts).all(|(a, b)| a.readings.iter().zip(&b.readings).all(|(x, y)| x.measured.max_width == y.measured.max_width && x.measured.max_octave == y.measured.max_octave));
            let same_lineage = deed.returned.obstruction == returned.obstruction;
            let edges_predicted = sgraph.edges as u64 == deed.bound.apparatus_prediction.graph_edges && (sgraph.nodes, sgraph.edges) == sintended;
            all_same &= same_terminal && same_census && same_lineage && edges_predicted;
            lines.push(format!("{label} ({} nodes, {} edges, intended {:?}, predicted edges {}): terminal identical {same_terminal}, every port's measured octave and width identical {same_census}, obstruction lineage identical {same_lineage}",
                sgraph.nodes, sgraph.edges, sintended, deed.bound.apparatus_prediction.graph_edges));
        }
        // and the co-present graph launched again returns the same face
        let again = bound.launch(&mode).expect("the co-present deed again");
        let again_terminal = bound.read_terminal(&again).expect("read");
        verdicts.record(9, "physical concurrent completion preserves the complete receipt where interchange is claimed",
            all_same && again_terminal == terminal && again.measured_octaves == returned.measured_octaves,
            format!("co-present graph ({} nodes, {} edges) against {}; the co-present graph launched a second time: terminal identical {}",
                graph.nodes, graph.edges, lines.join(" · "), again_terminal == terminal));
    }

    // 10. the source/runtime cross-chart defect, as an artifact slot
    println!("\n  — the source runtime's face, chi_gamma per port");
    let mut chi_lines: Vec<String> = Vec::new();
    if args.source_face {
        let faces_path = format!("{}/source-runtime-faces-{}-tokens.tsv", args.out, args.tokens.len());
        std::fs::create_dir_all(&args.out).expect("output directory");
        let clock = Instant::now();
        let status = std::process::Command::new(&args.python)
            .args([concat!(env!("CARGO_MANIFEST_DIR"), "/examples/phoenix/source_runtime_face.py"), "--tokens", &args.tokens.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(","), "--emit", &faces_path])
            .output();
        match status {
            Ok(output) if output.status.success() => {
                let faces = read_faces(&faces_path).expect("faces read");
                println!("  source runtime emitted {} faces in {:.1} s → {faces_path}", faces.len(), clock.elapsed().as_secs_f64());
                // The ports, read from the one bound deed after its terminal: extra section reads,
                // counted, for the comparison slot and nothing else.
                let ports: [(&'static str, &'static str); 6] = [
                    ("input-rebase", resident_layer::INPUT_REBASE),
                    ("receiver-projection", resident_layer::RECEIVER_PROJECTION),
                    ("contact", resident_layer::CONTACT),
                    ("first-re-entry", resident_layer::FIRST_RE_ENTRY),
                    ("second-re-entry", resident_layer::SECOND_RE_ENTRY),
                    ("layer", resident_layer::LAYER_RETURN),
                ];
                let mut defects: Vec<PortDefect> = Vec::new();
                for (port, name) in ports {
                    let section = bound.section(founded.returns[name]).expect("port section");
                    let enclosure = surface.read_out(section).expect("port read");
                    for dtype in ["bf16", "f32"] {
                        if let Some(face) = faces.get(&(port.to_owned(), dtype.to_owned())) {
                            defects.push(defect_of(port, dtype, &enclosure, grain, face));
                        }
                    }
                }
                for d in &defects {
                    let line = format!("    chi[{:<19} {}] inside {:>5} outside {:>5} · worst gap {:.3e} at {:?} · first separating coordinate {:?} · bf16 fibre meets enclosure {:>5} · widest enclosure {:.3e}",
                        d.port, d.dtype, d.inside, d.outside, rat_f64(&d.worst_gap), d.worst_at, d.first_separating, d.fibre_meets, rat_f64(&d.widest_enclosure));
                    println!("{line}");
                    chi_lines.push(line);
                }
                let terminal_bf16 = defects.iter().find(|d| d.port == "layer" && d.dtype == "bf16");
                let earliest_bf16 = defects.iter().filter(|d| d.dtype == "bf16" && d.outside > 0).map(|d| d.port).next();
                let terminal_f32 = defects.iter().find(|d| d.port == "layer" && d.dtype == "f32");
                verdicts.record(10, "the source/runtime chi is nonzero on the bf16 face and propagates from an earlier port to the terminal",
                    terminal_bf16.is_some_and(|d| d.outside > 0) && earliest_bf16.is_some_and(|p| p != "layer"),
                    format!("bf16 face: outside the resident enclosure at the terminal {} of {}; the earliest port where the bf16 face leaves the enclosure is {:?}; f32 face at the terminal: outside {}; the resident enclosure is an interval realization of the exact formula over the stored BF16 map and the source's runtime rounds every intermediate — chi is the source's rounding fibre, carried per port and not dismissed",
                        terminal_bf16.map(|d| d.outside).unwrap_or(0), terminal_bf16.map(|d| d.inside + d.outside).unwrap_or(0), earliest_bf16, terminal_f32.map(|d| d.outside).unwrap_or(0)));
            }
            Ok(output) => verdicts.open(10, "the source/runtime chi slot", &format!("the source runtime refused: {}", String::from_utf8_lossy(&output.stderr).chars().take(300).collect::<String>())),
            Err(error) => verdicts.open(10, "the source/runtime chi slot", &format!("the source runtime could not be invoked at {}: {error}", args.python)),
        }
    } else {
        verdicts.open(10, "the source/runtime chi slot", "not run (--no-source-face)");
    }

    // 12. hiding the card returns a typed refusal and no answer — an executed subprocess control
    println!("\n  — the hidden-card control");
    {
        let exe = std::env::current_exe().expect("this executable");
        let output = std::process::Command::new(exe)
            .env("CUDA_VISIBLE_DEVICES", "")
            .args(["--tokens", "1", "--hidden-card-control", "--no-serial", "--no-source-face", "--no-whole-digest", "--root", &args.root])
            .output();
        match output {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let refused = stdout.contains("REFUSED") && !stdout.contains("THE TERMINAL FACE") && output.status.code() == Some(3);
                verdicts.record(12, "hiding the card returns a typed refusal and no semantic answer",
                    refused,
                    format!("subprocess with CUDA_VISIBLE_DEVICES='' exited {:?}; stdout: {}", output.status.code(), stdout.lines().filter(|l| l.contains("REFUSED") || l.contains("fallback")).collect::<Vec<_>>().join(" | ")));
            }
            Err(error) => verdicts.record(12, "hiding the card returns a typed refusal and no semantic answer", false, format!("the control could not be spawned: {error}")),
        }
    }

    // 13. both K/V families are separately load-bearing
    println!("\n  — the K/V families");
    {
        let base_contact = conduct(&passage, &material, &source_occurrence, &receiver, Some(&material_admission), terms, layer_scalar, &scales, Sibling::Base, resident_layer::CONTACT)
            .unwrap_or_else(|o| { println!("REFUSED: {}", describe_obstruction(&o)); std::process::exit(4) });
        let mut family_report = Vec::new();
        let mut families_separate = true;
        for family in 0..resident_layer::KV_HEADS {
            let withdrawn = conduct(&passage, &material, &source_occurrence, &receiver, Some(&material_admission), terms, layer_scalar, &scales, Sibling::WithdrawFamily(family), resident_layer::CONTACT)
                .unwrap_or_else(|o| { println!("REFUSED: {}", describe_obstruction(&o)); std::process::exit(4) });
            let per_head = resident_layer::HEAD_WIDTH;
            let heads_per_family = resident_layer::HEADS / resident_layer::KV_HEADS;
            let mut moved_by_head = vec![0usize; resident_layer::HEADS];
            for (at, (a, b)) in base_contact.terminal.iter().zip(&withdrawn.terminal).enumerate() {
                if a != b {
                    let head = (at % (resident_layer::HEADS * per_head)) / per_head;
                    moved_by_head[head] += 1;
                }
            }
            let served: Vec<usize> = (family * heads_per_family..(family + 1) * heads_per_family).collect();
            let served_moved = served.iter().all(|h| moved_by_head[*h] > 0);
            let others_still = (0..resident_layer::HEADS).filter(|h| !served.contains(h)).all(|h| moved_by_head[h] == 0);
            families_separate &= served_moved && others_still;
            let interventions: usize = withdrawn.bound.source_bindings.iter().map(|b| b.interventions.len()).sum();
            family_report.push(format!("family {family} withdrawn (typed as {interventions} interventions): moved coordinates by head {moved_by_head:?} (served heads {served:?})"));
        }
        verdicts.record(13, "both K/V families are separately load-bearing, and the withdrawal is typed as an intervention", families_separate, family_report.join(" · "));
    }

    // 14. a finer aperture nests the terminal enclosure
    println!("\n  — the finer aperture");
    {
        let fine_passage = FrontPassage::new(surface, ResidentGrain(args.grain + 4));
        let fine = conduct(&fine_passage, &material, &source_occurrence, &receiver, Some(&material_admission), SeriesAperture(args.terms + 8), layer_scalar, &scales, Sibling::Base, resident_layer::LAYER_RETURN)
            .unwrap_or_else(|o| { println!("REFUSED: {}", describe_obstruction(&o)); std::process::exit(4) });
        let (inside, outside) = nested(&terminal, args.grain, &fine.terminal, args.grain + 4);
        let fine_widest = fine.terminal.iter().map(|(l, h)| word_value(*h, ResidentGrain(args.grain + 4)) - word_value(*l, ResidentGrain(args.grain + 4))).max().unwrap_or_else(|| Rat::from_integer(0.into()));
        let coarse_widest = terminal.iter().map(|(l, h)| word_value(*h, grain) - word_value(*l, grain)).max().unwrap_or_else(|| Rat::from_integer(0.into()));
        verdicts.record(14, "increasing the approximation aperture nests the terminal enclosure",
            outside == 0 && fine_widest <= coarse_widest,
            format!("grain 2^-{} terms {} against grain 2^-{} terms {}: {inside} of {} terminal enclosures nested, {outside} not; widest coarse {:.3e} · widest fine {:.3e}",
                args.grain, args.terms, args.grain + 4, args.terms + 8, terminal.len(), rat_f64(&coarse_widest), rat_f64(&fine_widest)));
    }

    // 15. removing a local remainder reopens the terminal fibre or refuses
    println!("\n  — the remainder removed at one site");
    {
        let collapsed = conduct(&passage, &material, &source_occurrence, &receiver, Some(&material_admission), terms, layer_scalar, &scales, Sibling::CollapseAfterInputRebase, resident_layer::LAYER_RETURN);
        match &collapsed {
            Ok(collapsed) => {
                let m = moved(&collapsed.terminal, &terminal);
                let (inside, outside) = nested(&terminal, args.grain, &collapsed.terminal, args.grain);
                verdicts.record(15, "removing a local remainder reopens the terminal fibre or refuses", m > 0,
                    format!("input rebase collapsed to midpoints (typed as an intervention): {m} of {} terminal coordinates moved; the collapsed terminal sits inside the sound one at {inside} coordinates and outside it at {outside} — the sound enclosure is not reproduced by the unsound one", terminal.len()));
            }
            Err(o) => verdicts.record(15, "removing a local remainder reopens the terminal fibre or refuses", true, format!("refused: {}", describe_obstruction(o))),
        }
    }

    // 16. weights mount once for repeated inference: a second deed on other tokens, same bound passage
    println!("\n  — the second deed, other tokens, the same bound passage refilled");
    {
        let populations_before = material.populations.len();
        let ingress_before = surface.census().ingress_octets;
        let allocations_before = surface.census().allocations;
        enter_material(&mut material, &mut source, &args.second_tokens);
        bound.refill(&material).expect("refill");
        let second = bound.launch(&mode).expect("second deed");
        let second_terminal = bound.read_terminal(&second).expect("read");
        let ingress_after = surface.census().ingress_octets;
        let entering_rows_octets = (args.second_tokens.len() * (resident_layer::HIDDEN + resident_layer::PLE_WIDTH) * 2) as u64;
        verdicts.record(16, "invariant weights mount once for repeated inference; new material crosses once into the bound passage",
            material.populations.len() == populations_before && ingress_after - ingress_before == entering_rows_octets && surface.census().allocations == allocations_before && second.stands(),
            format!("populations {} → {} · ingress for the second deed {} octets = entering rows {} · allocations {} → {} · the second terminal differs from the first in {} of {} coordinates",
                populations_before, material.populations.len(), ingress_after - ingress_before, entering_rows_octets, allocations_before, surface.census().allocations, moved(&second_terminal, &terminal), terminal.len()));
        // restore the main deed's material for the serial reference below
        enter_material(&mut material, &mut source, &args.tokens);
        bound.refill(&material).expect("refill");
    }

    // 28–31. LINEAGE-LOCAL REFUSAL TRANSPORT. The per-layer entering rows are poisoned with a
    //        non-finite bf16 codeword at a NONZERO coordinate, so the per-layer token entry refuses
    //        MALFORMED on the card at runtime, in one branch. Every successor of that branch must
    //        refuse deterministically naming its predecessor; the attention and gated-passage
    //        chains — unrelated siblings — must be bit-identical to the clean deed; the complete
    //        obstruction lineage must be one reading under the co-present, serialized and
    //        reversed-serialized schedules; and the terminal must never be accepted as standing.
    println!("\n  — the poisoned branch: a runtime refusal at a nonzero coordinate");
    {
        let base = bound.launch(&mode).expect("the clean deed again");
        let base_terminal = bound.read_terminal(&base).expect("read");
        let siblings: [(&str, &'static str); 5] = [("input-rebase", resident_layer::INPUT_REBASE), ("receiver-projection", resident_layer::RECEIVER_PROJECTION), ("contact", resident_layer::CONTACT), ("first-re-entry", resident_layer::FIRST_RE_ENTRY), ("second-re-entry", resident_layer::SECOND_RE_ENTRY)];
        let base_siblings: Vec<(&str, Vec<(i64, i64)>)> = siblings.iter().map(|(label, name)| (*label, bound.read_section(&base, founded.returns[name]).expect("sibling stood"))).collect();
        let coordinate = 7usize;
        let original = material.entering[resident_layer::PLE_ENTERING].words[coordinate];
        material.entering.get_mut(resident_layer::PLE_ENTERING).expect("per-layer rows").words[coordinate] = 0x7F80;
        let mut lineages = Vec::new();
        let mut refusal_lists = Vec::new();
        let mut report = Vec::new();
        let mut successors_refuse = true;
        let mut siblings_identical = true;
        let mut terminal_refused = true;
        let mut origin_is_ple_entry = true;
        let mut footprints_carry_slots = true;
        for (label, control) in [("co-present", FrontPassage::new(surface, grain)), ("serialized", FrontPassage::serialized(surface, grain)), ("serialized-reversed", FrontPassage::serialized_reversed(surface, grain))] {
            let founded_p = resident_layer::found_deed(&scales, terms, layer_scalar, Sibling::Base).expect("deed founded");
            let bound_p = control.bind(&founded_p.complex, &founded_p.realization, &material, &source_occurrence, &receiver, Some(&material_admission), founded_p.returns[resident_layer::LAYER_RETURN])
                .unwrap_or_else(|o| { println!("REFUSED: {}", describe_obstruction(&o)); std::process::exit(4) });
            for front in bound_p.fronts() {
                for (footprint, (reads, own)) in front.footprints.iter().zip(&front.slot_footprints) {
                    footprints_carry_slots &= footprint.writes.contains(own) && reads.iter().all(|r| footprint.reads.contains(r));
                }
                footprints_carry_slots &= front.certificate.is_interchangeable();
            }
            let returned_p = bound_p.launch(&mode).expect("the poisoned deed returns whole");
            let lineage = &returned_p.obstruction;
            // the origin: the per-layer token entry, MALFORMED, of its own
            let ple_index = bound_p.index_of(founded_p.returns[resident_layer::X0]).map(|_| bound_p.index_of(founded_p.complex.shape.occurrences.keys().copied().find(|e| bound_p.producers_of(*e).is_some_and(|p| p.is_empty()) && founded_p.returns.values().all(|r| r != e)).expect("the per-layer token entry is the entering occurrence that is not a named return")).expect("index"));
            let origins: Vec<usize> = lineage.origins().map(|r| r.index).collect();
            origin_is_ple_entry &= origins.len() == 1 && Some(origins[0]) == ple_index && lineage.origins().all(|r| r.flags & REFUSED_MALFORMED != 0);
            // every successor of the origin refuses upstream, deterministically, naming a predecessor
            // that refused; no refusal stands outside the origin's forward cone
            let mut cone: Vec<bool> = vec![false; bound_p.apparatus_prediction.graph_nodes as usize];
            if let Some(origin) = origins.first() {
                cone[*origin] = true;
                for index in 0..cone.len() {
                    if let Some(event) = bound_p.occurrence_at(index) {
                        if let Some(producers) = bound_p.producers_of(event) {
                            if producers.iter().any(|p| cone[*p]) {
                                cone[index] = true;
                            }
                        }
                    }
                }
            }
            let in_cone: Vec<usize> = cone.iter().enumerate().filter(|(_, c)| **c).map(|(i, _)| i).collect();
            let refused_indices: Vec<usize> = lineage.refusals.iter().map(|r| r.index).collect();
            successors_refuse &= refused_indices == in_cone
                && lineage.refusals.iter().filter(|r| !r.origin).all(|r| r.upstream_first.is_some_and(|p| cone[p]) && r.upstream_count >= 1 && r.flags & holonic_engine::resident_section::REFUSED_UPSTREAM != 0);
            // the unrelated siblings are bit-identical to the clean deed
            for (sibling_label, clean) in &base_siblings {
                let name = siblings.iter().find(|(l, _)| l == sibling_label).map(|(_, n)| *n).expect("sibling");
                match bound_p.read_section(&returned_p, founded_p.returns[name]) {
                    Ok(words) => siblings_identical &= words == *clean,
                    Err(_) => siblings_identical = false,
                }
            }
            // the terminal is refused by name, never read as standing
            let terminal_outcome = bound_p.read_terminal(&returned_p);
            terminal_refused &= matches!(&terminal_outcome, Err(FrontPassageObstruction::Refused { occurrence, lineage: l, .. }) if *occurrence == founded_p.returns[resident_layer::LAYER_RETURN] && l == lineage);
            terminal_refused &= matches!(bound_p.standing(&returned_p), Err(FrontPassageObstruction::Refused { .. }));
            report.push(format!("{label}: origins {origins:?} (the per-layer token entry, MALFORMED at coordinate {coordinate}) · forward cone {} occurrences · refusals {} = cone {} · carried refusals each name a refusing predecessor · siblings identical {siblings_identical} · terminal refused {}",
                in_cone.len(), refused_indices.len(), refused_indices == in_cone, matches!(terminal_outcome, Err(_))));
            lineages.push(lineage.clone());
            refusal_lists.push(returned_p.refusals.iter().map(|(e, _, s)| (*e, *s)).collect::<Vec<_>>());
        }
        material.entering.get_mut(resident_layer::PLE_ENTERING).expect("per-layer rows").words[coordinate] = original;
        bound.refill(&material).expect("refill");
        let schedules_agree = lineages.windows(2).all(|w| w[0] == w[1]) && refusal_lists.windows(2).all(|w| w[0] == w[1]);
        let after_restore = bound.launch(&mode).expect("the clean deed after restoring");
        let restored_terminal = bound.read_terminal(&after_restore).expect("read");
        verdicts.record(28, "a runtime refusal at a nonzero coordinate in one branch makes every successor of that branch refuse deterministically, naming a refusing predecessor, and nothing outside the branch's forward cone",
            origin_is_ple_entry && successors_refuse,
            report.join(" || "));
        verdicts.record(29, "an unrelated co-present sibling of the failing branch remains bit-identical to the clean deed",
            siblings_identical && restored_terminal == base_terminal,
            format!("five sibling sections (input rebase, receiver projection, contact, first re-entry, second re-entry) read from each poisoned deed and compared word for word with the clean deed: identical {siblings_identical}; the clean deed after restoring the codeword returns the base terminal bit-identically: {}", restored_terminal == base_terminal));
        verdicts.record(30, "co-present, serialized and reversed-serialized schedules return the identical complete obstruction lineage",
            schedules_agree && lineages.len() == 3,
            format!("three schedules, {} refusals each, lineages equal {schedules_agree}: {:?}", lineages.first().map(|l| l.refusals.len()).unwrap_or(0), lineages.first().map(|l| l.refusals.iter().map(|r| (r.index, r.origin, r.upstream_first)).collect::<Vec<_>>()).unwrap_or_default()));
        verdicts.record(31, "a refusal never produces a partially written section accepted as standing, and every footprint carries the predecessor slots read and the own slot written",
            terminal_refused && footprints_carry_slots,
            format!("the poisoned terminal refused by name with the complete lineage under every schedule: {terminal_refused}; `standing` refused likewise; every member footprint carries its predecessors' census slots as reads and its own as a write, and every front is FootprintDisjoint: {footprints_carry_slots}"));
    }

    // 11. poisoning the CPU reference cannot move the GPU result
    println!("\n  — the serial reference");
    if args.serial && args.tokens.len() <= 4 {
        let clock = Instant::now();
        let serial = Serial::new(96);
        let reference = serial_layer(&serial, &mut source, &args.tokens, layer_scalar, &scales, args.terms as usize + 8);
        match reference {
            Ok(reference) => {
                let parity = serial.parity(&terminal, args.grain, &reference);
                let poisoned: Vec<_> = reference.iter().map(|(l, h)| (l + BigInt::from(1u64 << 40) * BigInt::from(1u64 << 56), h + BigInt::from(1u64 << 40) * BigInt::from(1u64 << 56))).collect();
                let poisoned_parity = serial.parity(&terminal, args.grain, &poisoned);
                let again = bound.launch(&mode).expect("the deed again");
                let again_terminal = bound.read_terminal(&again).expect("read");
                verdicts.record(11, "poisoning the CPU reference cannot move the GPU result; it only fails parity",
                    parity.holds() && !poisoned_parity.holds() && again_terminal == terminal && again.stands(),
                    format!("serial reference at 2^-96 in {:.1} s: parity {} over {} coordinates ({} disagree; widest resident {} grains, widest serial {} grains of 2^-96); poisoned reference: {} disagree; the card's terminal re-read is bit-identical: {}",
                        clock.elapsed().as_secs_f64(), parity.holds(), parity.coordinates, parity.disagreeing.len(), parity.widest_resident_grains, parity.widest_serial_grains,
                        poisoned_parity.disagreeing.len(), again_terminal == terminal));
            }
            Err(error) => verdicts.record(11, "poisoning the CPU reference cannot move the GPU result", false, format!("the serial reference refused: {error}")),
        }
    } else {
        verdicts.open(11, "poisoning the CPU reference cannot move the GPU result", "the serial reference was not run (--no-serial, or more than four tokens)");
    }

    // stations not attempted here
    for (number, name) in [
        (17u32, "seal → separate-process mount → seal without the original buffers"),
        (18, "the native rest contains no program, event ordinals, hard-coded rows or source routing"),
        (19, "runtime inference does not spawn an example program"),
        (20, "replacing the adjoint with a transpose changes the cultivation delta or refuses"),
        (21, "held-out material is absent during development and cultivation"),
        (22, "matched arms share one predecessor rather than three complete bodies"),
        (23, "targeted ablation removes only the attributable cultivated consequence"),
    ] {
        verdicts.open(number, name, "not attempted: the roadmap's execution order reaches rest, inference, condensation, cultivation and ablation only after this one-layer resident deed; this driver is that deed and claims no later station");
    }

    // ------------------------------------------------------------------------------------------
    // the deposit
    // ------------------------------------------------------------------------------------------
    std::fs::create_dir_all(&args.out).expect("output directory");
    let path = format!("{}/layer-0-resident-{}-tokens-grain-{}-terms-{}.form", args.out, args.tokens.len(), args.grain, args.terms);
    let mut file = std::fs::File::create(&path).expect("receipt file");
    writeln!(file, "THE LAYER STAYS ON THE CARD — receipt").unwrap();
    writeln!(file, "root {} · tokens {:?} · grain 2^-{} · terms {} · device {}", args.root, args.tokens, args.grain, args.terms, declaration.name).unwrap();
    writeln!(file, "mode {:?}", mode).unwrap();
    writeln!(file, "source implementation {} sha256 {} ({})", source_occurrence.implementation.locator, source_occurrence.implementation.sha256, source_occurrence.implementation.version.as_deref().unwrap_or("?")).unwrap();
    writeln!(file, "source configuration {} sha256 {}", source_occurrence.configuration.locator, source_occurrence.configuration.sha256).unwrap();
    writeln!(file, "source container {} octets {} header octets {} header sha256 {} content sha256 {:?}", source_occurrence.container.locator, source_occurrence.container.octets, source_occurrence.container.header_octets, source_occurrence.container.header_sha256, source_occurrence.container.content_sha256).unwrap();
    for (name, region) in &source_occurrence.container.regions {
        writeln!(file, "  region {name} dtype {} shape {:?} span {}..{} sha256 {:?}", region.dtype, region.shape, region.start, region.end, region.sha256).unwrap();
    }
    for asset in &source_occurrence.assets {
        writeln!(file, "  asset {} {} sha256 {:?} used {}", asset.role, asset.locator, asset.sha256, asset.used).unwrap();
    }
    writeln!(file, "source bindings validated:").unwrap();
    for binding in &bound.source_bindings {
        writeln!(file, "  {} [{:?}] symbols {:?} fields {:?} shapes {:?} interventions {:?}", binding.operation, binding.species,
            binding.symbols.iter().map(|s| format!("{} @{}", s.symbol, s.line)).collect::<Vec<_>>(), binding.fields, binding.shapes, binding.interventions).unwrap();
    }
    writeln!(file, "deed prediction {:?}", bound.deed_prediction.coordinates()).unwrap();
    writeln!(file, "apparatus prediction {:?}", bound.apparatus_prediction).unwrap();
    writeln!(file, "admission {:?}", bound.admission).unwrap();
    writeln!(file, "graph {:?} intended {:?}", graph, intended).unwrap();
    writeln!(file, "census before {census_before:?}").unwrap();
    writeln!(file, "census after  {census_after:?}").unwrap();
    writeln!(file, "wall {:.3} s · cpu ticks {} · utilization samples {:?}", wall.as_secs_f64(), ticks_after - ticks_before, samples).unwrap();
    writeln!(file, "traffic {:?}", bound.traffic).unwrap();
    for (front, deed_front) in bound.fronts().iter().zip(&returned.fronts) {
        writeln!(file, "front depth {} members {:?} certificate {:?} cover {:?} predicted {:?}", front.depth, front.members, front.certificate.coherence, front.cover, front.predicted.coordinates()).unwrap();
        for reading in &deed_front.readings {
            writeln!(file, "    {} bound {} needed {} measured {:?}", reading.operation, reading.bound, reading.needed, reading.measured).unwrap();
        }
        for coupling in &deed_front.couplings {
            writeln!(file, "    coupling {} kernel {} extent {} block {} written {} octave {} width {} refused {} reach {} predicted {:?}", coupling.plan.coupling, coupling.plan.kernel, coupling.plan.extent, coupling.plan.block, coupling.written, coupling.measured_octave, coupling.measured_width, coupling.refused, coupling.reach, coupling.plan.predicted.coordinates()).unwrap();
        }
    }
    writeln!(file, "source/runtime chi:").unwrap();
    for line in &chi_lines {
        writeln!(file, "{line}").unwrap();
    }
    writeln!(file, "terminal face ({} coordinates, {} = tokens x 2560):", terminal.len(), resident_layer::LAYER_RETURN).unwrap();
    for (at, (l, h)) in terminal.iter().enumerate() {
        writeln!(file, "  {at} {l} {h}").unwrap();
    }
    writeln!(file, "falsifiers:").unwrap();
    for line in &verdicts.lines {
        writeln!(file, "{line}").unwrap();
    }
    println!("\nreceipt: {path}");
    let _ = &founded;
    if verdicts.failed > 0 {
        println!("\n{} falsifier(s) FAILED", verdicts.failed);
        std::process::exit(1);
    }
    println!("\nevery attempted falsifier returned PASS; the OPEN ones are named with why");
}

fn rat_f64(value: &Rat) -> f64 {
    // A display face only, never a carrier: the exact value stays in the receipt as its words.
    let scaled = value * Rat::from_integer(BigInt::from(1u64 << 60));
    let integer = scaled.floor().to_integer();
    let approx: f64 = integer.to_string().parse::<f64>().unwrap_or(0.0);
    approx / (1u64 << 60) as f64
}

/// The serial reference of the whole deed — the same source law, on the serial chart, at 2^-96.
fn serial_layer(
    serial: &Serial,
    source: &mut Source,
    tokens: &[usize],
    layer_scalar: Dyadic,
    scales: &(holonic_engine::resident_section::DyadicEnclosure, holonic_engine::resident_section::DyadicEnclosure),
    terms: usize,
) -> Result<Vec<serial_reference::Iv>, String> {
    use resident_layer::*;
    let rows = tokens.len();
    let eps = Dyadic::of_binary64_bits(EPS_BITS).map_err(|e| e.to_string())?;
    let c1 = Dyadic::of_binary64_bits(GELU_SCALE_BITS).map_err(|e| e.to_string())?;
    let c2 = Dyadic::of_binary64_bits(GELU_CUBIC_BITS).map_err(|e| e.to_string())?;
    let mut entering = Vec::new();
    let mut per_layer = Vec::new();
    for token in tokens {
        let (row, _) = source.container.read_rows_bf16(&mut source.file, EMBED, *token, 1).map_err(|e| e.to_string())?;
        entering.extend(row);
        let (row, _) = source.container.read_rows_bf16(&mut source.file, PLE_EMBED, *token, 1).map_err(|e| e.to_string())?;
        per_layer.extend_from_slice(&row[LAYER * PLE_WIDTH..(LAYER + 1) * PLE_WIDTH]);
    }
    let (ple_proj_words, _) = source.container.read_rows_bf16(&mut source.file, PLE_MODEL_PROJECTION, PLE_WIDTH * LAYER, PLE_WIDTH).map_err(|e| e.to_string())?;
    let mut whole = |name: &str| -> Result<Vec<u16>, String> { source.container.read_bf16_whole(&mut source.file, name).map_err(|e| e.to_string()) };
    let x0 = serial.enter(&entering, EMBED_SCALE)?;
    let proj = serial.contract(&x0, rows, HIDDEN, &ple_proj_words, PLE_WIDTH)?;
    let proj = serial.scale(&proj, scales.0);
    let ple_norm_words = whole(PLE_PROJECTION_NORM)?;
    let proj = serial.rms(&proj, PLE_WIDTH, Some(&ple_norm_words), eps)?;
    let tok = serial.enter(&per_layer, PLE_EMBED_SCALE)?;
    let ple = serial.scale(&serial.re_entry(&proj, &tok), scales.1);
    let g = |suffix: &str| named(suffix);
    let h = serial.rms(&x0, HIDDEN, Some(&whole(&g("input_layernorm.weight"))?), eps)?;
    let q = serial.contract(&h, rows, HIDDEN, &whole(&g("self_attn.q_proj.weight"))?, HEADS * HEAD_WIDTH)?;
    let k = serial.contract(&h, rows, HIDDEN, &whole(&g("self_attn.k_proj.weight"))?, KV_HEADS * HEAD_WIDTH)?;
    let v = serial.contract(&h, rows, HIDDEN, &whole(&g("self_attn.v_proj.weight"))?, KV_HEADS * HEAD_WIDTH)?;
    let qn = serial.rms(&q, HEAD_WIDTH, Some(&whole(&g("self_attn.q_norm.weight"))?), eps)?;
    let kn = serial.rms(&k, HEAD_WIDTH, Some(&whole(&g("self_attn.k_norm.weight"))?), eps)?;
    let vn = serial.rms(&v, HEAD_WIDTH, None, eps)?;
    let qr = serial.chronology(&qn, rows, HEADS, HEAD_WIDTH, ROPE_THETA, terms)?;
    let kr = serial.chronology(&kn, rows, KV_HEADS, HEAD_WIDTH, ROPE_THETA, terms)?;
    let c = serial.contact(&qr, &kr, &vn, rows, HEADS, KV_HEADS, HEAD_WIDTH, SLIDING_WINDOW, terms)?;
    let o = serial.contract(&c, rows, HEADS * HEAD_WIDTH, &whole(&g("self_attn.o_proj.weight"))?, HIDDEN)?;
    let on = serial.rms(&o, HIDDEN, Some(&whole(&g("post_attention_layernorm.weight"))?), eps)?;
    let r1 = serial.re_entry(&x0, &on);
    let h2 = serial.rms(&r1, HIDDEN, Some(&whole(&g("pre_feedforward_layernorm.weight"))?), eps)?;
    let gate = serial.contract(&h2, rows, HIDDEN, &whole(&g("mlp.gate_proj.weight"))?, FFN)?;
    let up = serial.contract(&h2, rows, HIDDEN, &whole(&g("mlp.up_proj.weight"))?, FFN)?;
    let gated = serial.gelu(&gate, c1, c2, terms)?;
    let admitted = serial.hadamard(&gated, &up);
    let down = serial.contract(&admitted, rows, FFN, &whole(&g("mlp.down_proj.weight"))?, HIDDEN)?;
    let dn = serial.rms(&down, HIDDEN, Some(&whole(&g("post_feedforward_layernorm.weight"))?), eps)?;
    let r2 = serial.re_entry(&r1, &dn);
    let pg = serial.contract(&r2, rows, HIDDEN, &whole(&g("per_layer_input_gate.weight"))?, PLE_WIDTH)?;
    let pga = serial.gelu(&pg, c1, c2, terms)?;
    let pm = serial.hadamard(&pga, &ple);
    let pp = serial.contract(&pm, rows, PLE_WIDTH, &whole(&g("per_layer_projection.weight"))?, HIDDEN)?;
    let ppn = serial.rms(&pp, HIDDEN, Some(&whole(&g("post_per_layer_input_norm.weight"))?), eps)?;
    let r3 = serial.re_entry(&r2, &ppn);
    Ok(serial.scale(&r3, resident_layer::point_enclosure(layer_scalar)))
}

#[allow(dead_code)]
fn _unused(_: BTreeMap<String, String>, _: OccurrencePort, _: EventId, _: &SourceRefusal) {}
