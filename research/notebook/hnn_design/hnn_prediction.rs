//! **`hnn_prediction`: native generation on known-truth terrain and on text** (THE_REBUILD U6;
//! Brandon, September 29; #73, #148, #63). The pins are
//! `research/records/2026-09-29_NATIVE_GENERATION_PINNED_BEFORE_ITS_RUNS.md` and, for the certified
//! step's runs (`moire 4`, `moire 8`, `copy`, `develop text`),
//! `research/records/2026-09-29_THE_CERTIFIED_DEPOSITION_STEP_PINNED_BEFORE_ITS_RUNS.md`, each
//! committed before any measured run; a committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- probe copy
//! cargo run --release -p holonics --example hnn_prediction -- probe moire
//! cargo run --release -p holonics --example hnn_prediction -- probe text .local/cuts/curated-u6-passage-cut.bin
//! cargo run --release -p holonics --example hnn_prediction -- copy
//! cargo run --release -p holonics --example hnn_prediction -- moire [K]
//! cargo run --release -p holonics --example hnn_prediction -- divergence
//! cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-native-sections.txt
//! cargo run --release -p holonics --example hnn_prediction -- develop copy|moire <train> <evaluate> [s] [batch] [d] [K]
//! cargo run --release -p holonics --example hnn_prediction -- develop text <cut> <train> [s]
//! ```
//!
//! [definition; agent-inferred, the record's pins] **What it executes.**
//! - **The field** (`declare`): three rings of one period `d = 32` in a chain `0 — 1 — 2`, joined
//!   node to node on every node at exponent 0 (`G_a = Y_a`), ring 0 the source and the receiving
//!   ring (its lock every port, so it steps once a cell and the port chart does not enter), rings 1
//!   and 2 stepping only by carries; no pair offset (no window on the source); the receiver's grain
//!   `L_R = 16`; its aperture `K·w + 1`, so the word's precisions by rule cover the refinement's
//!   junction steps. The refinement is `K = 2` words of `w = 1` tick; its diamond does not reach
//!   ring 1's element or anything of ring 2, so the unreached check is exercised.
//! - **The constitution** is `Constitution::initial` at campaign 1's factor step `η_x = ½`, the normal
//!   laws' steps certified at every deposit (the declared `γ_U = 1` was retired September 29):
//!   `R = 0`, `E` the declared sign sequence, nothing authored for a terrain. Everything a terrain's
//!   answer needs is located by the field's own refinement and deposition.
//! - **Development** (`develop`) reads the terrains at development seeds only (never the pinned
//!   ones) and the text's choosing pairs only; it chose `d`, `K`, the batch and the steps before the
//!   pins (the record's development table).
//! - **Learning** (`hnn::prediction::{stage, deposit_of}`): each request is ingested from rest into
//!   its own moment, refined, compared with its target at every station, its covector pulled back
//!   through the words and composed; a batch of requests is deposited at one commit.
//! - **The checks, on every refinement**: the refinement's balance closes, the adjoint pairing holds
//!   on the executed charts, every locus outside the refinement's diamond is unchanged by the
//!   deposit, the balance closes across the commit, and each release's width is read.
//! - **Known truth.** `copy`: requests of `n` symbols drawn uniformly from `|A| − 1` symbols, the
//!   target the request itself (below the moment's capacity); `moire`: one pinned moiré's emission,
//!   a request its window of `n` cells at an offset, the target the next `m` cells. Each is scored by
//!   how many released sections equal their truth exactly.
//! - **Text.** Requests and responses are the curated passage's request relations (the human part a
//!   response answers, and the response's first `m` bytes, a termination where it ends); training
//!   reads the choosing role only, the earliest pairs up to the pin's bound; the eight generated
//!   sections answer the validation requests F0's rule selects (`RELEASE_SEED`), each written whole
//!   to an owner-only file with nothing beside it. A plural section is held (a typed refusal); no
//!   keyed latent is tried (retired September 29). Every cut is refused unless it names the reserve
//!   as excluded (`exterior`).
//! - **The certified step** (September 29; `hnn::constitution`, "The certified step"): the normal
//!   laws' steps are certified at every deposit; the readout prints each locus's certified steps
//!   `2^k` (the least and largest `k`), the largest absolute entry of every learned map (`E`, `R`,
//!   each `W_c`) over the run and after each of the first eight deposits, and the committed energy
//!   bound read on every refinement at its commit (`RefinementBalance::energy_bound`) with the
//!   certified storage growth's product. `s` now scales only the factor families' `η_x = 1/(2s)`.
//! - **Guards**: the run stops at its deadline (the pin's projection bound) or at its resident cap,
//!   and reports its partial evidence as incomplete. `train <pairs>` and `passes <n>` bound the text
//!   run's training below the pinned 1,024 pairs and 2 passes (a bounded reading, reported as such).
//!   The founded chart (`founding <cut>`) was retired September 29 with the passage's founding
//!   (the lessons record; `96d8940b`): every field reads the declared residue chart.

#[path = "exterior.rs"]
mod exterior;

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::{SectionChart, StopPrior};
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::chart::Charts;
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Steps};
use holonics::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration,
    ReceiverDeclaration, RingDeclaration,
};
use holonics::hnn::moment::SourceMoment;
use holonics::hnn::prediction::{Refinement, Section, deposit_of, stage, unreached_unchanged};
use holonics::hnn::word::PowerForm;
use holonics::holarchy::terrain::Draw;
use holonics::holarchy::terrain::moire::{Moire, MoireClass, MoireFamily};
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use holonics::ratio::{Rat, rat};
use holonics::receiver::population::RelationKind;
use num_traits::{Signed, Zero};

use exterior::{
    RESERVE_SHA256, read_curated, read_incidence, reading_of, reserve_read, resident_set,
};

/// The receiver's code tolerance: campaign 1's `1/16` bit, so `L_R = 16`.
const TOLERANCE: (i64, i64) = (1, 16);
/// The declared population, above every declared field's capacity `n*`.
const POPULATION: u64 = 1 << 16;
/// The run's deadline (the pin's projection bound) and its resident cap.
/// Training stops here (the pin: evaluation and generation fit in the rest of the ten minutes).
const DEADLINE_MS: u128 = 540_000;
const RESIDENT_CAP: u128 = 20_000_000_000;

/// The text releases (F0's rule, as U6 item 2 read it): how many, and the seed of their keys.
const RELEASES: usize = 8;
const RELEASE_SEED: u64 = 20_260_929;
/// The curated chart's agent channel.
const AGENT: usize = 1;

/// [definition] **A run's declaration** (the record's pins).
#[derive(Clone, Copy, Debug)]
struct Declared {
    /// `d`: every ring's period.
    period: u64,
    /// `s`: the factor families' declared step `η_x = 1/(2s)` (campaign 1 at `s = 1`); the normal
    /// laws' steps are certified.
    steps: i64,
    /// `|A|`: the exterior chart, its last class the termination.
    alphabet: usize,
    /// `K` and `w`.
    words: usize,
    span: usize,
    /// `m`.
    stations: usize,
    /// Requests a deposit.
    batch: usize,
}

/// **The field** (module header).
fn declare(declared: &Declared) -> Field {
    let d = declared.period;
    let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
    let ring = |lock: Vec<u64>| RingDeclaration {
        period: d,
        screw: axis.clone(),
        placements: (0..d)
            .map(|node| FieldDeclaration::quarter_turn(node, d))
            .collect(),
        lock,
        reflector: (0..d).map(|port| ((d - port) % d) as usize).collect(),
        admittance: Rat::from_integer(2.into()),
        initial: 0,
    };
    let contact = |from: usize, to: usize| ContactDeclaration {
        from,
        to,
        channel: (0..d as usize).map(|node| (node, node)).collect(),
        admittance: Rat::from_integer(2.into()),
        exponent: Rat::from_integer(0.into()),
    };
    Field::declare(
        FieldDeclaration {
            rings: vec![ring((0..d).collect()), ring(Vec::new()), ring(Vec::new())],
            contacts: vec![contact(0, 1), contact(1, 2)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: declared.alphabet,
            step: Rat::from_integer(1.into()),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: declared.words * declared.span + 1,
                tolerance: rat(TOLERANCE.0, TOLERANCE.1),
                depth: 1,
                prior: StopPrior::half(),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: POPULATION,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .expect("the declared field")
}

/// **A request's moment**, ingested from rest (past any carry-out: the moment's own law continues).
fn ingest(field: &Field, request: &[usize]) -> (Current, SourceMoment) {
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < request.len() {
        fed += moment
            .ingest(field, &mut current, &request[fed..])
            .expect("a request in the chart")
            .cells;
    }
    (current, moment)
}

/// [definition] **The checks' tally** over a run: refinements staged, balances closed, pairings
/// checked and held, commits closed, unreached-locus checks and loci checked, releases at width zero
/// and held, and the training code enclosed.
#[derive(Default)]
struct Tally {
    refinements: u64,
    balances: u64,
    pairings: u64,
    pairings_held: u64,
    commits: u64,
    deposits: u64,
    unreached_checks: u64,
    unreached_loci: u64,
    unreached_unchanged: u64,
    released: u64,
    held: u64,
    code: Option<ExactInterval>,
    peak_bits: u64,
    stage_ms: u128,
    deposit_ms: u128,
    /// The committed energy bound read on every refinement at its commit, and how many held.
    energy_checks: u64,
    energy_holds: u64,
    /// Every certified step's exponent `k` (the step `2^k`), by locus: the least and the largest.
    exponents: BTreeMap<String, (i64, i64)>,
    /// The largest absolute entry of each learned map after each deposit (the source port, the
    /// receiving map and every contrast port), the largest over the run, and the first deposits'.
    entries: BTreeMap<String, Rat>,
    trajectory: Vec<Vec<(String, Rat)>>,
    /// The certified storage growth's product since the founding, at the last deposit, and the
    /// least and largest growth `ε_k` of one deposit.
    storage_product: Option<Rat>,
    growths: Option<(Rat, Rat)>,
}

impl Tally {
    fn add_code(&mut self, code: &ExactInterval) {
        self.code = Some(match &self.code {
            Some(total) => interval_sum(total, code).expect("enclosures add"),
            None => code.clone(),
        });
    }
}

/// [definition] **The engine**: the field, the refinement, the constitution, the charts it warms,
/// the diamond, and the tally.
struct Engine {
    field: Field,
    refinement: Refinement,
    theta: Constitution,
    charts: Charts,
    tally: Tally,
}

impl Engine {
    fn new(declared: Declared) -> Self {
        let field = declare(&declared);
        let refinement = Refinement::declare(
            &field,
            0,
            declared.words,
            declared.span,
            declared.stations,
            declared.alphabet - 1,
        )
        .expect("the declared refinement");
        let theta = Constitution::initial(
            &field,
            Steps {
                factor: rat(1, 2 * declared.steps),
            },
            CAMPAIGN_ONE_BUDGET,
        )
        .expect("the initial constitution");
        Self {
            field,
            refinement,
            theta,
            charts: Charts::new(),
            tally: Tally::default(),
        }
    }

    /// **One deposit over a batch**: every request staged with its checks, the batch deposited at
    /// one commit, the unreached loci and every refinement's commit balance checked.
    fn learn(&mut self, batch: &[(Vec<usize>, Vec<usize>)]) {
        let staging = Instant::now();
        let mut composed = Vec::with_capacity(batch.len());
        let mut balances = Vec::with_capacity(batch.len());
        for (request, target) in batch {
            let (current, moment) = ingest(&self.field, request);
            let staged = stage(
                &self.field,
                &self.theta,
                &current,
                &moment,
                &self.refinement,
                target,
                &mut self.charts,
                true,
            )
            .expect("a staged refinement");
            self.tally.refinements += 1;
            self.tally.balances += u64::from(staged.balance.closes());
            if let Some(pairing) = &staged.pairing {
                self.tally.pairings += 1;
                self.tally.pairings_held += u64::from(pairing.holds());
            }
            if staged.release.released() {
                self.tally.released += 1;
            } else {
                self.tally.held += 1;
            }
            self.tally.peak_bits = self.tally.peak_bits.max(staged.peak_bits);
            self.tally
                .add_code(&staged.ratio.code_length().expect("the section's code"));
            balances.push((current, staged.end, staged.balance));
            composed.push(staged.composed);
        }
        self.tally.stage_ms += staging.elapsed().as_millis();
        let depositing = Instant::now();
        let deposit =
            deposit_of(&self.theta, &self.refinement, &composed).expect("the batch's deposit");
        let amplitude = self
            .theta
            .amplitude()
            .expect("the amplitude reads")
            .expect("no pumped resonator on the declared field");
        let (next, reading) = self.theta.deposited(&deposit).expect("the deposit");
        self.tally.deposit_ms += depositing.elapsed().as_millis();
        for (locus, step) in &reading.steps {
            let entry = self
                .tally
                .exponents
                .entry(format!("{locus:?}"))
                .or_insert((step.step.exponent, step.step.exponent));
            entry.0 = entry.0.min(step.step.exponent);
            entry.1 = entry.1.max(step.step.exponent);
        }
        self.tally.storage_product = Some(reading.storage_product.clone());
        let largest = |matrix: &holonics::ratio::linear::ExactRatMatrix| {
            matrix
                .entries()
                .iter()
                .map(|x| x.abs())
                .max()
                .unwrap_or_else(Rat::zero)
        };
        let mut maps: Vec<(String, Rat)> = Vec::new();
        for g in 0..self.field.rings().len() {
            if let Some(port) = next.source_port(g) {
                maps.push((format!("E{g}"), largest(port)));
            }
            if let Some(map) = next.receiving_map(g) {
                maps.push((format!("R{g}"), largest(map)));
            }
            maps.push((format!("Wc{g}"), largest(next.contrast_port(g))));
            maps.push((format!("f{g}"), largest(next.passive_factor(g))));
            let slices = next
                .slices(g)
                .iter()
                .flat_map(|(u, v)| u.iter().chain(v))
                .map(|x| x.abs())
                .max()
                .unwrap_or_else(Rat::zero);
            maps.push((format!("slices{g}"), slices));
            let standing = next
                .standing(g)
                .iter()
                .map(|x| x.abs())
                .max()
                .unwrap_or_else(Rat::zero);
            maps.push((format!("q{g}"), standing));
        }
        for a in 0..self.field.contacts().len() {
            maps.push((format!("c{a}"), largest(next.contact_storage(a))));
            maps.push((format!("b{a}"), largest(next.contact_stiffness(a))));
            maps.push((format!("F{a}"), largest(next.contact_dissipation(a))));
        }
        let growth = self.tally.growths.get_or_insert((
            reading.storage_growth.clone(),
            reading.storage_growth.clone(),
        ));
        if reading.storage_growth < growth.0 {
            growth.0 = reading.storage_growth.clone();
        }
        if reading.storage_growth > growth.1 {
            growth.1 = reading.storage_growth.clone();
        }
        for (name, value) in &maps {
            let kept = self
                .tally
                .entries
                .entry(name.clone())
                .or_insert_with(Rat::zero);
            if value > kept {
                *kept = value.clone();
            }
        }
        if self.tally.trajectory.len() < 8 {
            self.tally.trajectory.push(maps);
        }
        let (loci, unchanged) = unreached_unchanged(
            &self.field,
            &self.theta,
            &next,
            &self.refinement.diamond(&self.field),
        );
        self.tally.unreached_checks += 1;
        self.tally.unreached_loci += loci as u64;
        self.tally.unreached_unchanged += u64::from(unchanged);
        for (current, end, mut balance) in balances {
            let before = PowerForm::read(&self.field, &self.theta, &current).expect("a form");
            let after = PowerForm::read(&self.field, &next, &current).expect("a form");
            balance
                .commit(&before, &after, &end)
                .expect("the commit's work");
            self.tally.commits += u64::from(balance.closes());
            let bound = balance
                .energy_bound(
                    &self.refinement,
                    &amplitude,
                    &reading.storage_growth,
                    self.field.word_lattice(),
                )
                .expect("the committed energy bound");
            self.tally.energy_checks += 1;
            self.tally.energy_holds += u64::from(bound.holds);
        }
        self.tally.deposits += 1;
        self.theta = next;
        if self.tally.deposits.is_multiple_of(16) {
            eprintln!(
                "  progress: deposits {}, stage {} ms, deposit {} ms, peak bits {}, released {} held {}",
                self.tally.deposits,
                self.tally.stage_ms,
                self.tally.deposit_ms,
                self.tally.peak_bits,
                self.tally.released,
                self.tally.held
            );
        }
    }

    /// **A generated section**: refined at rest and released at width zero, or held (a plural
    /// section is a typed refusal, never retried).
    fn generate(&mut self, request: &[usize]) -> (Vec<usize>, bool) {
        let (current, moment) = ingest(&self.field, request);
        let section = Section::refine(
            &self.field,
            &self.theta,
            &current,
            &moment,
            &self.refinement,
            &mut self.charts,
        )
        .expect("a refined section");
        let release = section.release().expect("the section's release");
        if release.released() {
            (release.classes, true)
        } else {
            (Vec::new(), false)
        }
    }

    fn report(&self, label: &str) {
        let t = &self.tally;
        println!(
            "  {label}: refinements {}, balances closed {} of {}, pairings exact {} of {}, commits closed {} of {}, deposits {}, unreached checks {} ({} loci in all, every one unchanged in {} of {}), released at width zero {} and held {}, peak state bits {}",
            t.refinements,
            t.balances,
            t.refinements,
            t.pairings_held,
            t.pairings,
            t.commits,
            t.refinements,
            t.deposits,
            t.unreached_checks,
            t.unreached_loci,
            t.unreached_unchanged,
            t.unreached_checks,
            t.released,
            t.held,
            t.peak_bits
        );
        if let Some(code) = &t.code {
            println!(
                "  the training sections' code, Σ_j −log₂ p̂_j(t_j): {}",
                reading_of(code, 16)
            );
        }
        println!(
            "  the committed energy bound held at {} of {} refinements' commits; the certified storage growth's product since the founding {}",
            t.energy_holds,
            t.energy_checks,
            t.storage_product
                .as_ref()
                .map_or_else(|| "none".to_string(), ToString::to_string)
        );
        if let Some((least, largest)) = &t.growths {
            println!(
                "  the certified storage growth ε_k of one deposit: from {least} to {largest}"
            );
        }
        for (locus, (least, largest)) in &t.exponents {
            println!("  certified steps at {locus}: 2^k for k from {least} to {largest}");
        }
        for (name, value) in &t.entries {
            println!("  the largest absolute entry of {name} over the run: {value}");
        }
        for (deposit, maps) in t.trajectory.iter().enumerate() {
            println!(
                "  after deposit {}: {}",
                deposit + 1,
                maps.iter()
                    .map(|(name, value)| format!("{name} {value}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    }
}

/// The resident set at its peak against the cap, and the deadline.
fn guarded(clock: &Instant) -> bool {
    let within_time = clock.elapsed().as_millis() < DEADLINE_MS;
    let within_memory = resident_set().is_none_or(|(_, peak)| peak < RESIDENT_CAP);
    within_time && within_memory
}

fn resident() -> String {
    resident_set().map_or_else(|| "unread".to_string(), |(now, peak)| format!("{now} now, {peak} peak"))
}

// -------------------------------------------------------------------------------------------
// the known-truth terrains

/// **The copy terrain** (module header): `n` symbols drawn uniformly from `|A| − 1`, the target the
/// request itself.
fn copy_pairs(declared: &Declared, seed: u64, count: usize) -> Vec<(Vec<usize>, Vec<usize>)> {
    let mut draw = Draw::new(seed);
    (0..count)
        .map(|_| {
            let request: Vec<usize> = (0..declared.stations)
                .map(|_| draw.below(declared.alphabet - 1))
                .collect();
            (request.clone(), request)
        })
        .collect()
}

/// **The moiré terrain** (module header): windows of `n` cells at drawn offsets and the next `m`.
fn moire_pairs(
    moire: &Moire,
    declared: &Declared,
    seed: u64,
    count: usize,
) -> Vec<(Vec<usize>, Vec<usize>)> {
    let n = declared.stations;
    let period = moire.truth(&MOIRE_FAMILY).expect("the moiré's truth").least_period;
    let emission = moire.emit(period + 2 * n);
    let mut draw = Draw::new(seed);
    (0..count)
        .map(|_| {
            let offset = draw.below(period);
            (
                emission[offset..offset + n].to_vec(),
                emission[offset + n..offset + 2 * n].to_vec(),
            )
        })
        .collect()
}

/// Every distinct window of the moiré: one per offset below its least period.
fn moire_windows(moire: &Moire, declared: &Declared) -> Vec<(Vec<usize>, Vec<usize>)> {
    let n = declared.stations;
    let period = moire.truth(&MOIRE_FAMILY).expect("the moiré's truth").least_period;
    let emission = moire.emit(period + 2 * n);
    (0..period)
        .map(|offset| {
            (
                emission[offset..offset + n].to_vec(),
                emission[offset + n..offset + 2 * n].to_vec(),
            )
        })
        .collect()
}

const MOIRE_FAMILY: MoireFamily = MoireFamily {
    rings: 2,
    denominator: 3,
};

/// **The terrains' declaration** (the record's pins).
fn terrain_declared() -> Declared {
    Declared {
        period: 32,
        steps: 1,
        alphabet: 5,
        words: 2,
        span: 1,
        stations: 8,
        batch: 16,
    }
}

/// The pins of a terrain run: training requests, the seeds, and the evaluation.
const COPY_TRAIN: usize = 1536;
const MOIRE_TRAIN: usize = 512;
const TRAIN_SEED: u64 = 2_026_092_901;
const EVALUATE: usize = 256;
const EVALUATE_SEED: u64 = 2_026_092_902;
const MOIRE_SEED: u64 = 2_026_092_903;

/// **A terrain run**: train over the pinned pairs in batches within the guards, then evaluate each
/// held-out pair's released section against its truth.
fn terrain(
    name: &str,
    declared: Declared,
    train: Vec<(Vec<usize>, Vec<usize>)>,
    evaluate: Vec<(Vec<usize>, Vec<usize>)>,
) {
    let clock = Instant::now();
    let mut engine = Engine::new(declared);
    println!(
        "hnn_prediction {name}: d = {}, |A| = {} (termination {}), K = {}, w = {}, m = {}, batch {}, steps 1/{}, n* = {}, training pairs {}, evaluated {}",
        declared.period,
        declared.alphabet,
        declared.alphabet - 1,
        declared.words,
        declared.span,
        declared.stations,
        declared.batch,
        declared.steps,
        engine.field.capacity().n_star(),
        train.len(),
        evaluate.len()
    );
    let mut complete = true;
    for batch in train.chunks(declared.batch) {
        if !guarded(&clock) {
            complete = false;
            break;
        }
        engine.learn(batch);
    }
    let trained = clock.elapsed().as_millis();
    engine.report("training");
    println!(
        "  training {} ms{}; resident {}",
        trained,
        if complete { "" } else { ", stopped at a guard: INCOMPLETE" },
        resident()
    );
    let mut exact = 0usize;
    let mut released = 0usize;
    let mut stations_right = 0usize;
    for (request, truth) in &evaluate {
        let (classes, was_released) = engine.generate(request);
        if was_released {
            released += 1;
            stations_right += classes.iter().zip(truth).filter(|(a, b)| a == b).count();
            exact += usize::from(&classes == truth);
        }
    }
    println!(
        "  evaluation: sections released at width zero {released} of {}; exact T(x) {exact} of {}; stations right {stations_right} of {}; {} ms in all",
        evaluate.len(),
        evaluate.len(),
        evaluate.len() * declared.stations,
        clock.elapsed().as_millis()
    );
}

// -------------------------------------------------------------------------------------------
// text

/// **The text declaration** (the record's pins): `|A| = 257`, the bytes and a termination.
fn text_declared() -> Declared {
    Declared {
        period: 32,
        steps: 1,
        alphabet: 257,
        words: 2,
        span: 1,
        stations: 32,
        batch: 16,
    }
}

/// The bytes of the part opened at letter `tick`, up to the next section letter.
fn part(codes: &[usize], chart: &SectionChart, tick: usize) -> Vec<usize> {
    codes[tick + 1..]
        .iter()
        .take_while(|&&code| chart.section(code).is_none())
        .copied()
        .collect()
}

/// A response's first `m` bytes, the termination where it ends and after.
fn target_of(response: &[usize], stations: usize, termination: usize) -> Vec<usize> {
    (0..stations)
        .map(|j| response.get(j).copied().unwrap_or(termination))
        .collect()
}

/// **The pinned bound on the choosing pairs** read in training.
const TEXT_TRAIN: usize = 1024;
/// **The pinned passes** over the choosing pairs.
const TEXT_PASSES: usize = 2;

/// [definition] **The text passage read for the run**: the choosing role's request pairs (the
/// request's bytes and the response's target), every eligible count, and the validation requests
/// F0's rule selects (their letter ticks and request bytes).
struct TextPassage {
    cells: usize,
    development: usize,
    eligible: usize,
    train: Vec<(Vec<usize>, Vec<usize>)>,
    validation_eligible: usize,
    selected: Vec<(usize, Vec<usize>)>,
}

fn text_passage(cut_path: &str, declared: &Declared, bound: usize, validation: bool) -> TextPassage {
    let chart = SectionChart::curated();
    let cut = read_curated(cut_path, &chart);
    let relations = read_incidence(cut_path);
    let development = cut.held.start;
    let termination = declared.alphabet - 1;
    let codes = &cut.codes;
    let opens_agent = |tick: usize| {
        chart
            .section(codes[tick])
            .is_some_and(|section| section.channel == AGENT)
    };
    // The choosing role's request relations, in letter order.
    let mut choosing: Vec<(usize, usize)> = relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Request)
        .filter_map(|relation| {
            let (letter, target) = (relation.letter as usize, relation.target as usize);
            (letter < development && target < letter && opens_agent(letter))
                .then_some((letter, target))
        })
        .filter(|&(letter, target)| {
            !part(codes, &chart, letter).is_empty() && !part(codes, &chart, target).is_empty()
        })
        .collect();
    choosing.sort_unstable();
    let eligible = choosing.len();
    choosing.truncate(bound);
    let train: Vec<(Vec<usize>, Vec<usize>)> = choosing
        .iter()
        .map(|&(letter, target)| {
            (
                part(codes, &chart, target),
                target_of(&part(codes, &chart, letter), declared.stations, termination),
            )
        })
        .collect();
    // The validation requests F0's rule selects.
    // The validation role is read only by the run, never by the probe.
    let mut selected: Vec<(u64, usize, usize)> = if !validation { Vec::new() } else { relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Request)
        .filter_map(|relation| {
            let (letter, target) = (relation.letter as usize, relation.target as usize);
            let nonempty = |at: usize| codes.get(at + 1).is_some_and(|&c| chart.section(c).is_none());
            (letter >= development
                && target >= development
                && target < letter
                && opens_agent(letter)
                && nonempty(letter)
                && nonempty(target)
                && (cut.population as usize) > letter + 2)
                .then(|| {
                    (
                        Draw::new(RELEASE_SEED.wrapping_add((letter - development) as u64)).next(),
                        letter,
                        target,
                    )
                })
        })
        .collect() };
    let validation_eligible = selected.len();
    selected.sort_unstable();
    selected.truncate(RELEASES);
    TextPassage {
        cells: codes.len(),
        development,
        eligible,
        train,
        validation_eligible,
        selected: selected
            .into_iter()
            .map(|(_, letter, target)| (letter - development, part(codes, &chart, target)))
            .collect(),
    }
}

#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn text(cut_path: &str, out_path: &str, bound: usize, passes: usize) {
    let clock = Instant::now();
    let declared = text_declared();
    let termination = declared.alphabet - 1;
    let TextPassage {
        cells,
        development,
        eligible,
        train,
        validation_eligible,
        selected,
    } = text_passage(cut_path, &declared, bound, true);
    let mut engine = Engine::new(declared);
    println!(
        "hnn_prediction text: the passage {cells} cells, the choosing role's first {development}; choosing request pairs {eligible}, trained on the first {}; validation eligible {validation_eligible}, released {}; d = {}, |A| = {}, K = {}, w = {}, m = {}, batch {}; reserve excluded {}",
        train.len(),
        selected.len(),
        declared.period,
        declared.alphabet,
        declared.words,
        declared.span,
        declared.stations,
        declared.batch,
        if reserve_read() { "NO (--read-reserve)" } else { RESERVE_SHA256 }
    );
    let mut complete = true;
    'passes: for _ in 0..passes {
        for batch in train.chunks(declared.batch) {
            if !guarded(&clock) {
                complete = false;
                break 'passes;
            }
            engine.learn(batch);
        }
    }
    engine.report("training");
    println!(
        "  training ({passes} passes) {} ms{}; resident {}",
        clock.elapsed().as_millis(),
        if complete { "" } else { ", stopped at a guard: INCOMPLETE" },
        resident()
    );
    let mut written = String::new();
    for (order, (letter, request)) in selected.iter().enumerate() {
        let start = Instant::now();
        let (classes, released) = engine.generate(request);
        let bytes: Vec<u8> = classes
            .iter()
            .take_while(|&&class| class != termination)
            .map(|&class| u8::try_from(class).expect("a byte class"))
            .collect();
        let utf8 = std::str::from_utf8(&bytes).is_ok();
        println!(
            "  section {order} (validation letter {letter}, request {} bytes): {}, {} bytes, UTF-8 {utf8}, {} ms",
            request.len(),
            if released { "released" } else { "held (typed refusal)" },
            bytes.len(),
            start.elapsed().as_millis()
        );
        written.push_str(&format!(
            "section {order}: {}\n{}\n\n",
            if released { "released" } else { "held" },
            String::from_utf8_lossy(&bytes)
        ));
    }
    std::fs::write(out_path, written).expect("write the sections, owner-only");
    println!("  the sections are written whole to the owner-only file; {} ms in all", clock.elapsed().as_millis());
}

// -------------------------------------------------------------------------------------------
// the probe

/// **The probe**: a bounded dry run of one mode's engine, its milliseconds a refinement and a
/// deposit and its resident set, from which the pinned run is projected.
fn probe(mode: &str, cut: Option<&str>) {
    let clock = Instant::now();
    let (declared, pairs) = match mode {
        "copy" => (terrain_declared(), copy_pairs(&terrain_declared(), 1, 32)),
        "moire" => {
            let moire = Moire::draw(&MOIRE_FAMILY, MoireClass::Sheets, &mut Draw::new(MOIRE_SEED))
                .expect("the moiré");
            (terrain_declared(), moire_pairs(&moire, &terrain_declared(), 1, 32))
        }
        "text" => {
            let declared = text_declared();
            let passage = text_passage(cut.expect("a passage cut"), &declared, 32, false);
            (declared, passage.train)
        }
        other => panic!("probe copy | moire | text, not {other}"),
    };
    let mut engine = Engine::new(declared);
    let built = clock.elapsed().as_millis();
    let start = Instant::now();
    for batch in pairs.chunks(declared.batch) {
        engine.learn(batch);
    }
    let learned = start.elapsed().as_millis();
    let start = Instant::now();
    let _ = engine.generate(&pairs[0].0);
    let generated = start.elapsed().as_millis();
    engine.report("probe");
    println!(
        "hnn_prediction probe {mode}: setup {built} ms; {} refinements in {} deposits {learned} ms ({} ms a refinement with its deposit share); one generation {generated} ms; resident {}",
        engine.tally.refinements,
        engine.tally.deposits,
        learned / u128::from(engine.tally.refinements.max(1)),
        resident()
    );
}

fn main() {
    let arguments = exterior::admit_reserve_flag(std::env::args().collect());
    match arguments.get(1).map(String::as_str) {
        Some("probe") => probe(
            arguments.get(2).map(String::as_str).expect("a mode"),
            arguments.get(3).map(String::as_str),
        ),
        // Development reads before the pins: the terrain at development seeds (never the pinned
        // training or evaluation seeds) and counts given on the command line.
        Some("develop") => {
            let mut declared = terrain_declared();
            if let Some(steps) = arguments.get(5).and_then(|value| value.parse().ok()) {
                declared.steps = steps;
            }
            if let Some(batch) = arguments.get(6).and_then(|value| value.parse().ok()) {
                declared.batch = batch;
            }
            if let Some(period) = arguments.get(7).and_then(|value| value.parse().ok()) {
                declared.period = period;
            }
            if let Some(words) = arguments.get(8).and_then(|value| value.parse().ok()) {
                declared.words = words;
            }
            let count = |at: usize| -> usize {
                arguments
                    .get(at)
                    .and_then(|value| value.parse().ok())
                    .expect("a count")
            };
            match arguments.get(2).map(String::as_str) {
                Some("copy") => terrain(
                    "develop copy",
                    declared,
                    copy_pairs(&declared, 11, count(3)),
                    copy_pairs(&declared, 12, count(4)),
                ),
                Some("moire") => {
                    let moire =
                        Moire::draw(&MOIRE_FAMILY, MoireClass::Sheets, &mut Draw::new(13))
                            .expect("the moiré");
                    terrain(
                        "develop moire",
                        declared,
                        moire_pairs(&moire, &declared, 14, count(3)),
                        moire_windows(&moire, &declared),
                    );
                }
                // Text: the choosing role's pairs only; the validation role is never read here.
                Some("text") => {
                    let mut declared = text_declared();
                    if let Some(steps) = arguments.get(5).and_then(|value| value.parse().ok()) {
                        declared.steps = steps;
                    }
                    let passage = text_passage(
                        arguments.get(3).map(String::as_str).expect("the passage cut"),
                        &declared,
                        count(4),
                        false,
                    );
                    let clock = Instant::now();
                    let mut engine = Engine::new(declared);
                    for batch in passage.train.chunks(declared.batch) {
                        if !guarded(&clock) {
                            break;
                        }
                        engine.learn(batch);
                    }
                    engine.report("develop text");
                    println!("  {} ms; resident {}", clock.elapsed().as_millis(), resident());
                }
                _ => panic!("develop copy | moire <train> <evaluate> | text <cut> <train>"),
            }
        }
        Some("copy") => {
            let declared = terrain_declared();
            terrain(
                "copy",
                declared,
                copy_pairs(&declared, TRAIN_SEED, COPY_TRAIN),
                copy_pairs(&declared, EVALUATE_SEED, EVALUATE),
            );
        }
        Some("moire") => {
            // `moire [K]`: the pinned moiré at `K` words (the pins of September 29 took `K = 2`;
            // the certified step's pins read `K = 4` and `K = 8`).
            let mut declared = terrain_declared();
            if let Some(words) = arguments.get(2).and_then(|value| value.parse().ok()) {
                declared.words = words;
            }
            let moire = Moire::draw(&MOIRE_FAMILY, MoireClass::Sheets, &mut Draw::new(MOIRE_SEED))
                .expect("the moiré");
            let truth = moire.truth(&MOIRE_FAMILY).expect("the moiré's truth");
            println!(
                "  the moiré: {} gratings, joint period {}, least period {}, determining depth {}",
                moire.gratings().len(),
                truth.joint_period,
                truth.least_period,
                truth.depth
            );
            terrain(
                "moire",
                declared,
                moire_pairs(&moire, &declared, TRAIN_SEED, MOIRE_TRAIN),
                moire_windows(&moire, &declared),
            );
        }
        // The development configuration where `K = 4` diverged under the declared step `γ_U = 1`
        // (the native generation pins' development table: `d = 16`, `K = 4`, `s = 1`, batch 8, 128
        // windows at the development seeds; `E`'s entries grew 1, 6, 26, 316), read again under the
        // certified step: development seeds only, never the pinned ones.
        Some("divergence") => {
            let mut declared = terrain_declared();
            declared.period = 16;
            declared.words = 4;
            declared.batch = 8;
            let moire = Moire::draw(&MOIRE_FAMILY, MoireClass::Sheets, &mut Draw::new(13))
                .expect("the moiré");
            terrain(
                "divergence",
                declared,
                moire_pairs(&moire, &declared, 14, 128),
                moire_windows(&moire, &declared),
            );
        }
        Some("text") => {
            let (mut bound, mut passes) = (TEXT_TRAIN, TEXT_PASSES);
            for pair in arguments[4..].chunks(2) {
                match pair {
                    [key, value] if key == "train" => bound = value.parse().expect("pairs"),
                    [key, value] if key == "passes" => passes = value.parse().expect("passes"),
                    _ => panic!("text <cut> <out> [train <pairs>] [passes <n>]"),
                }
            }
            text(
                arguments.get(2).map(String::as_str).expect("the passage cut"),
                arguments.get(3).map(String::as_str).expect("the sections' owner-only file"),
                bound,
                passes,
            )
        }
        _ => panic!(
            "hnn_prediction probe <mode> [cut] | copy | moire | text <cut> <out> [train <pairs>] [passes <n>]"
        ),
    }
}
