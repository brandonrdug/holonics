//! **The egg population on terrain a declared Holarchy made** (rebuild step 4 item 4, #73;
//! `holonics::receiver::population`): a receiver's Bayesian mixture over declared navigator
//! families (the receiving tree at a ladder of depths, a moiré's gratings, a rotor crib's keys),
//! gauged by selecting the family that made the terrain. Count-only **development receipts**, a
//! committed command run once in release, never a test: the conversation cut stays the living
//! substrate and the milestone (Brandon's ruling of August 26), and no claim here is joined to the
//! cut's.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- tree 2
//! cargo run --release -p holonics --example hnn_population -- tree 4
//! cargo run --release -p holonics --example hnn_population -- moire parity
//! cargo run --release -p holonics --example hnn_population -- moire sheets
//! cargo run --release -p holonics --example hnn_population -- crib
//! cargo run --release -p holonics --example hnn_population -- switching [parity | sheets]
//! cargo run --release -p holonics --example hnn_population -- standing .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_population -- composition [products | primes]
//! cargo run --release -p holonics --example hnn_population -- evolution
//! cargo run --release -p holonics --example hnn_population -- species
//! cargo run --release -p holonics --example hnn_population -- birth-probe
//! cargo run --release -p holonics --example hnn_population -- birth
//! cargo run --release -p holonics --example hnn_population -- birth-dimensions
//! cargo run --release -p holonics --example hnn_population -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
//! cargo run --release -p holonics --example hnn_population -- f0-census .local/cuts/curated-f4-passage-cut.bin
//! cargo run --release -p holonics --example hnn_population -- u2-acceptance .local/cuts/curated-u2-passage-cut.bin .local/cuts/curated-u2-passage-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred] **The declared population.** On each terrain the receiver declares
//! the receiving tree (`receiver::population::TreeFamily`: cell-only letters, the `½` stop prior,
//! KT nodes, `n*` the passage, `L_R = 16`) at every depth of the dyadic ladder [`DEPTHS`]
//! (`1, 2, …, 32`, below Decision 37's `48`: the population weighs the depths by Bayes instead of
//! the harness's depth rule), and the key family of the terrain's kind whose alphabet the cells
//! read: the parity color's joint grating keys, the sheet tuple's per-ring grating keys, or a rotor
//! crib's start, key and plugboard. Every family is named by `⌈log₂ F⌉` bits, `F` the declared
//! families, so the Kraft mass is `F · 2^(−⌈log₂ F⌉)` (its unused remainder printed) and the prior is
//! uniform over the declared families. Survivor filtering enumerates at most [`ENUMERATION`] keys
//! (the first cell holds every key's index, 8 bytes each: 128 MiB); a larger key space is refused
//! with the Bombe it is owed to, and the refusal is printed.
//!
//! [definition] **Printed, exactly**, for each terrain: its truth (the source's exact code or rate,
//! the drawn keys and their description); each family's description, prior, death cell (zero
//! likelihood), code alone `−log₂ L_f`, charged code `−log₂(π_f L_f)` and posterior `−log₂ w_f` (an
//! exact zero at death); each key family's surviving keys against the drawn ones; the
//! population's code `−log₂ Σ_f π_f L_f` against the truth; the posterior of each kind; and the
//! selected family (posterior decided above one half) against the family that made the terrain.
//! Bits are enclosures with exact endpoints, read at `L_R = 16` as `n + k/16 + ε`; no decimal is
//! printed.
//!
//! [definition; agent-inferred] **Campaign 3 at the population** (`switching`): on the dormant
//! grating's terrain the receiver declares three populations over the same cells:
//! - **static**: the trees and the static grating family (seven families, `M = 7/8`);
//! - **with dormancy**: the same and the dormant grating family (`receiver::population::DormantFamily`,
//!   each ring a layer under the fixed share at `α = 2^(−j)`, `j = ⌈log₂ n⌉ = 14`: a switch pays
//!   for its position among the passage's cells), eight families of 3 bits, `M = 1`;
//! - **born**: the static population founding the dormant family from its reserved `1/8` at the
//!   first section (every `2^8` cells) whose residual since the previous section passes the
//!   candidate's 3 bits (the opening section only opens the reading: it pays the declared families'
//!   own key location);
//! - **reseeding**: the static population re-founding its dead gratings' seed (the keys they held
//!   when they died) at each section whose residual passes the charge, half the reserved mass a
//!   re-founding.
//!
//! It prints the truth (the switches and their positions), each death's exchange receipt, the
//! dormant ring's survivors, activity and fibre mass at the end of the first aeon, at its return,
//! 64 cells after and at the end, the dormant family's code against its exact bound
//! (`log₂ |K| − log₂ #S_σ` by brute force over the truth's activity path, plus that path's
//! fixed-share code and the certified drift), and every population's code against the unswitched
//! one plus `j` bits a switch and against `log₂ C(n − 1, k)`.
//!
//! [definition] **The standing-cut regression** (`standing <cut>`): the population of trees alone
//! (no grating survives on text) over the standing real cut, prequential, its development and
//! held-out codes against the recorded tree (`D = 4`, `½`, `tree_prequential`).

#[path = "exterior.rs"]
mod exterior;

#[path = "hnn_population_composition.rs"]
mod composition;

#[path = "hnn_population_evolution.rs"]
mod evolution;

#[path = "hnn_population_curated.rs"]
mod curated;

#[path = "hnn_population_census.rs"]
mod census;

#[path = "hnn_population_u2.rs"]
mod u2;

#[path = "hnn_population_birth.rs"]
mod birth;

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior, cell_letters, code_length,
};
use holonics::hnn::Cut;
use holonics::hnn::field::{Field, FieldDeclaration};
use holonics::hnn::reference::tree_prequential;
use holonics::holarchy::terrain::{
    AeonFamily, Draw, Grating, Moire, MoireClass, MoireFamily, RotorCrib, Switching, TreeSource,
    TreeSourceFamily,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{
    ExactInterval, interval_difference, interval_sum, log2_enclosure,
};
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::receiver::population::{
    Candidate, DeathReceipt, DormantFamily, Family, Founding, KeyFamily, KeyReadout, Population,
    PopulationError, PopulationReceipt, Posterior, Readout, Reception, TreeFamily,
};
use num_bigint::{BigInt, BigUint};

use exterior::{against, enclosure, exact, per};

/// The declared seed of every terrain here (the terrain notebook's): its draw's initial
/// configuration.
const SEED: u64 = 20_260_927;

/// The receiver's grain `L_R`.
const GRAIN: u64 = 16;

/// The tree family's depth ladder.
const DEPTHS: [usize; 6] = [1, 2, 4, 8, 16, 32];

/// The declared enumeration: the most keys survivor filtering holds at its first cell (`2^24`
/// indices of 8 bytes, 128 MiB).
const ENUMERATION: u64 = 1 << 24;

/// The tree source's passage `2^16` and its faces' grid `1/16` (the terrain notebook's).
const TREE_CELLS: usize = 1 << 16;
const TREE_GRID: u64 = 16;

/// The moirés' passage `2^14` and rings.
const MOIRE_CELLS: usize = 1 << 14;
const MOIRE_RINGS: usize = 3;

/// The rotor crib's passage `2^10`, its field's population and its ring (campaign 1's period-7
/// ring, locked at every port so it steps every tick).
const CRIB_CELLS: usize = 1 << 10;
const CRIB_POPULATION: u64 = 1 << 16;
const CRIB_RING: usize = 1;

/// The switching terrain's aeons: each `2^10` to `2^11` cells, at least three joint periods of a
/// denominator-`2^3` moiré (`lcm ≤ 8·7·5 = 280`).
const AEONS: AeonFamily = AeonFamily {
    shortest: 1 << 10,
    longest: 1 << 11,
};

/// The recorded tree codes of the terrain notebook's moiré at its determining depth `D*`
/// (the retired `hnn_terrain -- moire`, the audit record's §6.2): parity `993 + 5/16 + ε`, sheets `1549 + 0/16 + ε`.
const RECORDED_PARITY_AT_D_STAR: &str = "993 + 5/16 + ε (D* = 14)";
const RECORDED_SHEETS_AT_D_STAR: &str = "1549 + 0/16 + ε (D* = 8)";

/// **An integer with its factorization**, `n = p^a·q^b…` (read from `log₂ n`'s exact form).
fn factored(value: &BigUint) -> String {
    if value <= &BigUint::from(1u32) {
        return value.to_string();
    }
    let form = SymbolicSurprisal::log2_of_ratio(&Rat::from_integer(BigInt::from(value.clone())))
        .expect("a positive integer");
    let factors: Vec<String> = form
        .terms()
        .iter()
        .map(|(prime, exponent)| {
            if exponent == &Rat::from_integer(BigInt::from(1)) {
                prime.to_string()
            } else {
                format!("{prime}^{exponent}")
            }
        })
        .collect();
    format!("{value} = {}", factors.join("·"))
}

fn point(value: u64) -> ExactInterval {
    ExactInterval::point(Rat::from_integer(BigInt::from(value)))
}

fn on_grid(interval: &ExactInterval) -> ExactInterval {
    interval_sum(interval, &point(0)).expect("an enclosure")
}

/// `log₂ n`, enclosed.
fn log2_of(value: &BigUint) -> ExactInterval {
    log2_enclosure(&Rat::from_integer(BigInt::from(value.clone()))).expect("a positive integer")
}

/// `⌈log₂ F⌉`, the bits naming one of `F` declared families.
fn naming_bits(families: usize) -> u64 {
    (usize::BITS - (families - 1).leading_zeros()) as u64
}

fn tree_declaration(alphabet: usize, depth: usize, population: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: population as u64,
        grain: GRAIN,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

/// The declared population: the tree at every depth of the ladder, then the key family built with
/// its description; each family named by `⌈log₂ F⌉` bits.
fn declare(
    alphabet: usize,
    population: usize,
    key: impl FnOnce(u64) -> Result<KeyFamily, PopulationError>,
) -> Population {
    let bits = naming_bits(DEPTHS.len() + 1);
    let mut families: Vec<Box<dyn Family>> = DEPTHS
        .iter()
        .map(|&depth| {
            Box::new(
                TreeFamily::new(tree_declaration(alphabet, depth, population), bits)
                    .expect("a declared tree"),
            ) as Box<dyn Family>
        })
        .collect();
    families.push(Box::new(key(bits).expect("a declared key family")));
    Population::new(families).expect("a declared population")
}

fn posterior_line(posterior: &Posterior) -> String {
    match posterior {
        Posterior::Dead => "exactly 0 (dead)".to_string(),
        Posterior::Bits(bits) => format!("−log₂ w: {}", enclosure(bits, GRAIN)),
    }
}

/// The receipt's lines; returns the receipt.
fn report(population: &Population, started: Instant) -> PopulationReceipt {
    let receipt = population.receipt().expect("the population's receipt");
    let mass = &receipt.mass;
    println!(
        "the population: {} families, each named by {} bits; Kraft mass M = {} (unused {}), prior 1/{} each; {} cells received in {} ms (exterior wall)",
        receipt.families.len(),
        receipt.families[0].description,
        exact(mass),
        exact(&(Rat::from_integer(BigInt::from(1)) - mass)),
        receipt.families.len(),
        receipt.cells,
        started.elapsed().as_millis()
    );
    for (index, family) in receipt.families.iter().enumerate() {
        println!("  [{index}] {}", family.label);
        match (&family.died, &family.code, &family.charged) {
            (Some(cell), _, _) => {
                println!("      died at cell {cell} (zero likelihood); posterior exactly 0")
            }
            (None, Some(code), Some(charged)) => {
                println!("      code alone −log₂ L: {}", enclosure(code, GRAIN));
                println!("        a cell: {}", per(code, receipt.cells as u64, GRAIN));
                println!("      charged −log₂(π L): {}", enclosure(charged, GRAIN));
                println!("      posterior {}", posterior_line(&family.posterior));
            }
            _ => println!("      no code"),
        }
        if let Some(keys) = &family.keys {
            let count = keys.count();
            println!(
                "      key space {} (factors {:?}); survivors {}",
                factored(&keys.space()),
                keys.spaces,
                factored(&count)
            );
            if keys.spaces.len() > 1 {
                let counts: Vec<usize> = keys.survivors.iter().map(Vec::len).collect();
                println!("      survivors per factor (ring): {counts:?}");
            }
            if count <= BigUint::from(16u32) && count > BigUint::from(0u32) {
                for (factor, members) in keys.survivors.iter().enumerate() {
                    for member in members {
                        println!("        factor {factor}: {member:?}");
                    }
                }
            }
        }
    }
    println!(
        "  the population's code −log₂ Σ π_f L_f: {}",
        enclosure(&receipt.code, GRAIN)
    );
    println!(
        "    a cell: {}",
        per(&receipt.code, receipt.cells as u64, GRAIN)
    );
    let trees: Vec<usize> = (0..DEPTHS.len()).collect();
    let key = DEPTHS.len();
    let kinds = [
        (
            "the tree kind",
            population.posterior_of(&trees).expect("a posterior"),
        ),
        (
            "the key family",
            population.posterior_of(&[key]).expect("a posterior"),
        ),
    ];
    for (name, posterior) in &kinds {
        println!("  {name}'s posterior: {}", posterior_line(posterior));
    }
    let above_half = |posterior: &Posterior| matches!(posterior, Posterior::Bits(bits) if bits.upper < Rat::from_integer(BigInt::from(1)));
    match kinds.iter().find(|(_, posterior)| above_half(posterior)) {
        Some((name, _)) => println!("  the kind selected (posterior decided above ½): {name}"),
        None => println!("  the kind selected: none decided above ½"),
    }
    match receipt.selected {
        Some(index) => println!(
            "  selected (posterior decided above ½): [{index}] {}",
            receipt.families[index].label
        ),
        None => println!("  selected: none decided above ½"),
    }
    receipt
}

/// The leading tree family: the least posterior bits' lower endpoint among the living trees.
fn leading_tree(receipt: &PopulationReceipt) -> Option<usize> {
    (0..DEPTHS.len())
        .filter_map(|index| match &receipt.families[index].posterior {
            Posterior::Bits(bits) => Some((index, bits.lower.clone())),
            Posterior::Dead => None,
        })
        .min_by(|a, b| a.1.cmp(&b.1))
        .map(|(index, _)| index)
}

/// **`tree d`** (module header).
fn tree_harness(depth: usize) {
    let family = TreeSourceFamily {
        alphabet: 2,
        depth,
        grid: TREE_GRID,
    };
    let mut draw = Draw::new(SEED);
    let source = TreeSource::draw(&family, &mut draw).expect("a tree source of the family");
    let cells = source.emit(TREE_CELLS, &mut draw);
    let truth = source.truth().expect("the source's truth");
    let n = TREE_CELLS as u64;
    println!(
        "hnn_population tree {depth}: a tree source over bits, depth d = {depth}, faces on 1/{TREE_GRID}, seed {SEED}; n = {n} = 2^16 cells"
    );
    let leaves: Vec<String> = truth
        .leaves
        .iter()
        .map(|leaf| {
            format!(
                "[{}]",
                leaf.iter().map(ToString::to_string).collect::<String>()
            )
        })
        .collect();
    println!(
        "the truth: the tree family made it; leaves {}",
        leaves.join(" ")
    );
    let total_rate = on_grid(
        &truth
            .rate
            .scaled(&Rat::from_integer(BigInt::from(n)))
            .enclosure()
            .expect("an enclosure"),
    );
    let own = on_grid(
        &source
            .passage(&cells)
            .expect("the passage")
            .code
            .enclosure()
            .expect("an enclosure"),
    );
    println!("  n·h: {}", enclosure(&total_rate, GRAIN));
    println!(
        "  the source's own code of the realized cells, code_θ(x): {}",
        enclosure(&own, GRAIN)
    );
    let key_family = MoireFamily {
        rings: MOIRE_RINGS,
        denominator: 8,
    };
    let started = Instant::now();
    let mut population = declare(2, TREE_CELLS, |bits| {
        KeyFamily::gratings(&key_family, MoireClass::Parity, ENUMERATION, bits)
    });
    population.receive_passage(&cells).expect("the passage");
    let receipt = report(&population, started);
    println!(
        "  the population's code − n·h: {}",
        enclosure(
            &interval_difference(&receipt.code, &total_rate).expect("a difference"),
            GRAIN
        )
    );
    println!(
        "  the population's code − code_θ(x): {}",
        enclosure(
            &interval_difference(&receipt.code, &own).expect("a difference"),
            GRAIN
        )
    );
    let selected_tree = receipt.selected.is_some_and(|index| index < DEPTHS.len());
    println!(
        "  the population selected the family that made the terrain (a tree): {selected_tree}"
    );
    if let Some(index) = leading_tree(&receipt)
        && DEPTHS[index] >= depth
        && let Some(Readout::Standing(standing)) = population.readout(index)
    {
        let recovery = source.recovery(standing).expect("the recovered tree");
        let show = |leaves: &[Vec<usize>]| -> String {
            leaves
                .iter()
                .map(|leaf| {
                    format!(
                        "[{}]",
                        leaf.iter().map(ToString::to_string).collect::<String>()
                    )
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        println!(
            "  the leading tree [{index}] (D = {}) recovers: {} ({} of {} addresses agree with the minimal tree {}; exact: {})",
            DEPTHS[index],
            show(&recovery.recovered),
            recovery.agree_minimal,
            recovery.addresses,
            show(&recovery.minimal),
            recovery.exact_minimal
        );
    }
}

/// The key family's code against the key description: `log₂ |K| − log₂ #S`, exactly.
fn key_lines(receipt: &PopulationReceipt, key_bits: u64, key_space: &BigUint) {
    let family = &receipt.families[DEPTHS.len()];
    println!(
        "  the key description: log₂ {} = {} (⌈⌉ = {key_bits} bits)",
        factored(key_space),
        enclosure(&log2_of(key_space), GRAIN)
    );
    if let (Some(code), Some(keys)) = (&family.code, &family.keys) {
        let count = keys.count();
        println!(
            "  the key family's code = log₂ |K| − log₂ #S = log₂ |K| − log₂ {}: {}",
            count,
            enclosure(code, GRAIN)
        );
        println!(
            "  the population's code − the key family's code alone: {}",
            enclosure(
                &interval_difference(&receipt.code, code).expect("a difference"),
                GRAIN
            )
        );
    }
}

/// **`moire parity`** and **`moire sheets`** (module header).
fn moire_harness(class: MoireClass) {
    let started = Instant::now();
    let (family, moire) = match class {
        MoireClass::Parity => {
            let family = MoireFamily {
                rings: MOIRE_RINGS,
                denominator: 8,
            };
            let moire = Moire::draw(&family, MoireClass::Parity, &mut Draw::new(SEED))
                .expect("a drawn moiré");
            (family, moire)
        }
        MoireClass::Sheets => {
            let family = MoireFamily {
                rings: MOIRE_RINGS,
                denominator: 16,
            };
            let parity = Moire::draw(&family, MoireClass::Parity, &mut Draw::new(SEED))
                .expect("the terrain notebook's moiré");
            let moire =
                Moire::new(parity.gratings().to_vec(), MoireClass::Sheets).expect("its sheets");
            (family, moire)
        }
    };
    let truth = moire.truth(&family).expect("the moiré's truth");
    let name = match class {
        MoireClass::Parity => "the parity color Σ s_i mod 2",
        MoireClass::Sheets => "the sheet tuple Σ s_i 2^i",
    };
    println!(
        "hnn_population moire: {MOIRE_RINGS} gratings, denominators up to {}, {name}, seed {SEED}; n = {MOIRE_CELLS} = 2^14 cells",
        family.denominator
    );
    let keys: Vec<Vec<u64>> = truth
        .gratings
        .iter()
        .map(|g| vec![g.numerator(), g.denominator(), g.phase()])
        .collect();
    for (i, key) in keys.iter().enumerate() {
        println!(
            "  the truth, grating {i}: rate {}/{}, phase {}/{}",
            key[0], key[1], key[2], key[1]
        );
    }
    println!(
        "  joint period {}, least period {}, determining depth D* = {}; the rate 0 bits a cell (periodic)",
        factored(&truth.joint_period),
        factored(&BigUint::from(truth.least_period)),
        truth.depth
    );
    let cells = moire.emit(MOIRE_CELLS);
    let mut population = declare(moire.alphabet(), MOIRE_CELLS, |bits| {
        KeyFamily::gratings(&family, class, ENUMERATION, bits)
    });
    population.receive_passage(&cells).expect("the passage");
    let receipt = report(&population, started);
    key_lines(&receipt, truth.key_bits, &truth.key_space);
    let key = &receipt.families[DEPTHS.len()];
    if let Some(readout) = &key.keys {
        let holds = match class {
            MoireClass::Parity => readout.survivors[0].contains(&keys.concat()),
            MoireClass::Sheets => keys
                .iter()
                .zip(&readout.survivors)
                .all(|(key, survivors)| survivors.contains(key)),
        };
        println!("  the drawn keys lie among the survivors: {holds}");
    }
    let selected = receipt.selected == Some(DEPTHS.len());
    println!(
        "  the population selected the family that made the terrain (the gratings): {selected}"
    );
    match class {
        MoireClass::Parity => {
            let wide = MoireFamily {
                rings: MOIRE_RINGS,
                denominator: 16,
            };
            match KeyFamily::gratings(&wide, MoireClass::Parity, ENUMERATION, 0) {
                Err(refusal) => println!(
                    "  the parity class at denominators up to 2^4 ({} keys): refused: {refusal}",
                    factored(&BigUint::from(wide.gratings()).pow(3))
                ),
                Ok(_) => println!("  the parity class at denominators up to 2^4: admitted"),
            }
        }
        MoireClass::Sheets => {
            println!(
                "  the recorded tree at D* on this moiré: parity {RECORDED_PARITY_AT_D_STAR}, sheets {RECORDED_SHEETS_AT_D_STAR}"
            );
        }
    }
}

/// Campaign 1's field with ring 1 (period 7) locked at every port (module header).
fn crib_field() -> Field {
    let mut declared = FieldDeclaration::campaign_one(CRIB_POPULATION);
    declared.rings[CRIB_RING].lock = (0..7).collect();
    Field::declare(declared).expect("the crib's field")
}

/// **`crib`** (module header).
fn crib_harness() {
    let started = Instant::now();
    let field = crib_field();
    let configurations = [0u64; 4];
    let crib = RotorCrib::draw(
        &field,
        CRIB_RING,
        &configurations,
        CRIB_CELLS,
        &mut Draw::new(SEED),
    )
    .expect("a drawn crib");
    let ports = field.ring(CRIB_RING).period() as usize;
    println!(
        "hnn_population crib: campaign 1's ring {CRIB_RING} ({ports} ports, locked at every port) behind a drawn plugboard, seed {SEED}; n = {CRIB_CELLS} = 2^10 cells"
    );
    println!(
        "  the truth: start {}, key {}, plugboard {:?}; the terrain's key description ⌈log₂(7·7!)⌉ = {} bits; the source's own code given the key: the start's log₂ 7",
        crib.truth.start,
        crib.truth.key,
        crib.truth.board.images(),
        crib.truth.key_bits
    );
    let mut population = declare(ports, CRIB_CELLS, |bits| {
        KeyFamily::rotor(&field, CRIB_RING, &configurations, ENUMERATION, bits)
    });
    population
        .receive_passage(&crib.cells)
        .expect("the passage");
    let receipt = report(&population, started);
    let space = BigUint::from(ports) * (1..=ports).map(BigUint::from).product::<BigUint>();
    println!(
        "  the family's key space adds the start: |K| = {ports} · {} = {}",
        space,
        factored(&(BigUint::from(ports) * &space))
    );
    key_lines(&receipt, crib.truth.key_bits, &space);
    let truth: Vec<u64> = [crib.truth.start as u64, crib.truth.key]
        .into_iter()
        .chain(crib.truth.board.images().iter().map(|&i| i as u64))
        .collect();
    if let Some(keys) = &receipt.families[DEPTHS.len()].keys {
        println!(
            "  the drawn start, key and plugboard lie among the survivors: {}",
            keys.survivors[0].contains(&truth)
        );
    }
    println!(
        "  the population selected the family that made the terrain (the rotor keys): {}",
        receipt.selected == Some(DEPTHS.len())
    );
    match KeyFamily::rotor(&field, 2, &configurations, ENUMERATION, 0) {
        Err(refusal) => println!("  ring 2 (11 ports): refused: {refusal}"),
        Ok(_) => println!("  ring 2 (11 ports): admitted"),
    }
}

/// The founding trigger's section: every `2^8` cells.
const SECTION: usize = 1 << 8;

/// The trees at every depth of the ladder, then the declared key families; each family named by
/// `⌈log₂ F⌉` bits.
type KeyDeclaration<'a> = Box<dyn FnOnce(u64) -> Result<Box<dyn Family>, PopulationError> + 'a>;

fn declare_all(
    alphabet: usize,
    population: usize,
    keys: Vec<KeyDeclaration<'_>>,
) -> (Population, u64) {
    let bits = naming_bits(DEPTHS.len() + keys.len());
    let mut families: Vec<Box<dyn Family>> = DEPTHS
        .iter()
        .map(|&depth| {
            Box::new(
                TreeFamily::new(tree_declaration(alphabet, depth, population), bits)
                    .expect("a declared tree"),
            ) as Box<dyn Family>
        })
        .collect();
    for key in keys {
        families.push(key(bits).expect("a declared key family"));
    }
    (
        Population::new(families).expect("a declared population"),
        bits,
    )
}

/// `⌈log₂ n⌉`: the rung whose switch pays for its position among `n` cells.
fn rung_of(cells: usize) -> u32 {
    naming_bits(cells) as u32
}

fn bits_line(posterior: &Posterior) -> String {
    posterior_line(posterior)
}

/// A death's exchange receipt, printed.
fn death_lines(death: &DeathReceipt, labels: &[String]) {
    println!(
        "  death: [{}] {} at cell {} (class {} arrived{}); its last face {:?}",
        death.family,
        death.label,
        death.cell,
        death.arrived,
        death
            .factor
            .map_or(String::new(), |f| format!(", factor {f} exhausted")),
        death.face.iter().map(exact).collect::<Vec<_>>()
    );
    println!(
        "    the dying mass −log₂ w_f: {}",
        enclosure(&death.mass, GRAIN)
    );
    for (g, share) in &death.shares {
        println!(
            "    received by [{g}] {}: −log₂(w_f w′_g) {}",
            labels[*g],
            enclosure(share, GRAIN)
        );
    }
}

/// `x` bits, an exact point.
fn bits_of(value: u64) -> ExactInterval {
    point(value)
}

/// `m · I` for an integer `m` and an enclosure `I`.
fn times(count: u64, interval: &ExactInterval) -> ExactInterval {
    let m = Rat::from_integer(BigInt::from(count));
    ExactInterval::new(&interval.lower * &m, &interval.upper * &m).expect("an enclosure")
}

/// **The truth path's fixed-share code** (Lean `Dormancy.share_path_code`): each layer opens as a
/// step from active; the dormant layer switches at every switch cell, the others never.
fn path_code(layers: u64, switches: u64, cells: u64, rung: u32) -> ExactInterval {
    let alpha = Rat::new(BigInt::from(1), BigInt::from(1) << rung as usize);
    let stay = code_length(&(Rat::from_integer(BigInt::from(1)) - &alpha)).expect("a stay");
    let stays = (cells - switches) + (layers - 1) * cells;
    on_grid(
        &interval_sum(&times(stays, &stay), &bits_of(switches * u64::from(rung))).expect("a sum"),
    )
}

/// `log₂ C(n − 1, k)`: the positions `k` switches can take among a passage's `n − 1` boundaries.
fn positions(cells: u64, switches: u64) -> ExactInterval {
    let mut choose = BigUint::from(1u32);
    for i in 0..switches {
        choose = choose * BigUint::from(cells - 1 - i) / BigUint::from(i + 1);
    }
    log2_of(&choose)
}

/// A key's readout line for the dormant ring: survivors, the drawn key's fibre mass and the
/// dormancy of its layer.
fn dormant_lines(when: &str, keys: &KeyReadout, class: MoireClass, truth: &[Vec<u64>]) {
    match class {
        MoireClass::Sheets => {
            let counts: Vec<usize> = keys.survivors.iter().map(Vec::len).collect();
            let mirror = {
                let g = Grating::new(truth[0][0], truth[0][1], truth[0][2]).expect("a grating");
                let m = holonics::receiver::population::GratingSheet::mirror(&g).expect("a mirror");
                vec![m.numerator(), m.denominator(), m.phase()]
            };
            let fibre: Rat = keys.survivors[0]
                .iter()
                .zip(&keys.masses[0])
                .filter(|(key, _)| **key == truth[0] || **key == mirror)
                .map(|(_, mass)| mass.clone())
                .sum();
            let held = keys.survivors[0].contains(&truth[0]);
            println!(
                "  {when}: survivors per ring {counts:?}; ring 0's drawn grating held: {held}; its fibre (grating and mirror) −log₂ mass {}; ring 0 dormant −log₂ P {}, active −log₂ P {}",
                bits_text(&fibre),
                bits_text(&keys.dormant[0][0]),
                bits_text(&(Rat::from_integer(BigInt::from(1)) - &keys.dormant[0][0]))
            );
        }
        MoireClass::Parity => {
            let drawn = truth.concat();
            let held = keys.survivors[0].contains(&drawn);
            let drawn_mass = keys.survivors[0]
                .iter()
                .zip(&keys.masses[0])
                .find(|(key, _)| **key == drawn)
                .map_or(Rat::from_integer(BigInt::from(0)), |(_, m)| m.clone());
            println!(
                "  {when}: joint survivors {}; the drawn key held: {held}, −log₂ mass {}; ring 0 dormant −log₂ P {}, active −log₂ P {}; rings 1, 2 dormant −log₂ P {}, {}",
                keys.survivors[0].len(),
                bits_text(&drawn_mass),
                bits_text(&keys.dormant[0][0]),
                bits_text(&(Rat::from_integer(BigInt::from(1)) - &keys.dormant[0][0])),
                bits_text(&keys.dormant[0][1]),
                bits_text(&keys.dormant[0][2])
            );
        }
    }
}

/// `−log₂ p` of an exact probability, enclosed (`∞` at zero).
fn bits_text(probability: &Rat) -> String {
    if probability <= &Rat::from_integer(BigInt::from(0)) {
        return "∞ (zero)".to_string();
    }
    enclosure(
        &code_length(probability).expect("a positive probability"),
        GRAIN,
    )
}

/// Each grating's sheet over the passage as a bitset.
fn sheet_words(gratings: &[Grating], cells: usize) -> Vec<Vec<u64>> {
    gratings
        .iter()
        .map(|g| {
            let mut word = vec![0u64; cells.div_ceil(64)];
            for t in 0..cells as u64 {
                if g.sheet(t) {
                    word[(t / 64) as usize] |= 1 << (t % 64);
                }
            }
            word
        })
        .collect()
}

/// `#S_σ`: the keys (per ring for the sheets, joint for the parity) that emit the cells along the
/// truth's activity path, ring 0 sounding only in the even aeons; by brute force over bitsets.
fn path_survivors(
    family: &MoireFamily,
    class: MoireClass,
    switching: &Switching,
    cells: usize,
) -> Vec<BigUint> {
    let gratings: Vec<Grating> = (0..family.gratings())
        .map(|i| family.grating(i).expect("a grating"))
        .collect();
    let words = sheet_words(&gratings, cells);
    let mut even = vec![0u64; cells.div_ceil(64)];
    for t in 0..cells {
        if switching.truth.source(t) == Some(0) {
            even[t / 64] |= 1 << (t % 64);
        }
    }
    let target = |bit: usize| -> Vec<u64> {
        let mut word = vec![0u64; cells.div_ceil(64)];
        for (t, &cell) in switching.cells.iter().enumerate() {
            if (cell >> bit) & 1 == 1 {
                word[t / 64] |= 1 << (t % 64);
            }
        }
        word
    };
    match class {
        MoireClass::Parity => {
            let x = target(0);
            let masked: Vec<Vec<u64>> = words
                .iter()
                .map(|w| w.iter().zip(&even).map(|(a, e)| a & e).collect())
                .collect();
            let mut count = 0u64;
            for first in &masked {
                for second in &words {
                    let pair: Vec<u64> = first.iter().zip(second).map(|(a, b)| a ^ b).collect();
                    for third in &words {
                        if pair
                            .iter()
                            .zip(third)
                            .zip(&x)
                            .all(|((a, b), c)| a ^ b == *c)
                        {
                            count += 1;
                        }
                    }
                }
            }
            vec![BigUint::from(count)]
        }
        MoireClass::Sheets => (0..MOIRE_RINGS)
            .map(|ring| {
                let x = target(ring);
                let count = words
                    .iter()
                    .filter(|w| {
                        w.iter()
                            .zip(&x)
                            .zip(&even)
                            .all(|((a, c), e)| if ring == 0 { a & e == *c } else { a == c })
                    })
                    .count();
                BigUint::from(count)
            })
            .collect(),
    }
}

/// **`switching`** (module header): the dormant grating on the parity moiré of `moire parity`, and
/// the same gratings' sheet tuple read per ring; the static population, the population with
/// dormancy and the born one.
fn switching_harness(classes: &[MoireClass]) {
    let family = MoireFamily {
        rings: MOIRE_RINGS,
        denominator: 8,
    };
    let parity =
        Moire::draw(&family, MoireClass::Parity, &mut Draw::new(SEED)).expect("a drawn moiré");
    let truth_keys: Vec<Vec<u64>> = parity
        .gratings()
        .iter()
        .map(|g| vec![g.numerator(), g.denominator(), g.phase()])
        .collect();
    let rung = rung_of(MOIRE_CELLS);
    for &class in classes {
        let moire = Moire::new(parity.gratings().to_vec(), class).expect("the moiré");
        let switching = Switching::dormant(&moire, 0, MOIRE_CELLS, &AEONS, &mut Draw::new(SEED))
            .expect("the dormant grating");
        let truth = &switching.truth;
        let k = truth.switches.len() as u64;
        let n = MOIRE_CELLS as u64;
        let name = match class {
            MoireClass::Parity => "parity color",
            MoireClass::Sheets => "sheet tuple",
        };
        println!(
            "hnn_population switching ({name}): grating 0 silent in the odd aeons, aeons of {} to {} cells, seed {SEED}; n = {MOIRE_CELLS} = 2^14 cells",
            AEONS.shortest, AEONS.longest
        );
        println!(
            "  the truth: aeon lengths {:?}; {k} switches at cells {:?}; dormant grating {:?}",
            truth.lengths, truth.switches, truth.dormant
        );
        let first_silent = (0..MOIRE_CELLS)
            .find(|&t| switching.cells[t] != moire.cell(t as u64, &[true; MOIRE_RINGS]))
            .map_or("none".to_string(), |t| t.to_string());
        println!("  the first cell the silent layer changes: {first_silent}");
        println!(
            "  the switch rate α = 2^(−{rung}): a switch pays ⌈log₂ n⌉ = {rung} bits, the log₂ of its positions; log₂ C(n − 1, {k}) = {}",
            enclosure(&positions(n, k), GRAIN)
        );
        let family = &family;
        let static_keys = move |bits: u64| -> Result<Box<dyn Family>, PopulationError> {
            Ok(Box::new(KeyFamily::gratings(
                family,
                class,
                ENUMERATION,
                bits,
            )?))
        };
        let dormant_keys = move |bits: u64| -> Result<Box<dyn Family>, PopulationError> {
            Ok(Box::new(DormantFamily::gratings(
                family,
                class,
                ENUMERATION,
                rung,
                bits,
            )?))
        };

        // The unswitched moiré: the static population and the population with dormancy.
        let whole = moire.emit(MOIRE_CELLS);
        let (mut unswitched, _) =
            declare_all(moire.alphabet(), MOIRE_CELLS, vec![Box::new(static_keys)]);
        unswitched.receive_passage(&whole).expect("the passage");
        let unswitched_code = unswitched.code().expect("its code");
        let (mut unswitched_dormant, _) = declare_all(
            moire.alphabet(),
            MOIRE_CELLS,
            vec![Box::new(static_keys), Box::new(dormant_keys)],
        );
        unswitched_dormant
            .receive_passage(&whole)
            .expect("the passage");
        let unswitched_dormant_code = unswitched_dormant.code().expect("its code");
        println!(
            "  unswitched: the static population codes {}; with dormancy {} ({} the static; the dormancy's price {})",
            enclosure(&unswitched_code, GRAIN),
            enclosure(&unswitched_dormant_code, GRAIN),
            against(&unswitched_dormant_code, &unswitched_code),
            enclosure(
                &interval_difference(&unswitched_dormant_code, &unswitched_code)
                    .expect("a difference"),
                GRAIN
            )
        );
        let target = interval_sum(&unswitched_code, &bits_of(k * u64::from(rung))).expect("a sum");
        println!(
            "  the unswitched code plus {rung} bits a switch: {}",
            enclosure(&target, GRAIN)
        );

        // The static population.
        println!("the static population:");
        let started = Instant::now();
        let (mut fixed, _) =
            declare_all(moire.alphabet(), MOIRE_CELLS, vec![Box::new(static_keys)]);
        let reception = fixed
            .receive_passage(&switching.cells)
            .expect("the passage");
        let receipt = report_kinds(&fixed, started, &[("the static keys", vec![DEPTHS.len()])]);
        let labels: Vec<String> = receipt.families.iter().map(|f| f.label.clone()).collect();
        for death in &reception.deaths {
            death_lines(death, &labels);
        }
        comparison_lines(&receipt.code, &unswitched_code, &target, &positions(n, k));

        // The population with dormancy, read at the checkpoints.
        println!("the population with dormancy:");
        let started = Instant::now();
        let (mut population, _) = declare_all(
            moire.alphabet(),
            MOIRE_CELLS,
            vec![Box::new(static_keys), Box::new(dormant_keys)],
        );
        let dormant_index = DEPTHS.len() + 1;
        let (first, second) = (truth.switches[0], truth.switches[1]);
        let marks = [
            (first, "the end of the first aeon"),
            (second, "the return (the silent aeon's end)"),
            (second + 64, "64 cells after the return"),
            (MOIRE_CELLS, "the end"),
        ];
        let mut deaths = Reception::default().deaths;
        let mut at = 0;
        for (mark, when) in marks {
            let reception = population
                .receive_passage(&switching.cells[at..mark])
                .expect("the passage");
            deaths.extend(reception.deaths);
            at = mark;
            if let Some(Readout::Keys(keys)) = population.readout(dormant_index) {
                dormant_lines(&format!("{when} (cell {mark})"), &keys, class, &truth_keys);
            }
        }
        let receipt = report_kinds(
            &population,
            started,
            &[
                ("the static keys", vec![DEPTHS.len()]),
                ("the dormant keys", vec![dormant_index]),
            ],
        );
        let labels: Vec<String> = receipt.families.iter().map(|f| f.label.clone()).collect();
        for death in &deaths {
            death_lines(death, &labels);
        }
        comparison_lines(&receipt.code, &unswitched_code, &target, &positions(n, k));
        let surviving = path_survivors(family, class, &switching, MOIRE_CELLS);
        let space = BigUint::from(family.gratings()).pow(MOIRE_RINGS as u32);
        let keys_code = interval_difference(
            &log2_of(&space),
            &surviving.iter().fold(point(0), |sum, count| {
                interval_sum(&sum, &log2_of(count)).expect("a sum")
            }),
        )
        .expect("a difference");
        let bound = on_grid(
            &interval_sum(&keys_code, &path_code(MOIRE_RINGS as u64, k, n, rung)).expect("a sum"),
        );
        if let Some(code) = &receipt.families[dormant_index].code {
            println!(
                "  the dormant family's code {} against its bound log₂ |K| − log₂ #S_σ + the truth path's code = {} (#S_σ {:?}; the path: ring 0 opens active and switches {k} times, the others never): {}; the certified drift {} bits",
                enclosure(code, GRAIN),
                enclosure(&bound, GRAIN),
                surviving.iter().map(|c| factored(c)).collect::<Vec<_>>(),
                against(code, &bound),
                exact(&receipt.families[dormant_index].drift)
            );
        }

        // The born population: the static one founding the dormant family from its reserved 1/8.
        println!("the born population (the static one, founding from its reserved mass):");
        let started = Instant::now();
        let (fixed, bits) = declare_all(moire.alphabet(), MOIRE_CELLS, vec![Box::new(static_keys)]);
        let newborn = family.clone();
        let found = move |cell: usize| -> Result<Box<dyn Family>, PopulationError> {
            Ok(Box::new(
                DormantFamily::gratings(&newborn, class, ENUMERATION, rung, bits)?
                    .wind(cell as u64),
            ))
        };
        let mut born = fixed
            .with_founding(Founding {
                section_period: SECTION,
                candidates: vec![Candidate {
                    description: bits,
                    found: Box::new(found),
                }],
                reseed: false,
            })
            .expect("the founding");
        let reception = born.receive_passage(&switching.cells).expect("the passage");
        for birth in &reception.births {
            println!(
                "  birth: [{}] {} at cell {}, charged {} bits (mass {}, reserved left {}); the section's residual {}; the population's code at the birth {}",
                birth.family,
                birth.label,
                birth.cell,
                birth.description,
                exact(&birth.mass),
                exact(&birth.reserved),
                birth
                    .residual
                    .as_ref()
                    .map_or("none".to_string(), |r| enclosure(r, GRAIN)),
                enclosure(&birth.inherited, GRAIN)
            );
        }
        let receipt = report_kinds(
            &born,
            started,
            &[
                ("the static keys", vec![DEPTHS.len()]),
                ("the newborn dormant keys", vec![DEPTHS.len() + 1]),
            ],
        );
        let labels: Vec<String> = receipt.families.iter().map(|f| f.label.clone()).collect();
        for death in &reception.deaths {
            death_lines(death, &labels);
        }
        if let Some(Readout::Keys(keys)) = born.readout(DEPTHS.len() + 1) {
            dormant_lines("the newborn at the end", &keys, class, &truth_keys);
        }
        comparison_lines(&receipt.code, &unswitched_code, &target, &positions(n, k));

        // The reseeding population: the static one re-founding its dead gratings' seed.
        println!(
            "the reseeding population (the static one, re-founding its dead seed from its reserved mass):"
        );
        let started = Instant::now();
        let (fixed, _) = declare_all(moire.alphabet(), MOIRE_CELLS, vec![Box::new(static_keys)]);
        let mut reseeding = fixed
            .with_founding(Founding {
                section_period: SECTION,
                candidates: Vec::new(),
                reseed: true,
            })
            .expect("the founding");
        let reception = reseeding
            .receive_passage(&switching.cells)
            .expect("the passage");
        let lived: Vec<(usize, Option<usize>)> = reception
            .births
            .iter()
            .map(|birth| (birth.cell, reseeding.died(birth.family)))
            .collect();
        let long: Vec<&(usize, Option<usize>)> = lived
            .iter()
            .filter(|(born, died)| died.is_none_or(|d| d >= born + SECTION))
            .collect();
        println!(
            "  {} re-foundings of the seed ({} seed keys), the charges {} to {} bits; {} lived a section or more (born, died): {:?}",
            reception.births.len(),
            reception
                .deaths
                .first()
                .and_then(|death| death.seed.as_ref())
                .map_or(0, |seed| seed
                    .survivors
                    .iter()
                    .map(Vec::len)
                    .product::<usize>()),
            reception
                .births
                .first()
                .map_or("none".to_string(), |b| enclosure(&b.charge, GRAIN)),
            reception
                .births
                .last()
                .map_or("none".to_string(), |b| enclosure(&b.charge, GRAIN)),
            long.len(),
            long
        );
        let receipt = reseeding.receipt().expect("the receipt");
        println!(
            "  {} families at the end in {} ms (exterior wall); the population's code −log₂ W: {}",
            receipt.families.len(),
            started.elapsed().as_millis(),
            enclosure(&receipt.code, GRAIN)
        );
        comparison_lines(&receipt.code, &unswitched_code, &target, &positions(n, k));
        println!();
    }
}

/// A population's code against the unswitched one, against it plus `j` bits a switch, and less the
/// switch positions' `log₂ C(n − 1, k)`.
fn comparison_lines(
    code: &ExactInterval,
    unswitched: &ExactInterval,
    target: &ExactInterval,
    positions: &ExactInterval,
) {
    println!(
        "  the code {}: less the unswitched {}; less the unswitched plus j bits a switch {} ({}); less the unswitched and log₂ C(n − 1, k) {}",
        enclosure(code, GRAIN),
        enclosure(
            &interval_difference(code, unswitched).expect("a difference"),
            GRAIN
        ),
        enclosure(
            &interval_difference(code, target).expect("a difference"),
            GRAIN
        ),
        against(code, target),
        enclosure(
            &interval_difference(code, &interval_sum(unswitched, positions).expect("a sum"))
                .expect("a difference"),
            GRAIN
        )
    );
}

/// The receipt's lines with the declared kinds' posteriors; returns the receipt.
fn report_kinds(
    population: &Population,
    started: Instant,
    keys: &[(&str, Vec<usize>)],
) -> PopulationReceipt {
    let receipt = population.receipt().expect("the population's receipt");
    println!(
        "  {} families (declared mass {}, founded {}, reserved {}); {} cells in {} ms (exterior wall)",
        receipt.families.len(),
        exact(&receipt.mass),
        exact(&receipt.founded),
        exact(&(Rat::from_integer(BigInt::from(1)) - &receipt.founded)),
        receipt.cells,
        started.elapsed().as_millis()
    );
    for (index, family) in receipt.families.iter().enumerate() {
        let born = if family.born > 0 {
            format!(", founded at cell {}", family.born)
        } else {
            String::new()
        };
        match (&family.died, &family.charged) {
            (Some(cell), _) => println!(
                "  [{index}] {}{born}: died at cell {cell}; posterior exactly 0",
                family.label
            ),
            (None, Some(charged)) => println!(
                "  [{index}] {}{born}: code alone {}; charged {}; posterior {}",
                family.label,
                family
                    .code
                    .as_ref()
                    .map_or("none".to_string(), |c| enclosure(c, GRAIN)),
                enclosure(charged, GRAIN),
                bits_line(&family.posterior)
            ),
            _ => println!("  [{index}] {}: no code", family.label),
        }
    }
    let trees: Vec<usize> = (0..DEPTHS.len()).collect();
    println!(
        "  the tree kind's posterior: {}",
        posterior_line(&population.posterior_of(&trees).expect("a posterior"))
    );
    for (name, set) in keys {
        println!(
            "  {name}' posterior: {}",
            posterior_line(&population.posterior_of(set).expect("a posterior"))
        );
    }
    match receipt.selected {
        Some(index) => println!(
            "  selected (posterior decided above ½): [{index}] {}",
            receipt.families[index].label
        ),
        None => println!("  selected: none decided above ½"),
    }
    println!(
        "  the population's code −log₂ W: {} (a cell {})",
        enclosure(&receipt.code, GRAIN),
        per(&receipt.code, receipt.cells as u64, GRAIN)
    );
    receipt
}

/// **`standing <cut>`** (module header): the trees' population on the standing real cut against the
/// recorded tree.
fn standing_harness(path: &str) {
    let (bytes, count, held) = exterior::read_cut(path);
    let cells: Vec<usize> = bytes.iter().map(|&b| usize::from(b)).collect();
    println!(
        "hnn_population standing: the standing real cut, {count} cells, held out {}..{} ({} cells); the population of trees alone, D ∈ {DEPTHS:?}, each named by {} bits",
        held.start,
        held.end,
        held.len(),
        naming_bits(DEPTHS.len())
    );
    let started = Instant::now();
    let (mut population, _) = declare_all(256, count, Vec::new());
    population
        .receive_passage(&cells[..held.start])
        .expect("the development cells");
    let development = population.code().expect("its code");
    population
        .receive_passage(&cells[held.start..])
        .expect("the held-out cells");
    let receipt = report_kinds(&population, started, &[]);
    let held_out = interval_difference(&receipt.code, &development).expect("a difference");
    let recorded = tree_declaration(256, 4, count);
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![held.clone()],
    };
    let ([tree_development, tree_held], _) =
        tree_prequential(&cut, &cell_letters(&cells), &recorded).expect("the recorded tree");
    println!(
        "  development ({} cells): the population {} (a cell {}); the recorded tree D = 4 {} (a cell {}); population − tree {}",
        held.start,
        enclosure(&development, GRAIN),
        per(&development, held.start as u64, GRAIN),
        enclosure(&tree_development, GRAIN),
        per(&tree_development, held.start as u64, GRAIN),
        enclosure(
            &interval_difference(&development, &tree_development).expect("a difference"),
            GRAIN
        )
    );
    println!(
        "  held out ({} cells): the population {} (a cell {}); the recorded tree D = 4 {} (a cell {}, recorded 3 + 1/16 + ε a cell, 3677 + 12/16 + ε on its exact face); population − tree {}",
        held.len(),
        enclosure(&held_out, GRAIN),
        per(&held_out, held.len() as u64, GRAIN),
        enclosure(&tree_held, GRAIN),
        per(&tree_held, held.len() as u64, GRAIN),
        enclosure(
            &interval_difference(&held_out, &tree_held).expect("a difference"),
            GRAIN
        )
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["tree", depth] => tree_harness(depth.parse().expect("a depth")),
        ["moire", "parity"] => moire_harness(MoireClass::Parity),
        ["moire", "sheets"] => moire_harness(MoireClass::Sheets),
        ["crib"] => crib_harness(),
        ["switching"] => switching_harness(&[MoireClass::Parity, MoireClass::Sheets]),
        ["switching", "parity"] => switching_harness(&[MoireClass::Parity]),
        ["switching", "sheets"] => switching_harness(&[MoireClass::Sheets]),
        ["standing", path] => standing_harness(path),
        ["composition"] => composition::harness(None),
        ["composition", which] => composition::harness(Some(which)),
        ["evolution"] => evolution::evolution(),
        ["species"] => evolution::species(),
        ["birth"] => birth::harness(),
        ["birth-probe"] => birth::probe(),
        ["birth-dimensions"] => birth::dimensions(),
        ["curated", curated_cut, flat_cut] => {
            curated::harness(curated_cut, flat_cut, curated::Reach::Whole);
        }
        ["curated", curated_cut, flat_cut, "development"] => {
            curated::harness(curated_cut, flat_cut, curated::Reach::Development);
        }
        ["curated", curated_cut, flat_cut, "merges"] => {
            curated::harness(curated_cut, flat_cut, curated::Reach::Merges);
        }
        ["f4", curated_cut, flat_cut] => {
            curated::harness(curated_cut, flat_cut, curated::Reach::F4);
        }
        ["f0-egg", curated_cut, flat_cut] => {
            curated::harness(curated_cut, flat_cut, curated::Reach::F0Egg);
        }
        ["f0-census", curated_cut] => census::standing_census(curated_cut),
        ["u2-acceptance", curated_cut, flat_cut] => u2::acceptance(curated_cut, flat_cut),
        ["f5-native", choosing_cut, request, seed, private_output] => {
            curated::native_probe(choosing_cut, request, seed, private_output, false);
        }
        ["f5-family", choosing_cut, request, seed, private_output] => {
            curated::native_probe(choosing_cut, request, seed, private_output, true);
        }
        [
            "f5-family-verify",
            choosing_cut,
            request,
            seed,
            private_output,
        ] => {
            curated::native_verify_family_probe(choosing_cut, request, seed, private_output);
        }
        ["f5-bundle", choosing_cut, bundle, private_dir] => {
            curated::native_bundle(choosing_cut, bundle, private_dir, 32);
        }
        ["f5-bundle", choosing_cut, bundle, private_dir, limit] => {
            curated::native_bundle(
                choosing_cut,
                bundle,
                private_dir,
                limit.parse().expect("a request limit"),
            );
        }
        ["f5-checkpoint-census", choosing_cut] => {
            curated::checkpoint_census(choosing_cut);
        }
        ["f5-checkpoint-restore", choosing_cut, checkpoint_path] => {
            curated::checkpoint_restore(choosing_cut, checkpoint_path);
        }
        _ => println!(
            "usage: hnn_population -- tree <d> | moire parity | moire sheets | crib | switching | standing <cut> | composition [products | primes] | evolution | species | curated <curated-cut> <flat-cut> [development | merges] | f4 <joined-cut> <joined-flat-cut> | f0-egg <joined-cut> <joined-flat-cut> | f0-census <joined-cut> | u2-acceptance <joined-cut> <joined-flat-cut> | f5-native <choosing-cut> <private-request> <private-seed> <private-output> | f5-family <choosing-cut> <private-request> <private-seed> <private-output> | f5-family-verify <choosing-cut> <private-request> <private-seed> <private-output> | f5-bundle <choosing-cut> <private-F5R1-bundle> <owner-only-output-dir> [limit 1..32] | f5-checkpoint-census <choosing-cut> | f5-checkpoint-restore <choosing-cut> <.local/cuts/private-checkpoint>"
        ),
    }
}
