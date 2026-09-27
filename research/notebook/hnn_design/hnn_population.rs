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
//! cargo run --release -p holonics --example hnn_population -- switching
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

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use holonics::hnn::field::{Field, FieldDeclaration};
use holonics::holarchy::terrain::{
    AeonFamily, Draw, Moire, MoireClass, MoireFamily, RotorCrib, Switching, TreeSource,
    TreeSourceFamily,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{
    ExactInterval, interval_difference, interval_sum, log2_enclosure,
};
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::receiver::population::{
    Family, KeyFamily, Population, PopulationError, PopulationReceipt, Posterior, Readout,
    TreeFamily,
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
/// (`hnn_terrain -- moire`, the audit record's §6.2): parity `993 + 5/16 + ε`, sheets `1549 + 0/16 + ε`.
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

/// **`switching`** (module header): the dormant grating on the parity moiré of `moire parity`, and
/// the same gratings' sheet tuple read per ring.
fn switching_harness() {
    let family = MoireFamily {
        rings: MOIRE_RINGS,
        denominator: 8,
    };
    let parity =
        Moire::draw(&family, MoireClass::Parity, &mut Draw::new(SEED)).expect("a drawn moiré");
    for class in [MoireClass::Parity, MoireClass::Sheets] {
        let started = Instant::now();
        let moire = Moire::new(parity.gratings().to_vec(), class).expect("the moiré");
        let switching = Switching::dormant(&moire, 0, MOIRE_CELLS, &AEONS, &mut Draw::new(SEED))
            .expect("the dormant grating");
        let truth = &switching.truth;
        println!(
            "hnn_population switching ({}): grating 0 silent in the odd aeons, aeons of {} to {} cells, seed {SEED}; n = {MOIRE_CELLS} = 2^14 cells",
            match class {
                MoireClass::Parity => "parity color",
                MoireClass::Sheets => "sheet tuple",
            },
            AEONS.shortest,
            AEONS.longest
        );
        println!(
            "  the truth: aeon lengths {:?}, switch cells {:?}, dormant grating {:?}",
            truth.lengths, truth.switches, truth.dormant
        );
        let first_silent = (0..MOIRE_CELLS)
            .find(|&t| switching.cells[t] != moire.cell(t as u64, &[true; MOIRE_RINGS]))
            .map_or("none".to_string(), |t| t.to_string());
        println!("  the first cell the silent layer changes: {first_silent}");
        let mut population = declare(moire.alphabet(), MOIRE_CELLS, |bits| {
            KeyFamily::gratings(&family, class, ENUMERATION, bits)
        });
        population
            .receive_passage(&switching.cells)
            .expect("the passage");
        let receipt = report(&population, started);
        let whole = Moire::new(parity.gratings().to_vec(), class)
            .expect("the moiré")
            .emit(MOIRE_CELLS);
        let unswitched = declare(moire.alphabet(), MOIRE_CELLS, |bits| {
            KeyFamily::gratings(&family, class, ENUMERATION, bits)
        });
        let mut unswitched = unswitched;
        unswitched.receive_passage(&whole).expect("the passage");
        let code = unswitched.code().expect("its code");
        println!(
            "  the same population on the unswitched moiré: {} ({} the switching terrain's)",
            enclosure(&code, GRAIN),
            against(&code, &receipt.code)
        );
        println!(
            "  the switching terrain's code less the unswitched one: {}",
            enclosure(
                &interval_difference(&receipt.code, &code).expect("a difference"),
                GRAIN
            )
        );
    }
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
        ["switching"] => switching_harness(),
        _ => println!(
            "usage: hnn_population -- tree <d> | moire parity | moire sheets | crib | switching"
        ),
    }
}
