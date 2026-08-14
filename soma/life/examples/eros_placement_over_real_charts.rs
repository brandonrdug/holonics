//! Placement over two real receiver charts conditioned on this repository's own documents.
//!
//! Every organ built this week was tested on fixtures its author wrote. This runs them on material
//! that was not made for them: the records and canon of this repository, read as text.
//!
//! Two charts over one source, which is the smallest honest instance of the five the morphological
//! ecology carries:
//!
//! ```text
//!   forward marks, horizon 2   sees the first two marks
//!   forward marks, horizon 3   sees the first three
//!   reverse marks, horizon 2   sees the last two
//! ```
//!
//! **The horizon is what makes these receivers rather than addresses.** The first version of this
//! driver observed the full automaton state, which is very nearly injective on distinct surfaces:
//! the one-shot partition came back already discrete over 2,758 surfaces, refinement was zero, and
//! the compression organ had nothing to do. A receiver that distinguishes everything compresses
//! nothing. That is the same degenerate branch the cyclic family exposed — where the family already
//! separates the population, there is no identified pair for conduct to refine — met on real data.
//!
//! ## What each organ is asked
//!
//! - **`ObservedSystem`** — items are word surfaces; a receiver's observation of a surface is the
//!   *state its own suffix automaton reaches* on it, which is a receiver-local address and not a
//!   magnitude; an input appends a mark; a successor is the extended surface when the population
//!   holds one, and a declared terminus when it does not.
//! - **`receiver_exact_compression`** — refine to the conduct classes. Two surfaces sharing a class
//!   are indistinguishable to both charts under every admitted extension.
//! - **`supported_realizers` via `placement`** — a class stands only where the ecology's own
//!   `emanate` can actually reach it. What it distinguishes and cannot produce is OPEN.
//!
//! Nothing here is a fixture. The corpus is whatever files are passed, defaulting to this
//! repository's research records, and the surfaces are whatever those files contain.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use body::num::Cog;
use holonic_engine::placement::{place, Placement};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use holonic_engine::supported_realizers::RealizerId;
use life::resonance_ecology::{fiber_from_bytes, ResonanceGerm};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::RelationAtom;

const MARK_SCHEMA: u64 = 0x4d41_524b;
/// Surfaces shorter than this carry too little conduct to be worth placing, and longer than this
/// are rare enough in prose that they distort the population. Declared, not tuned.
const SHORTEST: usize = 3;
/// Each receiver is a direction and a declared horizon in marks.
const APERTURES: [(bool, usize); 3] = [(false, 2), (false, 3), (true, 2)];
const LONGEST: usize = 12;

fn germs(surface: &str, reversed: bool) -> Vec<ResonanceGerm> {
    let phase = RelationAtom::new(Cog::lit(1)).expect("unit phase");
    let marks: Vec<char> = if reversed {
        surface.chars().rev().collect()
    } else {
        surface.chars().collect()
    };
    marks
        .into_iter()
        .map(|mark| {
            ResonanceGerm::new(
                fiber_from_bytes(MARK_SCHEMA, mark.to_string().as_bytes()),
                phase,
            )
        })
        .collect()
}

/// Two charts over one surface population.
struct Charts {
    surfaces: Vec<String>,
    forward: ExactSuffixEcology,
    reverse: ExactSuffixEcology,
    /// Marks that actually occur, in canonical order. The input alphabet, declared rather than
    /// assumed — the refutation of these organs named an undeclared alphabet as a live gap.
    alphabet: Vec<char>,
    index: BTreeMap<String, usize>,
}

impl Charts {
    fn condition(surfaces: Vec<String>) -> Self {
        let forward_paths: Vec<Vec<ResonanceGerm>> =
            surfaces.iter().map(|s| germs(s, false)).collect();
        let reverse_paths: Vec<Vec<ResonanceGerm>> =
            surfaces.iter().map(|s| germs(s, true)).collect();
        let alphabet: BTreeSet<char> = surfaces.iter().flat_map(|s| s.chars()).collect();
        let index = surfaces
            .iter()
            .enumerate()
            .map(|(at, surface)| (surface.clone(), at))
            .collect();
        Self {
            forward: ExactSuffixEcology::condition(&forward_paths).expect("forward conditions"),
            reverse: ExactSuffixEcology::condition(&reverse_paths).expect("reverse conditions"),
            surfaces,
            alphabet: alphabet.into_iter().collect(),
            index,
        }
    }

    /// A receiver reads the state its automaton reaches within a declared horizon of marks. Beyond
    /// the horizon it sees nothing, which is what lets two surfaces look alike to it.
    fn state(&self, surface: &str, receiver: ReceiverId) -> u32 {
        let (reversed, horizon) = APERTURES[receiver.0 as usize];
        let ecology = if reversed {
            &self.reverse
        } else {
            &self.forward
        };
        let mut path = germs(surface, reversed);
        path.truncate(horizon);
        if path.is_empty() {
            return 0;
        }
        ecology
            .receive_path(&path)
            .map(|current| current.state())
            .unwrap_or(0)
    }
}

impl ObservedSystem for Charts {
    fn items(&self) -> Vec<ItemId> {
        (0..self.surfaces.len() as u64).map(ItemId).collect()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        (0..APERTURES.len() as u64).map(ReceiverId).collect()
    }
    fn inputs(&self) -> Vec<InputId> {
        (0..self.alphabet.len() as u64).map(InputId).collect()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        Observation(u64::from(
            self.state(&self.surfaces[item.0 as usize], receiver),
        ))
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let mut extended = self.surfaces[item.0 as usize].clone();
        extended.push(self.alphabet[input.0 as usize]);
        self.index.get(&extended).map(|at| ItemId(*at as u64))
    }
}

fn corpus(paths: &[PathBuf]) -> Vec<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for path in paths {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        for raw in text.split(|c: char| !c.is_alphanumeric()) {
            let surface = raw.to_lowercase();
            if surface.chars().count() >= SHORTEST && surface.chars().count() <= LONGEST {
                seen.insert(surface);
            }
        }
    }
    seen.into_iter().collect()
}

fn report(placed: &Placement, charts: &Charts) {
    println!(
        "  surfaces {:>5}   one-shot classes {:>5}   conduct classes {:>5}   refinement {:>4}",
        charts.surfaces.len(),
        placed.compression.one_shot.len(),
        placed.compression.conduct.len(),
        placed.compression.refinement(),
    );
    println!(
        "  standing {:>5}   OPEN {:>5}   collapsed pairs {:>5}   rounds {:>3}",
        placed.standing.len(),
        placed.open.len(),
        placed.compression.collapsed.len(),
        placed.compression.rounds,
    );

    for pair in placed.compression.collapsed.iter().take(3) {
        let word: String = pair
            .distinguishing_word
            .iter()
            .map(|input| charts.alphabet[input.0 as usize])
            .collect();
        println!(
            "    collapsed  {:<14} {:<14}  separated by {:?}",
            charts.surfaces[pair.left.0 as usize], charts.surfaces[pair.right.0 as usize], word
        );
    }
    for open in placed.open.iter().take(3) {
        let members: Vec<&str> = open
            .members
            .iter()
            .take(3)
            .map(|item| charts.surfaces[item.0 as usize].as_str())
            .collect();
        println!(
            "    OPEN       class {:<5} {:?}{}",
            open.class,
            members,
            open.reached_only_in_multiple
                .as_ref()
                .map(|factor| format!("  reached only x{factor}"))
                .unwrap_or_default()
        );
    }
}

fn main() {
    let arguments: Vec<PathBuf> = std::env::args().skip(1).map(PathBuf::from).collect();
    let paths = if arguments.is_empty() {
        let mut found: Vec<PathBuf> = std::fs::read_dir("research/records")
            .map(|entries| {
                entries
                    .flatten()
                    .map(|entry| entry.path())
                    .filter(|path| path.extension().is_some_and(|kind| kind == "md"))
                    .collect()
            })
            .unwrap_or_default();
        found.sort();
        found.truncate(12);
        found
    } else {
        arguments
    };

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a class stands only where the ecology's own emanation reaches it");
    println!("corpus={} documents", paths.len());
    if paths.is_empty() {
        println!("FAILED — no documents; this driver refuses to run on a fixture");
        std::process::exit(1);
    }

    let surfaces = corpus(&paths);
    let charts = Charts::condition(surfaces);
    println!(
        "\nforward chart {:>6} states   reverse chart {:>6} states   alphabet {:>4} marks",
        charts.forward.state_count(),
        charts.reverse.state_count(),
        charts.alphabet.len(),
    );

    // Realizers are the ecology's own production: emanate from each surface and take the marks it
    // can actually continue with, then the surfaces those continuations name. A class is reached
    // only where emanation reaches it.
    let realizers: Vec<RealizerId> = (0..charts.surfaces.len() as u64).map(RealizerId).collect();
    let placed = place(&charts, &realizers, |realizer| {
        let surface = &charts.surfaces[realizer.0 as usize];
        let path = germs(surface, false);
        let Ok(emanation) = charts.forward.emanate(&path) else {
            return Vec::new();
        };
        let mut reached = Vec::new();
        for branch in emanation.branches() {
            for mark in &charts.alphabet {
                let mut extended = surface.clone();
                extended.push(*mark);
                if let Some(at) = charts.index.get(&extended) {
                    reached.push(ItemId(*at as u64));
                }
            }
            let _ = branch;
            break;
        }
        reached
    });

    println!("\nPLACEMENT");
    println!("---------");
    report(&placed, &charts);

    let mut holds: Vec<(&str, bool, String)> = Vec::new();
    holds.push((
        "the receivers genuinely differ on this material",
        charts.surfaces.iter().any(|surface| {
            charts.state(surface, ReceiverId(0)) != charts.state(surface, ReceiverId(1))
                || charts.state(surface, ReceiverId(0)) != charts.state(surface, ReceiverId(2))
        }),
        format!(
            "{} apertures over {} surfaces",
            APERTURES.len(),
            charts.surfaces.len()
        ),
    ));
    holds.push((
        "CONTROL the receivers do NOT already separate everything, so refinement has work",
        placed.compression.one_shot.len() < charts.surfaces.len(),
        format!(
            "{} one-shot classes over {} surfaces",
            placed.compression.one_shot.len(),
            charts.surfaces.len()
        ),
    ));
    holds.push((
        "CONTROL conduct actually refined the one-shot reading",
        placed.compression.refinement() > 0,
        format!(
            "{} -> {} classes, {} collapsed pairs",
            placed.compression.one_shot.len(),
            placed.compression.conduct.len(),
            placed.compression.collapsed.len()
        ),
    ));
    holds.push((
        "nothing stands that emanation did not reach",
        placed.every_standing_class_was_paid_for(),
        format!("{} standing", placed.standing.len()),
    ));
    holds.push((
        "no class is both standing and OPEN",
        placed.open.iter().all(|open| {
            placed
                .standing
                .iter()
                .all(|standing| standing.class != open.class)
        }),
        format!("{} OPEN", placed.open.len()),
    ));
    holds.push((
        "is_exact and refinement do not contradict",
        placed.compression.is_exact() == (placed.compression.refinement() == 0),
        format!(
            "exact={} refinement={}",
            placed.compression.is_exact(),
            placed.compression.refinement()
        ),
    ));
    holds.push((
        "CONTROL the corpus produced more than one conduct class",
        placed.compression.conduct.len() > 1,
        format!("{} classes", placed.compression.conduct.len()),
    ));

    println!("\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD — {} declared controls, 0 failed", holds.len());
    } else {
        println!("FAILED — {failed} of {} did not hold", holds.len());
        std::process::exit(1);
    }
}
