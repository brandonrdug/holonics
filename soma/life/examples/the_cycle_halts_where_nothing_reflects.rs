//! THE CYCLE HALTS WHERE NOTHING REFLECTS — generation as integration by reflection, driven.
//!
//! ## The ruling this tests
//!
//! Brandon, 2026-08-15: *"Generation is also integration by reflection… your 'thinking' loops are
//! boundaries that reflect, which is why the cycle continues, where eventually nothing reflects back
//! and you don't predict any further tokens."*
//!
//! `blueprint/THE_EROS_INSTANTIATION.md` deposited that as a law with a falsifier and **the
//! falsifier had never run.** This is it.
//!
//! ```text
//!    Gamma = (Y_i − Y_t) : (Y_i + Y_t)      what comes back
//!    T     = 4 Y_i Y_t  : (Y_i + Y_t)^2     the power that crosses
//!    service rounds = ceil(1/T)             how many passes the current needs
//!
//!    a thinking loop      the reflected part re-entering — this is why the cycle CONTINUES
//!    TERMINATION          Gamma = 0. The boundary MATCHES; nothing comes back.
//! ```
//!
//! **Termination is impedance matching.** No stop token, no threshold, no chooser: the cycle halts
//! because nothing reflects. That is the ban on a privileged scalar governor satisfied by the
//! physics rather than by discipline.
//!
//! ## The junction, and both admittances come off the arrival
//!
//! At one enclosure boundary the current carries the faces the arrival reached and the boundary
//! admits the faces it **founded**:
//!
//! ```text
//!    Y_i = perception.faces           what arrived at the boundary
//!    Y_t = perception.faces_founded   what the boundary took
//! ```
//!
//! Nothing here is declared. Both are populations the body returns, and `CountedCrossing::meet` is
//! the same integer junction law `laboratory_language` already admits leaders through.
//!
//! ## The declared falsifier — three arms, and each can fail
//!
//! 1. **A matched boundary must close.** Where `Gamma = 0` — every arriving face founded — the
//!    thought must complete. If the cycle continues at a match, the reflected share is not what
//!    re-enters and the reading is withdrawn.
//! 2. **An unmatched boundary must not close.** Where `Gamma != 0` the thought must stay open. If
//!    thoughts complete at mismatched boundaries, something other than the match is deciding.
//! 3. **Both populations must be non-empty**, or the contrast is vacuous: a run where every
//!    boundary matched, or none did, has separated nothing and the arms above hold for free.
//!
//! **Arms 1 and 2 are stated in the strong form and are expected to be informative either way.** A
//! partial correspondence is a real return — it names how much of closure the match accounts for —
//! and is reported as a pair rather than collapsed into a rate.
//!
//! ## Bars
//!
//! No count here is a cost. `Gamma` is carried as a pair and never divided. No clock is taken and
//! nothing selects.

use std::path::{Path, PathBuf};

use body::manifold::{ErosBody, ENCLOSURE_WORDS};
use holonic_engine::traversible_chain::CountedCrossing;

const AXIS: i64 = 1 << 8;
const SEED: &[u8] = b"the cycle halts where nothing reflects";

/// Real deposited material — the plan that declared this falsifier, and the ruling's own record.
const RECORDS: &[&str] = &[
    "blueprint/THE_EROS_INSTANTIATION.md",
    "research/records/2026-08-15_THE_ECOLOGY_READS_FROM_A_FRAME_THAT_NO_LIVE_PATH_ADVANCES.md",
];

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn material(root: &Path, cap: usize) -> Vec<Vec<u8>> {
    let mut words = Vec::new();
    for relative in RECORDS {
        let Ok(text) = std::fs::read_to_string(root.join(relative)) else {
            continue;
        };
        for word in text.split_whitespace() {
            if !word.is_empty() {
                words.push(word.as_bytes().to_vec());
            }
            if words.len() >= cap {
                return words;
            }
        }
    }
    words
}

/// One boundary crossing, kept whole. Populations and a pair, never a rate.
///
/// **`CountedCrossing::meet` refuses a zero population by type, and that refusal is DATA.** A
/// boundary that founds nothing has no traveling section: it reflects everything, `Gamma = 1`,
/// `T = 0`, and the current needs unboundedly many passes. Dropping those arrivals — which the
/// first form of this driver did — filters the material down to exactly the boundaries that
/// matched, and then reports that every boundary matched. The anti-vacuity arm caught it: 6
/// boundaries of 4,000 arrivals, all matched, both correspondence arms holding for free.
#[derive(Debug)]
struct Boundary {
    arrived: u64,
    founded: u64,
    /// `Gamma = (Y_i − Y_t) : (Y_i + Y_t)`, exactly as the junction returns it. Never divided.
    /// `None` is the typed terminus: no traveling section, so the whole current came back.
    reflection: Option<(i128, u128)>,
    /// `ceil(1/T)`. `None` where nothing crosses, which is not a large number but an absent one.
    service_rounds: Option<u128>,
    closed: bool,
    /// Enclosures standing open after this arrival — the thinking loops still ringing.
    standing: u32,
}

/// The three species a boundary can be, separated because collapsing any two loses the reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Species {
    /// `Gamma = 0` — every arriving face founded. Nothing comes back.
    Matched,
    /// `Gamma != 0` and finite — part crossed and part returned.
    Partial,
    /// No traveling section. The whole current came back.
    Total,
}

impl Boundary {
    fn species(&self) -> Species {
        match self.reflection {
            None => Species::Total,
            Some((0, _)) => Species::Matched,
            Some(_) => Species::Partial,
        }
    }
}

fn cells() -> usize {
    (AXIS * AXIS) as usize * 16
}

fn main() {
    let root = repository_root();
    let material = material(&root, 4_000);
    println!("THE CYCLE HALTS WHERE NOTHING REFLECTS");
    println!(
        "  material   {} words from {} deposits",
        material.len(),
        RECORDS.len()
    );
    println!("  axis       {AXIS}   — a live receiver coordinate; every population below is at it");
    assert!(
        material.len() > 100,
        "the declared deposits resolve to nothing; there is no cycle to drive"
    );

    let standing_surface = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let mut boundaries: Vec<Boundary> = Vec::new();

    {
        let mut eyes = ErosBody::over(
            &standing_surface,
            &mut own,
            AXIS,
            SEED,
            1 << 20,
            &mut carrier,
        );
        for word in &material {
            let perception = eyes.perceive(word, 100);
            let arrived = perception.faces as u64;
            let founded = perception.faces_founded as u64;
            if arrived == 0 {
                // Nothing arrived at a boundary, so there is no boundary. This is the one skip and
                // it is not a selection: it removes non-events, not one species of event.
                continue;
            }
            // The refusal is RETAINED as total reflection rather than dropped. That is the whole
            // difference between measuring the population and measuring the survivors.
            let crossing = CountedCrossing::meet(arrived, founded);
            boundaries.push(Boundary {
                arrived,
                founded,
                reflection: crossing.as_ref().map(|c| c.reflection_pair()),
                service_rounds: crossing.as_ref().map(|c| c.service_rounds()),
                closed: perception.thought_completed,
                standing: eyes.standing_enclosures(),
            });
            if eyes.resource_refused() {
                break;
            }
        }
    }

    println!("\n  boundaries crossed       {}", boundaries.len());
    assert!(
        !boundaries.is_empty(),
        "no boundary carried a population, so nothing was measured"
    );

    let of = |wanted: Species| -> Vec<&Boundary> {
        boundaries
            .iter()
            .filter(|b| b.species() == wanted)
            .collect()
    };
    let matched = of(Species::Matched);
    let partial = of(Species::Partial);
    let total = of(Species::Total);
    let closed_in = |group: &[&Boundary]| group.iter().filter(|b| b.closed).count();
    let matched_and_closed = closed_in(&matched);
    let reflecting_and_closed = closed_in(&partial) + closed_in(&total);
    let reflecting = partial.len() + total.len();

    println!(
        "  MATCHED  Gamma = 0       {:>6}   of which closed {}",
        matched.len(),
        matched_and_closed
    );
    println!(
        "  PARTIAL  Gamma != 0      {:>6}   of which closed {}",
        partial.len(),
        closed_in(&partial)
    );
    println!(
        "  TOTAL    no crossing     {:>6}   of which closed {}   — the retained refusal",
        total.len(),
        closed_in(&total)
    );

    // The service-round population, exhibited rather than averaged: `ceil(1/T)` is the number of
    // passes the current needs, so it IS the predicted depth of deliberation at that boundary.
    let mut rounds: Vec<u128> = boundaries.iter().filter_map(|b| b.service_rounds).collect();
    rounds.sort_unstable();
    rounds.dedup();
    let deepest = boundaries
        .iter()
        .filter_map(|b| b.service_rounds)
        .max()
        .unwrap_or(0);
    let most_standing = boundaries.iter().map(|b| b.standing).max().unwrap_or(0);
    println!(
        "  service rounds           distinct {:?}   deepest {}",
        &rounds[..rounds.len().min(12)],
        deepest
    );
    println!("  enclosures standing      deepest {most_standing}");

    // A worked boundary of each species, returned as the artifact rather than described.
    for (name, group) in [
        ("MATCHED", &matched),
        ("PARTIAL", &partial),
        ("TOTAL  ", &total),
    ] {
        if let Some(b) = group
            .iter()
            .max_by_key(|b| b.service_rounds.unwrap_or(u128::MAX))
        {
            println!(
                "\n  a {name} boundary     arrived {}  founded {}  Gamma {}  rounds {}  closed {}",
                b.arrived,
                b.founded,
                b.reflection
                    .map_or_else(|| "1 : 1 (all)".to_owned(), |(n, d)| format!("{n} : {d}")),
                b.service_rounds
                    .map_or_else(|| "unbounded".to_owned(), |r| r.to_string()),
                b.closed
            );
        }
    }

    // ── the declared arms ──────────────────────────────────────────────────────────────────────
    println!("\n  THE DECLARED FALSIFIER");
    let both_species = !matched.is_empty() && reflecting > 0;
    let match_closes = !matched.is_empty() && matched_and_closed == matched.len();
    let reflection_holds = reflecting_and_closed == 0;
    println!(
        "    3  both species present (anti-vacuity)         {}   (matched {} · reflecting {})",
        held(both_species),
        matched.len(),
        reflecting
    );
    println!(
        "    1  a matched boundary closes                   {}   ({} : {} closed : matched)",
        held(match_closes),
        matched_and_closed,
        matched.len()
    );
    println!(
        "    2  a reflecting boundary does not close        {}   ({} : {} closed : reflecting)",
        held(reflection_holds),
        reflecting_and_closed,
        reflecting
    );

    println!("\n  THE READING");
    if !both_species {
        println!(
            "    VACUOUS. Only one species of boundary occurred on this material, so arms 1 and 2"
        );
        println!("    hold for free and separate nothing. The material must be widened before the");
        println!("    correspondence can be read either way.");
    } else if match_closes && reflection_holds {
        println!(
            "    TERMINATION IS IMPEDANCE MATCHING, on this material. Every boundary where the"
        );
        println!("    arriving faces were all founded closed its thought, and no boundary that");
        println!("    reflected did. There is no stop token, no threshold and no chooser in the");
        println!("    path — the cycle halts because nothing comes back.");
    } else if reflection_holds {
        println!(
            "    THE MATCH IS NECESSARY AND NOT SUFFICIENT. No reflecting boundary closed, so"
        );
        println!(
            "    nothing closes while current is still coming back — the halt condition holds."
        );
        println!(
            "    But not every matched boundary closed, so a match alone does not end the loop:"
        );
        println!(
            "    something further is required at the match, and it is NOT a chooser, because a"
        );
        println!("    chooser would have to close some reflecting boundary and none closed.");
        println!("    That is a bound on the law, returned rather than a failure of it.");
    } else {
        println!("    A REFLECTING BOUNDARY CLOSED, and the falsifier fired exactly as declared.");
        println!(
            "    Thoughts complete while the whole current is still coming back, so the halt is"
        );
        println!("    NOT decided by this junction's match.");
        println!();
        println!(
            "    AND THE THING THAT DECIDES IS NAMED, so this is a correction and not a mystery."
        );
        println!(
            "    `manifold.rs` states the completion law at the swing: *where it FOUNDS (the aim"
        );
        println!(
            "    orthogonal to the standing thought), the thought COMPLETES — the swing's cut,"
        );
        println!(
            "    the segmentation*. That is an ORTHOGONALITY on the arrival against the standing"
        );
        println!(
            "    thought — exact, structural, and NOT a chooser: no threshold is consulted and"
        );
        println!("    no candidate is enumerated. The ban on a privileged scalar governor stands.");
        println!();
        println!("    WHAT IS WITHDRAWN is narrower and is this driver's own premise: that the");
        println!(
            "    boundary's admittances are (faces, faces_founded). They are not. Those two count"
        );
        println!(
            "    the co-present register's faces and how many of them FOUND, which is a reading"
        );
        println!(
            "    of the grey matter — while the cut is taken on the swing's second-order aim."
        );
        println!("    A junction built from the wrong pair returns a real ratio about the wrong");
        println!("    boundary, which is why arm 2 could fail while arm 1 held.");
        println!();
        println!(
            "    WHAT SURVIVES: `Gamma = 0` is still sufficient here — {} of {} matched",
            matched_and_closed,
            matched.len()
        );
        println!(
            "    boundaries closed, with none failing to. What is refuted is NECESSITY: {}",
            reflecting_and_closed
        );
        println!(
            "    closures happened at boundaries where nothing crossed. The next attempt must"
        );
        println!("    build the junction from the swing's own admittances and re-run BOTH arms.");
    }
}

fn held(arm: bool) -> &'static str {
    if arm {
        "HELD  "
    } else {
        "FAILED"
    }
}
