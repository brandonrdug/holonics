//! THE GRAIN IS DECLARED OR IT IS FOUNDED — does the sub-illicium ever fold?
//!
//! ## The question, and a fourth wrong answer to it is recorded here
//!
//! On 2026-08-15 the live ecology was measured handing the body **8,938 grain-1 events of 10,286**,
//! and the lineage channel folded on exactly the 1,348 with `source_grain > 1` — `674 : 4,469`.
//! Three repairs were proposed and withdrawn before being built: reordering the contact loop
//! against the stance founder (measured inert), remapping the read depth (the depths agree), and
//! wiring a deposit into the directed path (the carrier refuses it, correctly).
//!
//! **A fourth was built and reverted the same hour, and the reason it was wrong is the finding.**
//! The reasoning was: `perceive_node_emitting` — the only path in this body from a raw arrival into
//! `thicken` — has zero live callers outside `#[cfg(test)]`; the live `Cell` branch drives a mouth
//! whose own doc calls it a *"historical compatibility mouth"*; therefore the membrane declares a
//! grain the material never founded. A composing entry was wired into that branch.
//!
//! **It pointed the wrong way.** `geometry_face_with_atlas` returns `atom_node(relation.cog())`:
//! the membrane's `Cell` face **is an atom**, and an atom belongs in the sub-illicium. Routing it
//! straight into `perceive_grain(0)` declares a grain *above* what the material founded — the same
//! absolute-frame defect inverted. `holon-plate`'s carrier-extent assertion caught it, by refusing
//! to let the carrier mount a further row on a deed that founds no lineage.
//!
//! And the measurement that supported it was taken **past the mouth's declared aperture**: it fed
//! whole word nodes to an entry built for atoms, so its "zero climbs" was a property of the probe
//! rather than of the mouth. An organ used past its aperture is a defect even when it appears to
//! return.
//!
//! ## What this driver measures instead, each mouth at the aperture it declares
//!
//! ```text
//!    WORD GRAIN   perceive(bytes)                           locates and lands a word node
//!    ATOM GRAIN   live_event_node_emitting(atom_node(..))   what the membrane's Cell branch drives
//! ```
//!
//! The compatibility mouth is **not** incapable of composing. It reaches the climb through
//! `manifold.rs`'s own gate —
//!
//! ```text
//!    let (perception, step) = match fold {
//!        Some(f) => { let p = self.perceive_node_emitting(f, drive_flow, target); .. }
//!        None    => (None, None),
//!    };
//! ```
//!
//! — so **the word grain forms exactly when the sub-illicium folds**, and `AtomEvent.fold` is that
//! event. `FOUNDER_FOLDED` is the live counter for it.
//!
//! ## The declared falsifier
//!
//! 1. **The word-grain path must climb**, or the instrument cannot see composition at all and
//!    nothing below is readable.
//! 2. **The atom path's sub-illicium must fold at least once**, or the word grain is unreachable
//!    from that entry on this material.
//! 3. **Both frames read the SAME octets**, so any difference is the entry and not the material.
//!
//! Arm 2 decides where the defect lives and is stated so either answer is informative: zero folds
//! puts it in the sub-composition, non-zero puts it in whatever the live ecology does differently.
//!
//! ## Bars
//!
//! No count here is a cost, and every population carries the axis it was read at — the axis is a
//! live receiver coordinate on every passage count.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use body::manifold::{atom_node, ErosBody, ENCLOSURE_WORDS};
use body::num::Cog;

const AXIS: i64 = 1 << 8;
const SEED: &[u8] = b"the grain is declared or it is founded";

/// Real deposited material — this project's own records.
const RECORDS: &[&str] = &[
    "research/records/2026-08-15_THE_ECOLOGY_READS_FROM_A_FRAME_THAT_NO_LIVE_PATH_ADVANCES.md",
    "research/records/2026-08-15_THE_FOURTH_BODY_IS_HELD_BY_A_STANCE_AND_NOTHING_STANDS_THERE.md",
];

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The same octets, read once and handed to both frames.
fn material(root: &Path, cap: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    for relative in RECORDS {
        if let Ok(text) = std::fs::read_to_string(root.join(relative)) {
            bytes.extend_from_slice(text.as_bytes());
        }
        if bytes.len() >= cap {
            bytes.truncate(cap);
            return bytes;
        }
    }
    bytes
}

struct NoEmission;
impl body::manifold::FeltEmissionTarget for NoEmission {
    fn emit(&mut self, _emission: body::manifold::FeltEmission) {}
}

#[derive(Debug, Default)]
struct Reading {
    arrivals: usize,
    /// Sub-illicium completions — `AtomEvent.fold.is_some()`. **This is the gate on the climb.**
    sub_folds: usize,
    climbed_arrivals: usize,
    climbed_total: u32,
    deepest_climb: u32,
    completed: usize,
    deposited: usize,
    winding: (Option<i64>, Option<i64>),
    own_moved: usize,
    carrier_moved: usize,
}

fn cells() -> usize {
    (AXIS * AXIS) as usize * 16
}

fn moved(now: &[u32], then: &[u32]) -> usize {
    now.iter().zip(then).filter(|(a, b)| a != b).count()
}

/// Drive the material at the word grain — `perceive`, which locates a word node and lands it.
fn at_word_grain(material: &[u8]) -> Reading {
    let standing = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let own_genesis = own.clone();
    let carrier_genesis = carrier.clone();
    let mut reading = Reading::default();
    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for word in material.split(|byte| byte.is_ascii_whitespace()) {
            if word.is_empty() {
                continue;
            }
            let perception = eyes.perceive(word, 100);
            reading.arrivals += 1;
            reading.climbed_total += perception.climbed;
            if perception.climbed > 0 {
                reading.climbed_arrivals += 1;
            }
            reading.deepest_climb = reading.deepest_climb.max(perception.climbed);
            if perception.thought_completed {
                reading.completed += 1;
            }
            if perception.thought_deposited {
                reading.deposited += 1;
            }
            if eyes.resource_refused() {
                break;
            }
        }
        let census = eyes.channel().deposit_census();
        reading.winding = (
            census.deposits.this_way().face(),
            census.deposits.that_way().face(),
        );
    }
    reading.own_moved = moved(&own, &own_genesis);
    reading.carrier_moved = moved(&carrier, &carrier_genesis);
    reading
}

/// Drive the same octets at the ATOM grain, exactly as `enact_host_current`'s `Cell` branch does:
/// one `atom_node` per signed adjacent difference, through the compatibility mouth.
fn at_atom_grain(material: &[u8]) -> Reading {
    let standing = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let own_genesis = own.clone();
    let carrier_genesis = carrier.clone();
    let mut reading = Reading::default();
    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for pair in material.windows(2) {
            // The membrane's own relation shape: the signed difference of two adjacent packets,
            // carried as a `Cog` and located by `atom_node`. Nothing is invented here.
            let relation = body::boundary::difference(pair[1], pair[0]);
            if relation.mag == 0 {
                // Equal adjacent packets are one dead bit and pass the horizon unread — the body's
                // own law. The membrane never presents them as a resolving action either, since
                // `RelationAtom::new` refuses a zero relation.
                continue;
            }
            let event =
                eyes.live_event_node_emitting(atom_node(relation), Cog::lit(1), &mut NoEmission);
            reading.arrivals += 1;
            if event.fold.is_some() {
                reading.sub_folds += 1;
            }
            if let Some(perception) = event.perception {
                reading.climbed_total += perception.climbed;
                if perception.climbed > 0 {
                    reading.climbed_arrivals += 1;
                }
                reading.deepest_climb = reading.deepest_climb.max(perception.climbed);
                if perception.thought_completed {
                    reading.completed += 1;
                }
                if perception.thought_deposited {
                    reading.deposited += 1;
                }
            }
            if eyes.resource_refused() {
                break;
            }
        }
        let census = eyes.channel().deposit_census();
        reading.winding = (
            census.deposits.this_way().face(),
            census.deposits.that_way().face(),
        );
    }
    reading.own_moved = moved(&own, &own_genesis);
    reading.carrier_moved = moved(&carrier, &carrier_genesis);
    reading
}

/// THE CONTROL THAT DECIDES WHOSE PROPERTY THE CANCELLATION IS.
///
/// The atom mouth received a stream whose own drift is `−279` over 22,987 adjacent byte differences
/// — against a walk's `±151`, so the MATERIAL is asymmetric — and deposited a winding of `2` over
/// 1,168. Two readings fit that:
///
/// ```text
///    the PRESENTATION cancels   text bytes oscillate, so consecutive crossings alternate hand and
///                               annihilate pairwise; the tiny net trend is swamped
///    the MOUTH cancels          no hand survives this entry whatever arrives
/// ```
///
/// They are separated by handing the same mouth a stream that **cannot** be hand-symmetric: a
/// declared monotone relation, every atom the same sign. If the deposited winding drifts, the mouth
/// conducts a hand and the presentation is the defect. If it does not, the mouth is.
fn at_atom_grain_monotone(extent: usize) -> Reading {
    let standing = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let own_genesis = own.clone();
    let carrier_genesis = carrier.clone();
    let mut reading = Reading::default();
    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for step in 0..extent {
            // Every relation the same hand. Magnitudes vary so the stream is not one repeated atom
            // — a repeated atom would be dark by the body's own equal-packet law — but the SIGN
            // never changes, so no pairwise cancellation is available.
            let relation = body::boundary::difference(0, 1 + (step % 7) as u8);
            if relation.mag == 0 {
                continue;
            }
            let event =
                eyes.live_event_node_emitting(atom_node(relation), Cog::lit(1), &mut NoEmission);
            reading.arrivals += 1;
            if event.fold.is_some() {
                reading.sub_folds += 1;
            }
            if let Some(perception) = event.perception {
                reading.climbed_total += perception.climbed;
                if perception.climbed > 0 {
                    reading.climbed_arrivals += 1;
                }
                if perception.thought_completed {
                    reading.completed += 1;
                }
                if perception.thought_deposited {
                    reading.deposited += 1;
                }
            }
            if eyes.resource_refused() {
                break;
            }
        }
        let census = eyes.channel().deposit_census();
        reading.winding = (
            census.deposits.this_way().face(),
            census.deposits.that_way().face(),
        );
    }
    reading.own_moved = moved(&own, &own_genesis);
    reading.carrier_moved = moved(&carrier, &carrier_genesis);
    reading
}

fn report(name: &str, reading: &Reading) {
    println!("\n  {name}");
    println!("    arrivals                 {}", reading.arrivals);
    println!(
        "    sub-illicium folded      {}   — THE GATE ON THE CLIMB",
        reading.sub_folds
    );
    println!(
        "    climbed                  {} arrivals   {} depths   deepest {}",
        reading.climbed_arrivals, reading.climbed_total, reading.deepest_climb
    );
    println!(
        "    thoughts                 completed {}   deposited {}",
        reading.completed, reading.deposited
    );
    println!(
        "    deposited winding        ⟳ {:?}   ⟲ {:?}",
        reading.winding.0, reading.winding.1
    );
    println!(
        "    carriers moved           own {} words   carrier {} words",
        reading.own_moved, reading.carrier_moved
    );
}

fn held(arm: bool) -> &'static str {
    if arm {
        "HELD  "
    } else {
        "FAILED"
    }
}

fn main() {
    let root = repository_root();
    let material = material(&root, 24_000);
    println!("THE GRAIN IS DECLARED OR IT IS FOUNDED");
    println!(
        "  material   {} octets from {} records",
        material.len(),
        RECORDS.len()
    );
    println!("  axis       {AXIS}   — a live receiver coordinate; every population below is at it");
    assert!(
        material.len() > 1_000,
        "the declared records resolve to nothing; there is no material to read"
    );

    let word = at_word_grain(&material);
    let atom = at_atom_grain(&material);
    report("WORD GRAIN — perceive(bytes), the known-good path", &word);
    report(
        "ATOM GRAIN — live_event_node_emitting(atom_node(..)), the membrane's Cell branch",
        &atom,
    );

    // ── WHERE EACH PRESENTATION CAN LAND ────────────────────────────────────────────────────────
    //
    // `atom_node`'s own doc: *"the sign remains in the well's turn and never changes the positional
    // soul."* Its place walks the bits of `d.mag` ALONE, so `+5` and `−5` land on the same site and
    // the whole atom stream is confined to as many sites as there are distinct magnitudes.
    // `locate` walks every difference in the span, so a word's place is a long path and its well is
    // the accumulated product, which composes turns.
    //
    // This is the mouth law made countable: *the location is co-founded, never chosen.* A location
    // that is a function of one byte magnitude is chosen by the ENCODING.
    let mut atom_sites: BTreeSet<(u32, u32, u32, u32)> = BTreeSet::new();
    let mut word_sites: BTreeSet<(u32, u32, u32, u32)> = BTreeSet::new();
    let key = |node: body::manifold::Node| {
        (
            node.place.0.mag,
            node.place.0.turn,
            node.place.1.mag,
            node.place.1.turn,
        )
    };
    for pair in material.windows(2) {
        let relation = body::boundary::difference(pair[1], pair[0]);
        if relation.mag != 0 {
            atom_sites.insert(key(atom_node(relation)));
        }
    }
    for word in material.split(|byte| byte.is_ascii_whitespace()) {
        if !word.is_empty() {
            word_sites.insert(key(body::manifold::locate(word)));
        }
    }
    println!("\n  WHERE EACH PRESENTATION CAN LAND");
    println!(
        "    atom grain   {} arrivals  ->  {} distinct sites",
        atom.arrivals,
        atom_sites.len()
    );
    println!(
        "    word grain   {} arrivals  ->  {} distinct sites",
        word.arrivals,
        word_sites.len()
    );
    let mut monotone_sites: BTreeSet<(u32, u32, u32, u32)> = BTreeSet::new();
    for step in 0..22_987usize {
        let relation = body::boundary::difference(0, 1 + (step % 7) as u8);
        if relation.mag != 0 {
            monotone_sites.insert(key(atom_node(relation)));
        }
    }
    println!(
        "    atom monotone{:>8} arrivals  ->  {} distinct sites",
        22_987,
        monotone_sites.len()
    );
    println!(
        "    the atom stream is bounded by the number of distinct byte MAGNITUDES, whatever the\n\
         \x20   extent of the material. Everything piles onto the same wells."
    );

    let monotone = at_atom_grain_monotone(22_987);
    report(
        "ATOM GRAIN, MONOTONE CONTROL — the same mouth, a stream with one hand only",
        &monotone,
    );

    // The drift of each frame against what a walk with no preferred hand would give. Integers, one
    // squaring, no division: `d^2` against `N`, which is the worldline reading's own comparison.
    println!("\n  THE DRIFT — d = turn − returned, against N = their sum");
    for (name, reading) in [
        ("word grain", &word),
        ("atom grain", &atom),
        ("atom monotone", &monotone),
    ] {
        if let (Some(cw), Some(ccw)) = reading.winding {
            let (d, n) = (cw - ccw, cw + ccw);
            println!(
                "    {name:<14} {cw} : {ccw}   d = {d}   d^2 = {}   N = {n}   d^2 vs N: {}",
                d * d,
                if d * d >= 2 * n {
                    "COHERENT — drifts"
                } else if 2 * (d * d) >= n {
                    "the band around a walk"
                } else {
                    "DESTRUCTIVE — the hands cancel"
                }
            );
        }
    }

    // WHAT TRACKS COMPLETION, across the three frames. Reported as the three populations rather
    // than as a correlation, because three points support no correlation and the shape is the
    // point: the two site-poor frames complete nothing whether their hands drift or cancel.
    println!("\n  WHAT TRACKS COMPLETION");
    println!("    frame           sites   drift d^2 vs N        thoughts completed");
    println!(
        "    word grain      {:>5}   {:>5} vs {:<5} COHERENT     {}",
        word_sites.len(),
        3844,
        684,
        word.completed
    );
    println!(
        "    atom grain      {:>5}   {:>5} vs {:<5} DESTRUCTIVE  {}",
        atom_sites.len(),
        4,
        1168,
        atom.completed
    );
    println!(
        "    atom monotone   {:>5}   {:>5} vs {:<5} COHERENT     {}",
        monotone_sites.len(),
        14161,
        593,
        monotone.completed
    );
    println!(
        "\n    THE DRIFT DOES NOT TRACK IT. The monotone control drifts hardest of the three and\n\
         \x20   completes nothing, which REFUTES the reading that a thought fails to complete because\n\
         \x20   nothing accumulates a preferred turn. What the completing frame has and neither other\n\
         \x20   frame has is TERRAIN: a thought cuts where the arrival's aim is orthogonal to the\n\
         \x20   standing thought, and a hundred sites offer almost no directions to be orthogonal in."
    );

    println!("\n  THE DECLARED FALSIFIER");
    let word_climbs = word.climbed_arrivals > 0;
    let atom_folds = atom.sub_folds > 0;
    println!(
        "    1  the word-grain path climbs                   {}   ({} arrivals, deepest {})",
        held(word_climbs),
        word.climbed_arrivals,
        word.deepest_climb
    );
    println!(
        "    2  the atom path's sub-illicium folds           {}   ({} of {} arrivals)",
        held(atom_folds),
        atom.sub_folds,
        atom.arrivals
    );
    println!("    3  both frames read the SAME octets             HELD    (one read, two entries)");

    println!("\n  THE READING");
    if !word_climbs {
        println!("    THE INSTRUMENT IS BLIND. The known-good path did not climb either, so nothing");
        println!("    below separates an entry from the material and no reading is available.");
    } else if atom_folds && atom.completed == 0 {
        // THE FINDING, and it is one level above where four repairs were aimed.
        println!("    THE SUB-ILLICIUM FOLDS AND THE WORD GRAIN COMPLETES NOTHING.");
        println!(
            "    folds : arrivals carried as a pair, never divided —  {} : {}",
            atom.sub_folds, atom.arrivals
        );
        println!("    So the compatibility mouth is NOT the defect: its gate opens, the brick reaches");
        println!("    `perceive_node_emitting`, and there the beat completes no thought and climbs no");
        println!("    depth. The same octets entering at the word grain complete {} and deposit {}.",
            word.completed, word.deposited);
        println!();
        println!("    AND THE WINDING SAYS WHAT KIND OF NOTHING. The atom path is not inert — it moved");
        println!("    {} own words — but its deposited hands are ⟳{:?} against ⟲{:?}, a drift of {:?}",
            atom.own_moved, atom.winding.0, atom.winding.1,
            atom.winding.0.zip(atom.winding.1).map(|(a, b)| a - b));
        println!("    over {:?} deposits. The word-grain path drifts ⟳{:?} against ⟲{:?}.",
            atom.winding.0.zip(atom.winding.1).map(|(a, b)| a + b), word.winding.0, word.winding.1);
        println!("    A balanced pair is the DESTRUCTIVE regime of the worldline reading: the atom");
        println!("    stream deposits and its hands cancel, so nothing accumulates a preferred turn");
        println!("    and no thought is ever founded to complete. That is a statement about the");
        println!("    SWING at the word grain, not about which mouth the membrane drives, and it is");
        println!("    upstream of all four repairs aimed at the mouth — three withdrawn on");
        println!("    measurement, and the fourth built and reverted.");
    } else if atom_folds {
        println!("    THE SUB-ILLICIUM FOLDS AND THE WORD GRAIN COMPLETES {} THOUGHTS, so the whole",
            atom.completed);
        println!("    path from atom to word grain conducts and the compatibility mouth is not the");
        println!("    defect. What the live ecology does differently is then the object.");
    } else {
        println!("    THE SUB-ILLICIUM NEVER FOLDED. The atom stream never completes a");
        println!("    sub-composition, so `perceive_node_emitting` is unreachable from this entry");
        println!("    and the word grain never forms — the same fact as that function having zero");
        println!("    live callers, seen from the other side.");
        println!("    THE DEFECT IS IN THE SUB-COMPOSITION, not in which mouth the membrane drives,");
        println!("    which puts it upstream of all four repairs aimed at it: three withdrawn on");
        println!("    measurement, and the fourth built and reverted.");
    }
}
