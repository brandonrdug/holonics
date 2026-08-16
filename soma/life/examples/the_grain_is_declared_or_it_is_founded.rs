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
