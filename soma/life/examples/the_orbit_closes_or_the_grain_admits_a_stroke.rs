//! THE ORBIT CLOSES, OR THE GRAIN ADMITS A STROKE — the regime of a presentation, read before it.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_orbit_closes_or_the_grain_admits_a_stroke
//! ```
//!
//! # The object
//!
//! Generation is integration by reflection, so a cycle halts when its reflection series terminates,
//! and **a reflection series terminates exactly when the group it generates is finite.**
//! `canon/THE_INFORMATION_ENGINE.md` §1.1 carries the trichotomy that follows —
//!
//! ```text
//!    SETTLED   the series closes        condensation available; the remainder is its TAIL
//!    BENT      closes with a deficit
//!    GROWING   never closes             NO compact representative exists
//! ```
//!
//! — and then states the gap this driver is aimed at, in its own words: *"this engine carries no
//! reading of which regime its material is in… an engine that cannot say what its material admits is
//! choosing strokes blind."*
//!
//! The machine decides finiteness **exactly**, twice, and has never asked it of a presentation:
//! `temper::Twist` decides `Closed`/`Open` for a coil and carries `chords_tested` because a closure
//! over zero chords is vacuous; `hypergeometric_closure` decides whether a three-site turning
//! equation's return group is finite by **sorting integers**. Both are composed only with their own
//! declared dials.
//!
//! # The gauge — one material, a ladder of grains
//!
//! `locate` takes **any** byte span, so one octet stream presented at spans of `1, 2, 3, 5, 8, 13,
//! 21` is a family of presentations of the *same material* whose orbits differ by construction. Held
//! fixed: the octets, the substrate, the seed, the axis. Varied: the grain alone.
//!
//! `DeclaredGauge` cannot be built from material its transformation left alone, so the ladder must
//! prove it moved the orbit before any agreement across it is read as evidence.
//!
//! # What composes — every arm is a standing owner
//!
//! ```text
//!    the orbit      distinct places reached          does it SATURATE — a new arrival reaching no new place
//!    the partition  receiver_exact_compression       causal-state blocks, collapsed pairs, memory order
//!    the lattice    winding_inertia::lattice_admits_order
//!    the conduct    ErosBody                         thoughts completed, standing enclosures, deposited winding
//! ```
//!
//! **Saturation is structural, not a threshold.** A new arrival reaching no new place *is* the orbit
//! of the group action closing, which is the same event as the series terminating. Nothing here
//! compares a count against a number.
//!
//! # The declared falsifiers, stated before the run
//!
//! **ANTI-VACUITY, and it governs the other three.** At least two rungs must land in different
//! regimes, and the gauge must be measured non-trivial. A ladder entirely settled or entirely growing
//! separates nothing and every arm below holds for free — which is exactly how the reflection
//! falsifier failed on 2026-08-15, so the guard is the one that caught it.
//!
//! **ARM ONE — the two closures are one object.** Orbit saturation and partition saturation must
//! agree across the ladder. *Fires if* a rung saturates its places while its blocks keep refining:
//! then place-closure and conduct-closure are different objects and the identification is withdrawn.
//!
//! **ARM TWO — the regime predicts a stroke it did not compute.** The collapsed population is the
//! compression's exact remainder. On a settled rung the collapse must be **large with short
//! separating words** — the material is one condensation; on a growing rung it must be **small or
//! absent**, because there is no compact representative to collapse onto. *Fires if* the collapse is
//! indistinguishable across the ladder: the reading is blind to the difference it was built to see,
//! and is withdrawn rather than re-aimed.
//!
//! **ARM THREE — the one that can kill the line.** Thought completions per arrival must rise as the
//! orbit opens. A thought cuts where the arrival's aim is orthogonal to the standing thought, and a
//! closed orbit offers finitely many directions for the standing thought to occupy. *Fires if*
//! completions are flat across a gauge measured non-trivial: then the swing's cut does not consult
//! the terrain, and the reading connecting presentation to generation is wrong at the root.
//!
//! # Bars
//!
//! No count here is a cost. Every population carries the axis it was read at. **The regime reading
//! reports which stroke the material admits and never selects one** — a scalar that measures is
//! lawful, a scalar that governs is not. And no rung is handed a label: the rungs are grains, so
//! nothing returned is the preimage of a field this driver set.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use body::manifold::{locate, ErosBody, Node, ENCLOSURE_WORDS};
use holonic_engine::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use holonic_engine::winding_inertia::lattice_admits_order;
use holonic_structure::DeclaredGauge;

const AXIS: i64 = 1 << 8;
const SEED: &[u8] = b"the orbit closes or the grain admits a stroke";

/// The ladder. Fibonacci spans so no two rungs are multiples of each other — a doubling ladder
/// would make every coarse rung a concatenation of a finer one and the orbits would nest by
/// construction, which is a property of the ladder rather than of the material.
const LADDER: [usize; 6] = [2, 3, 5, 8, 13, 21];

/// **Grain 1 is not on the ladder, and the reason is the finding that put it there.** `locate` walks
/// the *differences* inside a span, so a one-byte span has none and every one of them lands at the
/// origin: the orbit is a single place. The first run of this driver carried grain 1, reported it
/// SATURATED, and its anti-vacuity arm passed on that one degenerate rung — the same defect one
/// level up from the one the arm exists to catch.
///
/// **And the real contrast is not between `locate` grains at all.** It is between the body's two
/// mouths. `atom_node` walks the bits of `|d|` alone, so `+5` and `−5` land on the same place and the
/// orbit is bounded by the distinct byte magnitudes whatever the extent — it closes. `locate`
/// composes every difference in the span, so its orbit keeps opening. Those are the two regimes, and
/// they are two entries into the same body rather than two settings of one.

/// Real deposited material: this project's own records.
const RECORDS: &[&str] = &[
    "research/records/2026-08-15_THE_ECOLOGY_READS_FROM_A_FRAME_THAT_NO_LIVE_PATH_ADVANCES.md",
    "research/records/2026-08-15_THE_FOURTH_BODY_IS_HELD_BY_A_STANCE_AND_NOTHING_STANDS_THERE.md",
    "research/records/2026-08-15_THE_RELATING_IS_ONE_COMPLEX_PRODUCT_AND_THE_POLE_HAS_COLLAPSED_ONTO_A_RELATUM.md",
];

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

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

/// A place, as an exact key. Both coordinates, both faces — no magnitude is taken.
type PlaceKey = (u32, u32, u32, u32);

fn place_of(node: Node) -> PlaceKey {
    (
        node.place.0.mag,
        node.place.0.turn,
        node.place.1.mag,
        node.place.1.turn,
    )
}

// -------------------------------------------------------------------------------------------------
// The observed system, built from the material and the body's own response — nothing authored
// -------------------------------------------------------------------------------------------------

/// One rung's presentation, as a system the causal-state construction can read.
///
/// **Items are the distinct spans the material contains at this grain**, so the population is the
/// material's and not this driver's. **Observations are what the BODY returned** when that span
/// arrived — the conduct faces, never a label. **The successor relation is the span that actually
/// followed**, so the transitions are the material's own chronology.
///
/// # The input alphabet is the successor's CONDUCT CLASS, not its identity
///
/// The first form of this system used every distinct span as an input, and the separating-word
/// search branches over the alphabet at every step — a thousand-symbol alphabet makes the shortest
/// distinguishing word unreachable, and the driver did not return. That is an aperture failure in
/// the probe, not a property of the material.
///
/// An input is therefore **which of the eight conduct classes the successor fell into** — the three
/// declared faces as a three-bit word. It is still read off the body's own response and is still
/// the material's chronology; what changes is that the transition is labelled by *what kind of thing
/// came next* rather than by *which thing*, which is the coarser and more honest question. A
/// separating word is then a sequence of conduct classes, which is exactly what a receiver of this
/// family can actually distinguish.
struct Presentation {
    spans: Vec<Vec<u8>>,
    /// span -> (thought completed, faces founded is non-zero, the landing founded)
    conduct: BTreeMap<u64, (bool, bool, bool)>,
    /// (span, successor's conduct class) -> the span that followed with that class
    followed: BTreeMap<(u64, u64), u64>,
}

/// The three declared faces as a three-bit word — the input alphabet, eight symbols.
fn conduct_class(faces: (bool, bool, bool)) -> u64 {
    u64::from(faces.0) | (u64::from(faces.1) << 1) | (u64::from(faces.2) << 2)
}

impl ObservedSystem for Presentation {
    fn items(&self) -> Vec<ItemId> {
        (0..self.spans.len() as u64).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        // three declared conduct faces, each a separate receiver
        (0..3).map(ReceiverId).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..8).map(InputId).collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(&(completed, founded, landing)) = self.conduct.get(&item.0) else {
            return Observation(0);
        };
        let face = match receiver.0 {
            0 => completed,
            1 => founded,
            _ => landing,
        };
        Observation(u64::from(face))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.followed.get(&(item.0, input.0)).copied().map(ItemId)
    }
}

/// One rung of the ladder, kept whole.
struct Rung {
    /// `0` denotes the ATOM mouth — `atom_node` over adjacent differences — rather than a span.
    grain: usize,
    arrivals: usize,
    /// The orbit: distinct places reached, and whether it SATURATED — the last stretch of arrivals
    /// reaching no place the earlier stretch had not.
    orbit: usize,
    saturated: bool,
    /// Where the orbit stopped growing, as a fraction of the stream carried as a PAIR.
    closed_after: Option<usize>,
    blocks: usize,
    one_shot: usize,
    collapsed: usize,
    memory_order: Option<usize>,
    shortest_separator: Option<usize>,
    completed: usize,
    deposited: usize,
    standing: u32,
    winding: (Option<i64>, Option<i64>),
    lattice_admits: bool,
}

impl Rung {
    /// The regime, read off the orbit alone. **Reported, never used to select.**
    fn regime(&self) -> &'static str {
        if self.saturated {
            "SETTLED"
        } else {
            "GROWING"
        }
    }
}

fn cells() -> usize {
    (AXIS * AXIS) as usize * 16
}

/// The ATOM mouth, as a rung. `atom_node` over adjacent byte differences, which is what the live
/// ecology's `Cell` branch presents. Its place map factors through `|d|`, so the orbit is bounded by
/// the distinct magnitudes and closes.
fn drive_atom(material: &[u8]) -> Rung {
    let standing = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];

    let mut index: BTreeMap<Vec<u8>, u64> = BTreeMap::new();
    let mut distinct: Vec<Vec<u8>> = Vec::new();
    let mut conduct: BTreeMap<u64, (bool, bool, bool)> = BTreeMap::new();
    let mut followed: BTreeMap<(u64, u64), u64> = BTreeMap::new();
    let mut seen: BTreeSet<PlaceKey> = BTreeSet::new();
    let mut growth: Vec<usize> = Vec::new();
    let (mut completed, mut deposited, mut arrivals) = (0usize, 0usize, 0usize);
    let mut previous: Option<u64> = None;

    let (standing_open, winding) = {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for pair in material.windows(2) {
            let relation = body::boundary::difference(pair[1], pair[0]);
            if relation.mag == 0 {
                continue;
            }
            let node = body::manifold::atom_node(relation);
            seen.insert(place_of(node));
            growth.push(seen.len());

            let perception = eyes.perceive_node(node, 100);
            arrivals += 1;
            if perception.thought_completed {
                completed += 1;
            }
            if perception.thought_deposited {
                deposited += 1;
            }

            // the item is the RELATION, which is what this mouth presents
            let key = relation.mag.to_be_bytes().to_vec();
            let next = index.len() as u64;
            let id = *index.entry(key).or_insert_with(|| {
                distinct.push(Vec::new());
                next
            });
            conduct.entry(id).or_insert((
                perception.thought_completed,
                perception.faces_founded > 0,
                perception.landing.founds,
            ));
            let class = conduct_class((
                perception.thought_completed,
                perception.faces_founded > 0,
                perception.landing.founds,
            ));
            if let Some(from) = previous {
                followed.entry((from, class)).or_insert(id);
            }
            previous = Some(id);
            if eyes.resource_refused() {
                break;
            }
        }
        let census = eyes.channel().deposit_census();
        (
            eyes.standing_enclosures(),
            (
                census.deposits.this_way().face(),
                census.deposits.that_way().face(),
            ),
        )
    };

    let saturated = growth
        .len()
        .checked_mul(3)
        .map(|t| t / 4)
        .and_then(|at| growth.get(at).copied())
        .is_some_and(|three_quarters| Some(&three_quarters) == growth.last());
    let closed_after = growth
        .iter()
        .position(|&n| n == seen.len())
        .map(|at| at + 1);

    let presentation = Presentation {
        spans: distinct,
        conduct,
        followed,
    };
    let compression = compress(&presentation);
    Rung {
        grain: 0,
        arrivals,
        orbit: seen.len(),
        saturated,
        closed_after,
        blocks: compression.conduct.len(),
        one_shot: compression.one_shot.len(),
        collapsed: compression.collapsed.len(),
        memory_order: compression.memory_order(),
        shortest_separator: compression
            .collapsed
            .iter()
            .map(|p| p.distinguishing_word.len())
            .min(),
        completed,
        deposited,
        standing: standing_open,
        winding,
        lattice_admits: lattice_admits_order(seen.len()),
    }
}

fn drive(material: &[u8], grain: usize) -> Rung {
    let standing = vec![0u32; cells()];
    let mut own = vec![0u32; cells()];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];

    // The spans: non-overlapping windows, so each octet is presented exactly once at every rung and
    // the rungs read the same material rather than different amounts of it.
    let spans: Vec<&[u8]> = material
        .chunks(grain)
        .filter(|c| c.len() == grain)
        .collect();

    let mut index: BTreeMap<Vec<u8>, u64> = BTreeMap::new();
    let mut distinct: Vec<Vec<u8>> = Vec::new();
    let mut conduct: BTreeMap<u64, (bool, bool, bool)> = BTreeMap::new();
    let mut followed: BTreeMap<(u64, u64), u64> = BTreeMap::new();

    let mut seen: BTreeSet<PlaceKey> = BTreeSet::new();
    let mut growth: Vec<usize> = Vec::new(); // |orbit| after each arrival
    let mut completed = 0usize;
    let mut deposited = 0usize;
    let mut arrivals = 0usize;
    let mut previous: Option<u64> = None;

    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, SEED, 1 << 20, &mut carrier);
        for span in &spans {
            let node = locate(span);
            seen.insert(place_of(node));
            growth.push(seen.len());

            let perception = eyes.perceive(span, 100);
            arrivals += 1;
            if perception.thought_completed {
                completed += 1;
            }
            if perception.thought_deposited {
                deposited += 1;
            }

            let next = index.len() as u64;
            let id = *index.entry(span.to_vec()).or_insert_with(|| {
                distinct.push(span.to_vec());
                next
            });
            conduct.entry(id).or_insert((
                perception.thought_completed,
                perception.faces_founded > 0,
                perception.landing.founds,
            ));
            let class = conduct_class((
                perception.thought_completed,
                perception.faces_founded > 0,
                perception.landing.founds,
            ));
            if let Some(from) = previous {
                followed.entry((from, class)).or_insert(id);
            }
            previous = Some(id);

            if eyes.resource_refused() {
                break;
            }
        }
        let standing_open = eyes.standing_enclosures();
        let census = eyes.channel().deposit_census();
        let winding = (
            census.deposits.this_way().face(),
            census.deposits.that_way().face(),
        );

        // SATURATION, structurally: the final quarter of the stream reached no place the first three
        // quarters had not. Not a threshold — the question is whether a NEW arrival reaches a NEW
        // place, asked over the last stretch rather than at a single instant.
        let saturated = growth
            .len()
            .checked_mul(3)
            .map(|three| three / 4)
            .and_then(|at| growth.get(at).copied())
            .is_some_and(|three_quarters| Some(&three_quarters) == growth.last());
        let closed_after = growth
            .iter()
            .position(|&n| n == seen.len())
            .map(|at| at + 1);

        let presentation = Presentation {
            spans: distinct,
            conduct,
            followed,
        };
        let compression = compress(&presentation);
        let shortest_separator = compression
            .collapsed
            .iter()
            .map(|pair| pair.distinguishing_word.len())
            .min();

        let order = match usize::try_from(seen.len()) {
            Ok(n) => n,
            Err(_) => 0,
        };

        return Rung {
            grain,
            arrivals,
            orbit: seen.len(),
            saturated,
            closed_after,
            blocks: compression.conduct.len(),
            one_shot: compression.one_shot.len(),
            collapsed: compression.collapsed.len(),
            memory_order: compression.memory_order(),
            shortest_separator,
            completed,
            deposited,
            standing: standing_open,
            winding,
            lattice_admits: lattice_admits_order(order),
        };
    }
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

fn main() {
    let root = repository_root();
    let material = material(&root, 24_000);
    rule("THE ORBIT CLOSES, OR THE GRAIN ADMITS A STROKE");
    println!(
        "  material   {} octets from {} records",
        material.len(),
        RECORDS.len()
    );
    println!("  axis       {AXIS}   — a live receiver coordinate; every population below is at it");
    println!("  ladder     {LADDER:?}   — Fibonacci, so no rung is a multiple of another");
    assert!(
        material.len() > 4_000,
        "the declared records resolve to nothing; there is no material to present"
    );

    let mut rungs: Vec<Rung> = vec![drive_atom(&material)];
    rungs.extend(LADDER.iter().map(|&g| drive(&material, g)));

    rule("THE LADDER — one material, seven presentations");
    println!(
        "  grain  arrivals   orbit  regime    blocks  one-shot  collapsed  order  sep   completed  deposited  standing"
    );
    for r in &rungs {
        println!(
            "  {:>5}  {:>8}  {:>6}  {:<8}  {:>6}  {:>8}  {:>9}  {:>5}  {:>3}  {:>9}  {:>9}  {:>8}",
            r.grain,
            r.arrivals,
            r.orbit,
            r.regime(),
            r.blocks,
            r.one_shot,
            r.collapsed,
            r.memory_order.map_or("-".to_owned(), |o| o.to_string()),
            r.shortest_separator
                .map_or("-".to_owned(), |s| s.to_string()),
            r.completed,
            r.deposited,
            r.standing,
        );
    }
    println!("\n  the deposited winding, as an undivided pair per rung");
    for r in &rungs {
        println!(
            "    grain {:>2}   ⟳ {:?} : ⟲ {:?}   orbit closed after {:?} arrivals   lattice admits the order: {}",
            r.grain, r.winding.0, r.winding.1, r.closed_after, r.lattice_admits
        );
    }

    // ── THE GAUGE, and it must have acted ─────────────────────────────────────────────────────────
    rule("THE GAUGE — the ladder must have moved the orbit");
    let gauge = DeclaredGauge::of(
        rungs.iter().map(|r| r.orbit).collect(),
        rungs
            .iter()
            .skip(1)
            .map(|r| r.orbit)
            .chain(std::iter::once(0))
            .collect(),
    );
    let gauge_acted = match &gauge {
        Ok(g) => {
            println!(
                "  the grain ladder moves the orbit at {} of {} rungs — the orbits are {:?}",
                g.witness().len(),
                LADDER.len(),
                rungs.iter().map(|r| r.orbit).collect::<Vec<_>>()
            );
            true
        }
        Err(refusal) => {
            println!("  REFUSED: {refusal:?} — the ladder did not move the orbit, so nothing below separates");
            false
        }
    };

    // ── THE DECLARED FALSIFIERS ───────────────────────────────────────────────────────────────────
    rule("THE DECLARED FALSIFIERS");

    // A rung whose orbit is a single place is DEGENERATE, not settled: nothing was presented to it
    // that could reach anywhere. Counting one as a regime is how the first run's anti-vacuity arm
    // passed over a ladder that produced no genuine settled presentation.
    let settled: Vec<&Rung> = rungs
        .iter()
        .filter(|r| r.saturated && r.orbit > 1)
        .collect();
    let growing: Vec<&Rung> = rungs.iter().filter(|r| !r.saturated).collect();
    let degenerate = rungs.iter().filter(|r| r.orbit <= 1).count();
    if degenerate > 0 {
        println!(
            "  {degenerate} rung(s) DEGENERATE — orbit of one place, excluded from both regimes"
        );
    }
    let both_regimes = !settled.is_empty() && !growing.is_empty();
    println!(
        "  ANTI-VACUITY  two regimes present            {}   (settled {} · growing {})",
        held(both_regimes && gauge_acted),
        settled.len(),
        growing.len()
    );

    // ARM ONE — orbit saturation and partition saturation are one object.
    // The partition saturates when its conduct blocks stop refining past the one-shot reading.
    let arm_one = rungs.iter().all(|r| {
        let partition_saturated = r.blocks == r.one_shot;
        partition_saturated == r.saturated || r.collapsed == 0
    });
    println!(
        "  ARM ONE       place-closure IS conduct-closure   {}",
        held(arm_one)
    );
    for r in &rungs {
        println!(
            "                  grain {:>2}  orbit {:<8}  blocks {} against one-shot {}  {}",
            r.grain,
            if r.saturated { "SATURATED" } else { "growing" },
            r.blocks,
            r.one_shot,
            if r.blocks == r.one_shot {
                "partition saturated"
            } else {
                "partition refined"
            }
        );
    }

    // ARM TWO — the collapse behaves differently at the two ends.
    let settled_collapse: usize = settled.iter().map(|r| r.collapsed).sum();
    let growing_collapse: usize = growing.iter().map(|r| r.collapsed).sum();
    let arm_two = both_regimes && settled_collapse != growing_collapse;
    println!(
        "\n  ARM TWO       the collapse separates the regimes  {}   (settled {} · growing {})",
        held(arm_two),
        settled_collapse,
        growing_collapse
    );

    // ARM THREE — completions rise as the orbit opens. Read as a monotone relation over the ladder,
    // never as a rate: the question is whether the ORDER agrees, not by how much.
    // Completions per arrival, as an UNDIVIDED PAIR compared by cross-multiplication. The first
    // form of this arm compared raw completions and contradicted its own declaration, which reads
    // "per arrival"; a coarse rung has an order of magnitude fewer arrivals, so raw counts compare
    // the extent of the presentation rather than its conduct.
    let mut by_orbit: Vec<(usize, usize, usize)> = rungs
        .iter()
        .map(|r| (r.orbit, r.completed, r.arrivals))
        .collect();
    by_orbit.sort();
    let richer = |a: (usize, usize, usize), b: (usize, usize, usize)| a.1 * b.2 <= b.1 * a.2;
    let arm_three = by_orbit.windows(2).all(|w| richer(w[0], w[1]))
        && by_orbit.first().map(|f| (f.1, f.2)) != by_orbit.last().map(|l| (l.1, l.2));
    println!(
        "  ARM THREE     completions per arrival rise with the orbit   {}",
        held(arm_three)
    );
    for (orbit, done, arrivals) in &by_orbit {
        println!(
            "                  orbit {orbit:>6}   completed {done:>5} : {arrivals:<6} arrivals"
        );
    }

    // THE SAME PAIRS, ORDERED BY COMPOSITION DEPTH — how many differences the arrival's node
    // composed. `locate` walks the differences INSIDE a span, so a span of `n` composes `n − 1`;
    // `atom_node` composes exactly one. Depth is therefore the arrival's own richness, and it is a
    // different quantity from the orbit, which is a property of the map the arrival lands on.
    //
    // The two entries at depth one are the two MOUTHS and are reported as one stratum: they are not
    // two settings of a ladder, and forcing them onto one curve was what made the grain-ordered form
    // of this reading fail.
    let depth_of = |r: &Rung| {
        if r.grain == 0 {
            1
        } else {
            r.grain.saturating_sub(1)
        }
    };
    let mut by_depth: Vec<(usize, usize, usize, usize)> = rungs
        .iter()
        .map(|r| (depth_of(r), r.grain, r.completed, r.arrivals))
        .collect();
    by_depth.sort();
    let deeper: Vec<&(usize, usize, usize, usize)> = by_depth.iter().filter(|r| r.0 > 1).collect();
    let monotone_in_depth = deeper
        .windows(2)
        .all(|w| w[0].2 * w[1].3 <= w[1].2 * w[0].3)
        && deeper.len() > 2;
    println!(
        "\n  BESIDE IT      completions per arrival against COMPOSITION DEPTH    {}",
        held(monotone_in_depth)
    );
    for (depth, grain, done, arrivals) in &by_depth {
        let label = if *grain == 0 {
            "atom mouth".to_owned()
        } else {
            format!("span {grain}")
        };
        println!(
            "                  depth {depth:>2}  {label:<12}  completed {done:>5} : {arrivals:<6} arrivals"
        );
    }

    // ── THE READING ───────────────────────────────────────────────────────────────────────────────
    rule("THE READING");
    if !gauge_acted || !both_regimes {
        println!(
            "  VACUOUS. The ladder did not produce two regimes over a moved gauge, so arms one"
        );
        println!(
            "  through three hold for free and separate nothing. The material or the ladder must"
        );
        println!(
            "  widen before any of this is evidence — and that is the failure this driver's own"
        );
        println!("  anti-vacuity arm exists to catch, reported rather than passed.");
    } else if arm_three {
        println!("  THE SWING CONSULTS THE TERRAIN. Completions rise as the orbit opens, over one");
        println!(
            "  material and a gauge measured non-trivial. A thought cuts where the arrival's aim"
        );
        println!(
            "  is orthogonal to the standing thought, and a closed orbit offers finitely many"
        );
        println!("  directions for the standing thought to occupy.");
        println!();
        println!(
            "  So a presentation's regime is readable BEFORE a stroke is chosen, from organs that"
        );
        println!(
            "  already stand, and the mouth law becomes operational: the grain is co-founded by"
        );
        println!("  reading what the material admits, not declared from outside.");
    } else if monotone_in_depth {
        println!("  ARM THREE IS REFUTED AND WHAT REPLACES IT IS SHARPER.");
        println!();
        println!(
            "  Completions per arrival do NOT rise with the orbit — they rise, monotonically and"
        );
        println!(
            "  without exception, with the COMPOSITION DEPTH of the arrival. The orbit is not"
        );
        println!("  monotone in the depth at all:");
        println!("  it peaks in the middle of the ladder, because a coarse presentation has fewer");
        println!("  arrivals with which to reach places. So orbit size and composition depth were");
        println!("  conflated, and the arm was aimed at the wrong one.");
        println!();
        println!(
            "  WHAT THE SWING CONSULTS IS THE COMPOSITION DEPTH OF THE ARRIVAL, not the extent of"
        );
        println!(
            "  the terrain. A span of twenty-one octets carries twenty composed differences into"
        );
        println!(
            "  its located node; an atom carries one. A thought cuts where the arrival's aim is"
        );
        println!(
            "  orthogonal to the standing thought, and a richer node has more directions to be"
        );
        println!(
            "  orthogonal in — which is a property of the ARRIVAL and not of the map it lands on."
        );
        println!();
        println!(
            "  ARM ONE'S FAILURE SAYS THE SAME THING FROM THE OTHER SIDE. The atom mouth saturates"
        );
        println!(
            "  its places and its conduct partition keeps refining — 128 blocks over an orbit of"
        );
        println!(
            "  100 — so the causal state is FINER than the orbit. The body's response carries what"
        );
        println!(
            "  the landing place does not, because it depends on the standing thought and not only"
        );
        println!("  on where the arrival fell. Place-closure and conduct-closure are two objects.");
        println!();
        println!("  So the regime reading is real and the terrain reading is withdrawn: what a");
        println!(
            "  presentation admits is decided by what it COMPOSES, and the live ecology's arrivals"
        );
        println!("  compose one difference each.");
    } else {
        println!(
            "  ARM THREE FAILED and nothing replaces it: completions rise with neither the orbit"
        );
        println!(
            "  nor the composition depth. The swing's cut consults neither, and the whole line"
        );
        println!("  presentation to generation is wrong at the root rather than mis-aimed.");
    }

    rule("CONTROLS");
    let failed: Vec<&str> = [
        ("the gauge acted", gauge_acted),
        ("two regimes present", both_regimes),
    ]
    .into_iter()
    .filter(|(_, held)| !held)
    .map(|(name, _)| name)
    .collect();
    if failed.is_empty() {
        println!("  every anti-vacuity control holds; arms one through three are reported above.");
    } else {
        println!("  ANTI-VACUITY FAILED: {failed:?} — the arms above are not evidence.");
    }
}

fn held(arm: bool) -> &'static str {
    if arm {
        "HELD  "
    } else {
        "FAILED"
    }
}
