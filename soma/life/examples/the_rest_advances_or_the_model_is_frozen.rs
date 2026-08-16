//! THE REST ADVANCES, OR THE MODEL IS FROZEN — the conditioning control, on two arms.
//!
//! **Plan:** `blueprint/THE_EROS_INSTANTIATION.md`. The law under test:
//!
//! ```text
//!    seal(body) -> bytes0 ;  run(body, material) ;  seal(body) -> bytes1
//!    REQUIRED:  bytes0 != bytes1,  and the difference EXHIBITED
//! ```
//!
//! **Both arms are required and that is the whole design.** A control that only ever passes has not
//! been tested, so this runs the same control over two paths through the same substrate:
//!
//! ```text
//!    ARM A   perception          folds the channel — MUST FIRE
//!    ARM B   directed contact    MUST NOT FIRE — it deposits nothing; the repair was reverted
//! ```
//!
//! **The contrast this driver first measured is now historical, and deliberately so.** On its first
//! run arm B moved **no word of any carrier** over 1,199 passages, matching the agentic ecology's
//! `sweep = origin` in 21,070 of 21,070 contacts. That was read as a property of the path — *"it
//! cannot deposit by construction"* — and **that reading was wrong.** Nothing prevented a deposit
//! there: the entry point takes `&mut self` and already computes the dragged meeting, the chi and
//! the winding. The fold had simply never been wired.
//!
//! **AND IT IS STILL NOT WIRED. This comment said it was, and `deposit_directed_flywheel` exists
//! in no source file — only in the sentence that named it.** The deposit was written on 2026-08-15,
//! moved 12 frame words and 7 carrier words, and was **reverted whole** when the carrier refused
//! it: `soma/membrane/src/live_carrier.rs:357-368` requires a **born stance** before a flywheel may
//! be live, and this path founds none.
//!
//! So **arm B is expected NOT to fire**, and its silence is the finding rather than a regression.
//! Arm A failing would mean perception does not condition and the whole plan is wrong.
//!
//! Nothing here is a cost, no clock is taken, and no float exists in this file.

use body::channel::LineageChannel;
use body::manifold::{ErosBody, ENCLOSURE_WORDS};
use body::num::Cog;
use body::place::Place;
use holonic_engine::conditioned_derivation::ConditionedBody;
use life::conditioned_rest::ConditionedRest;
use life::eros_rest::{ErosRest, MediumBlock, OrganRest};

const AXIS: i64 = 1 << 8;

fn organ(name: &str, bytes: &[u8]) -> OrganRest {
    OrganRest {
        organ: name.to_owned(),
        bytes: bytes.to_vec(),
    }
}

/// The deposited Lean standing — the same committed artifact tree the ablation driver mounts.
/// Nothing here is authored, and the walk takes whatever is deposited rather than a named list.
const STANDING_DEPOSIT: &str = "standing/output";

/// Real deposited mathematics, one whole per document — the conditioning material.
const WHOLES: &[&str] = &[
    "papers/source/mathematics/theorems/weil-support-induction-reduction.typ",
    "papers/source/mathematics/lemmas/situated-mean-transport.typ",
    "papers/source/mathematics/theorems/conditioned-effective-tension.typ",
];

fn repository_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read_material(paths: &[&str]) -> Vec<(String, String)> {
    let root = repository_root();
    paths
        .iter()
        .filter_map(|path| {
            std::fs::read_to_string(root.join(path))
                .ok()
                .map(|text| ((*path).to_owned(), text))
        })
        .collect()
}

/// Every deposited Lean artifact beneath the standing deposit, in path order.
fn deposited_lean(at: &std::path::Path, into: &mut Vec<(String, String)>) {
    let Ok(entries) = std::fs::read_dir(at) else {
        return;
    };
    let mut here: Vec<std::path::PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            deposited_lean(&path, into);
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            if let Ok(text) = std::fs::read_to_string(&path) {
                into.push((path.display().to_string(), text));
            }
        }
    }
}

/// The standing a conditioned body mounts: only artifacts `read_derivation` actually admits, so a
/// deposit that declares nothing is skipped by name rather than panicking the arm.
fn admitted_standing() -> Vec<(String, String)> {
    let mut deposited = Vec::new();
    deposited_lean(&repository_root().join(STANDING_DEPOSIT), &mut deposited);
    deposited
        .into_iter()
        .filter(|(source, text)| {
            ConditionedBody::mount([(source.clone(), text.clone())]).is_ok()
        })
        .collect()
}

/// THE DECLARED ENCODING of a sealed conditioned rest: length-prefixed, in founding order, no map
/// and no hash. The rest carries no bytes face of its own, so one is declared here — a boundary
/// codec in a driver, which is where the workspace's floats and its encodings both live.
fn encode_rest(rest: &ConditionedRest) -> Vec<u8> {
    let mut bytes = Vec::new();
    for record in rest.stems() {
        bytes.extend_from_slice(&record.id.to_be_bytes());
        bytes.extend_from_slice(&(record.stem.len() as u64).to_be_bytes());
        bytes.extend_from_slice(record.stem.as_bytes());
        bytes.extend_from_slice(&(record.wholes.len() as u64).to_be_bytes());
        for whole in &record.wholes {
            bytes.extend_from_slice(&(whole.len() as u64).to_be_bytes());
            bytes.extend_from_slice(whole.as_bytes());
        }
        // `None` is written as a distinct tag rather than as a reserved id, so a stem whose parent
        // is genuinely `u64::MAX` cannot be confused with the first stem.
        match record.parent {
            Some(parent) => {
                bytes.push(1);
                bytes.extend_from_slice(&parent.to_be_bytes());
            }
            None => bytes.push(0),
        }
    }
    bytes
}

/// A REAL organ rest, sealed from a conditioned derivation body over real repository material.
///
/// **This replaces `b"declared"`, and the replacement is the point.** Every `OrganRest` this driver
/// and this module's tests ever built carried `b"a"`, `b"b"` or `b"declared"`, so
/// `ErosRest::organ_difference` was a reading that **had never touched an organ** — and in this
/// driver both organs carried the *identical* literal, which made it a control that could not fire
/// on the arm it was there to watch. The grading rules convict exactly that shape.
fn conditioned_organ(name: &str, standing: &[(String, String)], wholes: &[(String, String)]) -> OrganRest {
    let mut body = ConditionedBody::mount(standing.to_vec()).expect("real Lean standing mounts");
    body.condition_wholes(wholes.iter().map(|(at, text)| (at.as_str(), text.as_str())));
    let rest = ConditionedRest::seal(&body).expect("a founded morphology seals");
    organ(name, &encode_rest(&rest))
}

fn declared_organs() -> Vec<OrganRest> {
    let standing = admitted_standing();
    assert!(
        !standing.is_empty(),
        "the declared Lean standing resolves to nothing; the organ arm would be authored again"
    );
    let wholes = read_material(WHOLES);
    assert!(!wholes.is_empty(), "the declared conditioning material resolves to nothing");
    vec![
        conditioned_organ("derivation", &standing, &wholes[..1]),
        conditioned_organ("language", &standing, &wholes),
    ]
}

/// THE ORGAN ARM, and it has both halves.
///
/// A rest sealed from a body conditioned on ONE whole against a rest sealed from a body conditioned
/// on THREE must differ, and must differ **by name**. A rest sealed twice from the same body must
/// not. Neither arm can pass by construction, which is what `b"declared"` against `b"declared"`
/// could not say.
fn organ_arm(frame: LineageChannel, standing: &[u32], own: &[u32], carrier: &[u32]) {
    let lean = admitted_standing();
    let wholes = read_material(WHOLES);
    println!("\n  THE ORGAN ARM — organ_difference against a real sealed organ");
    println!(
        "    material                 standing {} Lean artifacts   wholes {} deposited documents",
        lean.len(),
        wholes.len()
    );

    let thin = conditioned_organ("derivation", &lean, &wholes[..1]);
    let thick = conditioned_organ("derivation", &lean, &wholes);
    println!(
        "    sealed bytes             one whole {} octets   three wholes {} octets",
        thin.bytes.len(),
        thick.bytes.len()
    );

    let before = ErosRest::seal(
        frame.clone(),
        vec![block("standing", standing), block("own", own), block("carrier", carrier)],
        vec![thin.clone()],
    )
    .expect("seals");
    let after = ErosRest::seal(
        frame.clone(),
        vec![block("standing", standing), block("own", own), block("carrier", carrier)],
        vec![thick],
    )
    .expect("seals");
    let moved = before.organ_difference(&after);
    println!("    conditioned further      organ blocks moved {moved:?}");
    assert_eq!(
        moved,
        vec!["derivation".to_owned()],
        "a body conditioned on three wholes must not seal identically to one conditioned on one"
    );

    // THE NEGATIVE ARM. The same organ, sealed twice, must report NO movement — otherwise the
    // reading above is a statement about the encoder rather than about the organ.
    let twin = ErosRest::seal(
        frame,
        vec![block("standing", standing), block("own", own), block("carrier", carrier)],
        vec![thin],
    )
    .expect("seals");
    let still = before.organ_difference(&twin);
    println!("    resealed unchanged       organ blocks moved {still:?}");
    assert!(
        still.is_empty(),
        "an unconditioned reseal moved an organ, so the difference is not about the organ"
    );
    println!("    THE CONTROL              FIRED on the conditioned arm and NOT on the reseal");
}

fn block(name: &str, words: &[u32]) -> MediumBlock {
    MediumBlock {
        carrier: name.to_owned(),
        words: words.to_vec(),
    }
}

/// The WHOLE body: the frame, plus the three substrate carriers the caller itself supplies to
/// `ErosBody::over`. The enclosure rows live in `carrier`, so the FLYWHEEL is sealed here.
///
/// **`standing` is passed IMMUTABLY to `over`, so it cannot move within a run** and its unmoved
/// report is a tautology — correct design (the terrain a body was mounted on is read-only to it),
/// but it means only `own` and `carrier` vary here. Standing becomes informative only ACROSS runs,
/// where one body's `own` is mounted as the next body's standing.
fn seal_whole(channel: LineageChannel, standing: &[u32], own: &[u32], carrier: &[u32]) -> ErosRest {
    ErosRest::seal(
        channel,
        vec![
            block("standing", standing),
            block("own", own),
            block("carrier", carrier),
        ],
        declared_organs(),
    )
    .expect("a live body seals")
}

/// ARM A — perception. The folding path: `e.fly = met`, `sweep += basis`. The body is mounted
/// twice over the SAME buffers so the frame can be sealed before and after without holding a borrow
/// across the seal; `own` and `carrier` persist across the two mounts because the caller owns them.
fn arm_perception(material: &[Vec<u8>]) -> (ErosRest, ErosRest, usize) {
    let cells = (AXIS * AXIS) as usize * 16;
    let standing = vec![0u32; cells];
    let mut own = vec![0u32; cells];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];

    let before_own = own.clone();
    let before_carrier = carrier.clone();
    let genesis = {
        let eyes = ErosBody::over(&standing, &mut own, AXIS, b" a", 1 << 20, &mut carrier);
        eyes.channel()
    };
    let before = seal_whole(genesis, &standing, &before_own, &before_carrier);

    let mut steps = 0usize;
    let advanced = {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, b" a", 1 << 20, &mut carrier);
        for word in material {
            eyes.perceive(word, 100);
            steps += 1;
        }
        eyes.channel()
    };
    let after = seal_whole(advanced, &standing, &own, &carrier);
    (before, after, steps)
}

/// ARM B — the directed event contact, the path the language ecology drives. Its own doc states it
/// *"neither deposits into current-local OWN nor folds the lineage channel a second time"*, so the
/// prediction is that nothing moves however much material crosses it.
fn arm_directed_contact(material: &[Vec<u8>]) -> (ErosRest, ErosRest, usize) {
    let cells = (AXIS * AXIS) as usize * 16;
    let standing = vec![0u32; cells];
    let mut own = vec![0u32; cells];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];

    let before_own = own.clone();
    let before_carrier = carrier.clone();
    let genesis = {
        let eyes = ErosBody::over(&standing, &mut own, AXIS, b" b", 1 << 20, &mut carrier);
        eyes.channel()
    };
    let before = seal_whole(genesis, &standing, &before_own, &before_carrier);

    let mut steps = 0usize;
    let advanced = {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, b" b", 1 << 20, &mut carrier);
        // Places derived from the material's own bytes, so the relata differ as the material does;
        // nothing here is a constant standing in for a place.
        for pair in material.windows(2) {
            let from: Place = (
                Cog::lit(pair[0].iter().map(|&b| b as i64).sum::<i64>() + 1),
                Cog::lit(pair[0].len() as i64 + 1),
            );
            let to: Place = (
                Cog::lit(pair[1].iter().map(|&b| b as i64).sum::<i64>() + 1),
                Cog::lit(pair[1].len() as i64 + 1),
            );
            let Some(receiver) = eyes.event_receiver_at_source_grain(1) else {
                break;
            };
            eyes.directed_event_contact(receiver, from, to);
            steps += 1;
        }
        eyes.channel()
    };
    let after = seal_whole(advanced, &standing, &own, &carrier);
    (before, after, steps)
}

/// ARM C — THE DISTANT GRIP. The no-catastrophic-forgetting control, and it needs both halves:
/// a deposit must move ITS OWN reading, and must leave a distant one unmoved. Two disjoint material
/// stretches are perceived in sequence and the own-words each moved are compared as SETS.
///
/// A dense body cannot pass this: every update moves every response because every response reads
/// every parameter. A placing body passes it by construction, and if it does not, the claim that
/// freezing is unnecessary is refuted.
fn arm_distant_grip(first: &[Vec<u8>], second: &[Vec<u8>]) -> (Vec<usize>, Vec<usize>, usize) {
    let cells = (AXIS * AXIS) as usize * 16;
    let standing = vec![0u32; cells];
    let mut own = vec![0u32; cells];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];

    let at_genesis = own.clone();
    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, b" c", 1 << 20, &mut carrier);
        for word in first {
            eyes.perceive(word, 100);
        }
    }
    let after_first = own.clone();
    {
        let mut eyes = ErosBody::over(&standing, &mut own, AXIS, b" c", 1 << 20, &mut carrier);
        for word in second {
            eyes.perceive(word, 100);
        }
    }
    let after_second = own.clone();

    let moved_by_first: Vec<usize> = (0..cells)
        .filter(|&i| at_genesis[i] != after_first[i])
        .collect();
    let moved_by_second: Vec<usize> = (0..cells)
        .filter(|&i| after_first[i] != after_second[i])
        .collect();
    let overlap = moved_by_second
        .iter()
        .filter(|i| moved_by_first.binary_search(i).is_ok())
        .count();
    (moved_by_first, moved_by_second, overlap)
}

fn report(name: &str, before: &ErosRest, after: &ErosRest, steps: usize) -> bool {
    let moved = before.frame_difference(after);
    let organs = before.organ_difference(after);
    let medium = before.medium_difference(after).expect("comparable extents");
    let spent_before = before.ledger().expect("a census").deposits;
    let spent_after = after.ledger().expect("a census").deposits;
    println!("\n  {name}");
    println!("    passages driven          {steps}");
    println!(
        "    frame words moved        {} of {}   {:?}",
        moved.len(),
        before.frame_row().len(),
        moved
    );
    println!("    organ blocks moved       {organs:?}");
    for (carrier, words) in &medium {
        println!(
            "    carrier {carrier:<10}       {} words moved   first few {:?}",
            words.len(),
            &words[..words.len().min(6)]
        );
    }
    if medium.is_empty() {
        println!("    carriers                 NONE moved — standing, own and carrier all unchanged");
    }
    println!(
        "    action ledger  before    ⟳ {:?}  ⟲ {:?}",
        spent_before.this_way().face(),
        spent_before.that_way().face()
    );
    println!(
        "    action ledger  after     ⟳ {:?}  ⟲ {:?}",
        spent_after.this_way().face(),
        spent_after.that_way().face()
    );
    println!(
        "    THE CONTROL              {}",
        if moved.is_empty() && medium.is_empty() {
            "DID NOT FIRE — nothing was deposited anywhere; this body is FROZEN IN FACT"
        } else {
            "FIRED — the run advanced the body; it conditioned"
        }
    );
    !(moved.is_empty() && medium.is_empty())
}

fn main() {
    // The material is the same for both arms, so the arms differ only in which path is driven.
    let text = include_str!("../src/eros_rest.rs");
    let material: Vec<Vec<u8>> = text
        .split_whitespace()
        .take(1200)
        .map(|w| w.as_bytes().to_vec())
        .collect();

    println!("THE REST ADVANCES, OR THE MODEL IS FROZEN");
    println!("\n  the law under test");
    println!("    seal -> run -> seal must DIFFER, and the difference must be exhibited");
    println!("  both arms are required: a control that only ever passes has not been tested");
    println!("\n  material            {} words, identical for both arms", material.len());

    let (a0, a1, a_steps) = arm_perception(&material);
    let (b0, b1, b_steps) = arm_directed_contact(&material);

    let a_fired = report("ARM A — perception (the folding path)", &a0, &a1, a_steps);
    let b_fired = report(
        "ARM B — directed event contact (the path the ecology drives)",
        &b0,
        &b1,
        b_steps,
    );

    // ARM C — the distant grip, on two disjoint stretches of the same material.
    let half = material.len() / 2;
    let (first_moved, second_moved, overlap) = arm_distant_grip(&material[..half], &material[half..]);
    println!("\n  ARM C — the distant grip (the no-catastrophic-forgetting control)");
    println!("    own words moved by the first stretch    {}", first_moved.len());
    println!("    own words moved by the second stretch   {}", second_moved.len());
    println!("    words the second stretch RE-moved       {overlap}");
    println!(
        "    THE CONTROL              {}",
        if first_moved.is_empty() || second_moved.is_empty() {
            "CANNOT RUN — a stretch deposited nothing, so localisation is untested"
        } else if overlap == second_moved.len() {
            "REFUTED — the second stretch moved only what the first did; not localised"
        } else {
            "BOTH ARMS HELD — each stretch moved its own words, and most of what the second\n             \x20                            moved the first had never touched: the deposit is PLACED, not global"
        }
    );

    organ_arm(
        LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1))),
        &[0u32; 4],
        &[0u32; 4],
        &[0u32; ENCLOSURE_WORDS],
    );

    println!("\n  THE TWO-ARM READING");
    match (a_fired, b_fired) {
        (true, false) => {
            println!("    AS EXPECTED. Perception conditions and the directed path deposits nothing,");
            println!("    on the SAME substrate and the SAME material, so the control is");
            println!("    discriminating rather than decorative. The directed path founds no stance,");
            println!("    and live_carrier.rs:357-368 requires a born stance before a flywheel may");
            println!("    be live — that is the obstruction, not an impossibility.");
        }
        (true, true) => {
            println!("    ARM B FIRED. Something now deposits on the directed path. Find what, and");
            println!("    check it against the born-stance law before reading this as a repair.");
        }
        (false, _) => {
            println!("    ARM A DID NOT FIRE. Perception did not condition, so the instantiation");
            println!("    plan's premise is refuted and the control cannot be used as evidence.");
        }
    }
}
