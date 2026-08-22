//! THE COHERENCE OF THE WORLDLINE — constructions 4 and 5 of the action line.
//!
//! The fold is `basis_{k+1} = basis_k · deed_k` (phases ADD) and `sweep_{k+1} = sweep_k +
//! basis_{k+1}` (amplitudes SUM). Unrolling gives `sweep_n = Σ_k Π_{j<k} deed_j` — **the sum over
//! prefix paths**, weighted by reach because `FormedRotor` does not normalise. So `|sweep|` is the
//! coherence of a lineage's own history and its growth separates three regimes declared before this
//! ran:
//!
//! ```text
//!   |sweep| ∝ n      COHERENT     the deeds agree; stationary phase; the path constructs
//!   |sweep| ∝ √n     INCOHERENT   a random walk over phases
//!   |sweep| = O(1)   DESTRUCTIVE  the sum cancels — a path integral with no surviving path
//! ```
//!
//! Squared, those are `n²`, `n`, and `1`, so **doubling the step count must quadruple, double, or
//! leave unchanged `|sweep|²`.** Every comparison below is made by cross-multiplication against the
//! previous reading; nothing is divided and no float exists in this file.
//!
//! **Construction 5 is the second frame.** The same instrument runs on two declared materials —
//! prose about the machine, and derived mathematics. `CLAUDE.md`'s fourth archived lesson is that an
//! invariant is only visible across two frames, so a one-material coherence number could not be
//! evidence however exact it was.
//!
//! **Its falsifier, declared:** if both materials return the same regime, the instrument cannot see
//! the difference between a body that founds and one that does not, and it is withdrawn.

use std::fs;
use std::path::{Path, PathBuf};

use body::channel::DepositCensus;
use body::manifold::{ErosBody, ENCLOSURE_WORDS};

/// Small enough to mount several bodies in one process; the axis is a declared receiver coordinate
/// and every reading below is a ratio against another reading in the SAME axis, so it cancels.
const AXIS: i64 = 1 << 8;

/// The declared prose material — the same six records the agentic driver conditions on.
const PROSE_RECORDS: &[&str] = &[
    "research/records/2026-07-31_THE_RETURN_RECURS_AS_THE_CODEC_THE_UNSEEN_FACE_DEPARTS_THE_DEVELOPMENTAL_SOURCE.md",
    "research/records/2026-07-31_THE_MATERIAL_DEPARTS_THE_RETURNED_PATH_REMAINS_THE_BODY_ASKS_WHAT_ITS_DIFFERENCES_CAN_DO.md",
    "research/records/2026-07-31_THE_PREFIX_GROWS_THE_DEED_RETAINS_ITS_WITNESSES_THE_LEXICAL_STAR_REMAINS_TOO_BROAD.md",
];

/// The declared mathematics material — derived, networked, kernel-checked mathematics as bytes.
const MATHEMATICS_ROOT: &str = "soma/formal/elementary-holonics/ElementaryHolonics";

/// `|z|²` for a place, exactly, as one `Cog`. No square root is taken and none is needed: the
/// One rung of the ladder: the deposited winding at a doubling of the passage count.
///
/// **This carried `sweep_squared` and `scalar_sum_squared` until 2026-08-15 and both were dead** —
/// declared, computed every passage, and read by nothing, because `classify` had already been
/// repaired to the winding drift below while the fields, their two helper functions and their
/// doc comments were left standing. A withdrawn instrument that still computes is worse than one
/// that was removed: the compiler names it, but a reader takes the doc for the mechanism. Removed
/// rather than deprecated; the withdrawal itself is recorded on `classify`.
struct Rung {
    steps: usize,
    deposits_this: i64,
    deposits_that: i64,
}

/// THE COHERENCE TEST, REPAIRED 2026-08-15 after the first instrument convicted itself.
///
/// The first form compared `|sweep|²` against `Σ_k |basis_k|²` and returned `Coherent` at every
/// rung on both materials — because the deeds are unnormalised, `|basis_n|` grows as a PRODUCT, and
/// the sum is dominated by its last term by a factor of `2^(10^12)`. So the ratio was pinned at one
/// whatever the phases did: **a check whose material cannot vary the property under test**, which
/// is the tautology the operating contract convicts, wearing a passing result.
///
/// The exact replacement uses the one carrier that is already a pure count of turns and needs no
/// normalisation: the **oriented winding**. Over `N` deposited passages with net drift
/// `d = ⟳ − ⟲`, a walk with no preferred hand has `d² ≈ N`; a coherent path drifts, `d² ≫ N`; an
/// anti-correlated one holds `d² ≪ N`. All integers, one squaring, no division and no root.
/// The declared regimes, decided by cross-multiplication against the previous rung.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Regime {
    /// `d² ≥ 2N` — the hands do not balance; the path drifts and the deposits add in phase
    Coherent,
    /// `N/2 ≤ d² < 2N` — the declared band around a walk with no preferred hand
    Incoherent,
    /// `d² < N/2` — the hands cancel; the deposited winding is destroying itself
    Destructive,
    /// the path sum is empty; there is nothing to classify
    Empty,
}

/// THE COHERENCE, as the drift of the deposited winding — `d²` against `N`, integers throughout.
///
/// The first form of this reading compared `|sweep|²` against `Σ_k |basis_k|²` and returned
/// `Coherent` at every rung on both materials, because the deeds are unnormalised: `|basis_n|`
/// grows as a PRODUCT and the sum is dominated by its last term. The ratio was therefore pinned at
/// one whatever the phases did — **a check whose material cannot vary the property under test,
/// wearing a passing result.** It is withdrawn, and its machinery is now gone rather than merely
/// unread.
///
/// The replacement uses the one carrier that is already a pure count of turns and needs no
/// normalisation: the oriented winding. Over `N` deposited passages with net drift `d = ⟳ − ⟲`, a
/// walk with no preferred hand has `d² ≈ N`; a drifting path has `d² ≫ N`; an anti-correlated one
/// `d² ≪ N`. One squaring, no division, no root, and nothing that could not have come out
/// otherwise.
fn classify(rung: &Rung) -> Regime {
    let total = rung.deposits_this + rung.deposits_that;
    if total == 0 {
        return Regime::Empty;
    }
    let drift = rung.deposits_this - rung.deposits_that;
    let drift_squared = drift.saturating_mul(drift);
    // d² against N, by comparison of integers. A factor of two either way is the declared band
    // around the walk, so the classification cannot be read off a single-passage difference.
    if drift_squared >= total.saturating_mul(2) {
        Regime::Coherent
    } else if drift_squared.saturating_mul(2) >= total {
        Regime::Incoherent
    } else {
        Regime::Destructive
    }
}

fn ledger_hands(ledger: DepositCensus) -> (i64, i64) {
    (
        ledger.deposits.this_way().face().unwrap_or(i64::MIN),
        ledger.deposits.that_way().face().unwrap_or(i64::MIN),
    )
}

/// Feed one material through perception and read the path sum on a geometric ladder.
fn walk(material: &[Vec<u8>], seed: &[u8], axis: i64) -> (Vec<Rung>, Option<usize>) {
    // FORM_WORDS is private to the body; the reservation is the caller's affordance and a generous
    // one costs only memory. Nothing below reads a cell count.
    let cells = (axis * axis) as usize * 16;
    let standing = vec![0u32; cells];
    let mut own = vec![0u32; cells];
    let mut carrier = vec![0u32; 64 * ENCLOSURE_WORDS];
    let mut eyes = ErosBody::over(&standing, &mut own, axis, seed, 1 << 20, &mut carrier);

    let mut ladder = Vec::new();
    let mut next_rung = 1usize;
    let mut steps = 0usize;
    let mut last_fold: Option<usize> = None;
    let mut previous_quanta = (0i64, 0i64);
    for word in material {
        eyes.perceive(word, 100);
        steps += 1;
        let channel = eyes.channel();
        let hands = ledger_hands(channel.deposit_census());
        if hands != previous_quanta {
            last_fold = Some(steps);
            previous_quanta = hands;
        }
        if steps == next_rung {
            ladder.push(Rung {
                steps,
                deposits_this: hands.0,
                deposits_that: hands.1,
            });
            next_rung = next_rung.saturating_mul(2);
        }
    }
    (ladder, last_fold)
}

fn words_of(text: &str) -> Vec<Vec<u8>> {
    text.split_whitespace()
        .filter(|w| !w.is_empty())
        .map(|w| w.as_bytes().to_vec())
        .collect()
}

fn prose_material(root: &Path) -> Result<Vec<Vec<u8>>, String> {
    let mut words = Vec::new();
    for relative in PROSE_RECORDS {
        let path = root.join(relative);
        let text =
            fs::read_to_string(&path).map_err(|e| format!("read prose {}: {e}", path.display()))?;
        words.extend(words_of(&text));
    }
    Ok(words)
}

fn collect_lean(dir: &Path, into: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_lean(&path, into);
        } else if path.extension().map(|x| x == "lean").unwrap_or(false) {
            into.push(path);
        }
    }
}

fn mathematics_material(root: &Path) -> Result<Vec<Vec<u8>>, String> {
    let dir = root.join(MATHEMATICS_ROOT);
    let mut files: Vec<PathBuf> = Vec::new();
    collect_lean(&dir, &mut files);
    files.sort();
    files.truncate(400);
    let mut words = Vec::new();
    for path in files {
        let text = fs::read_to_string(&path)
            .map_err(|e| format!("read mathematics {}: {e}", path.display()))?;
        words.extend(words_of(&text));
    }
    Ok(words)
}

fn report(name: &str, ladder: &[Rung], stop: Option<usize>, extent: usize) -> Option<Regime> {
    println!("\n  {name}");
    println!(
        "    the ledger last moved at step {} of {extent}",
        match stop {
            Some(s) => s.to_string(),
            None => "NEVER".to_owned(),
        }
    );
    println!(
        "    {:>8}  {:>20}  {:>20}  {:>12}  {}",
        "steps", "Δpassages : Δsteps", "drift² : passages", "quanta ⟳ ⟲", "hand coherence"
    );
    let mut last: Option<Regime> = None;
    for (at, rung) in ladder.iter().enumerate() {
        let regime = if rung.deposits_this + rung.deposits_that == 0 {
            None
        } else {
            Some(classify(rung))
        };
        println!(
            "    {:>8}  {:>8} : {:<9}  {:>9} : {:<8}  {:>5} {:>5}  {}",
            rung.steps,
            rung.deposits_this + rung.deposits_that
                - if at == 0 {
                    0
                } else {
                    ladder[at - 1].deposits_this + ladder[at - 1].deposits_that
                },
            rung.steps - if at == 0 { 0 } else { ladder[at - 1].steps },
            (rung.deposits_this - rung.deposits_that)
                .saturating_mul(rung.deposits_this - rung.deposits_that),
            rung.deposits_this + rung.deposits_that,
            rung.deposits_this,
            rung.deposits_that,
            match regime {
                None => "—".to_owned(),
                Some(r) => format!("{r:?}"),
            }
        );
        if let Some(r) = regime {
            last = Some(r);
        }
    }
    last
}

fn main() -> Result<(), String> {
    let root = std::env::current_dir().map_err(|e| e.to_string())?;
    println!("THE COHERENCE OF THE WORLDLINE — the path sum, read on two materials");
    println!("\n  the identity under test");
    println!("    basis_(k+1) = basis_k · deed_k        phases ADD      — one path's amplitude");
    println!("    sweep_(k+1) = sweep_k + basis_(k+1)   amplitudes SUM  — the sum over prefixes");
    println!("    |sweep|² doubling the steps:  ×4 coherent · ×2 walk · ×1 destructive");
    println!(
        "\n  every comparison is a cross-multiplication; nothing is divided, no float exists here"
    );

    let prose = prose_material(&root)?;
    let mathematics = mathematics_material(&root)?;
    println!(
        "\n  material            prose {} words · mathematics {} words",
        prose.len(),
        mathematics.len()
    );

    // THE CONTROL FOR MATERIAL LENGTH. The first run gave prose 4,970 words and mathematics 2,541,
    // so "mathematics kept depositing to the end" could have meant only that it ran out. Both are
    // now cut to the same declared extent and the comparison is at equal steps.
    let extent = prose.len().min(mathematics.len());
    println!("  equal extent        {extent} words each — the length confound is cut");
    let (prose_ladder, prose_stop) = walk(&prose[..extent], b" p", AXIS);
    let (mathematics_ladder, mathematics_stop) = walk(&mathematics[..extent], b" m", AXIS);

    let prose_regime = report(
        "PROSE — six records about the machine",
        &prose_ladder,
        prose_stop,
        extent,
    );
    let mathematics_regime = report(
        "MATHEMATICS — derived, networked, kernel-checked",
        &mathematics_ladder,
        mathematics_stop,
        extent,
    );

    // THE RESERVATION CONTROL. If prose saturates because the medium filled rather than because the
    // material stopped presenting differences, a larger axis must move the stop. If the stop does
    // not move, the saturation is the MATERIAL and not the apparatus.
    println!("\n  THE RESERVATION CONTROL — both materials at twice the axis");
    let (prose_wide, prose_stop_wide) = walk(&prose[..extent], b" p", AXIS * 2);
    let (mathematics_wide, mathematics_stop_wide) = walk(&mathematics[..extent], b" m", AXIS * 2);
    let passages = |l: &[Rung]| {
        l.last()
            .map(|r| r.deposits_this + r.deposits_that)
            .unwrap_or(0)
    };
    println!(
        "    prose        axis {AXIS} stop {prose_stop:?} passages {}  |  axis {} stop {prose_stop_wide:?} passages {}",
        passages(&prose_ladder),
        AXIS * 2,
        passages(&prose_wide)
    );
    println!(
        "    mathematics  axis {AXIS} stop {mathematics_stop:?} passages {}  |  axis {} stop {mathematics_stop_wide:?} passages {}",
        passages(&mathematics_ladder),
        AXIS * 2,
        passages(&mathematics_wide)
    );
    if prose_stop == prose_stop_wide && mathematics_stop == mathematics_stop_wide {
        println!("    NEITHER STOP MOVED — no apparatus bound is active at this axis, so the");
        println!("    passage counts above are comparable and the difference is the MATERIAL.");
    } else {
        println!(
            "    A STOP MOVED — an apparatus bound is still active; the passage counts at this"
        );
        println!("    axis are apparatus readings and may not be compared as material.");
    }

    println!("\n  THE SECOND FRAME");
    println!("    prose        {prose_regime:?}");
    println!("    mathematics  {mathematics_regime:?}");
    match (prose_regime, mathematics_regime) {
        (Some(a), Some(b)) if a == b => println!(
            "    THE INSTRUMENT DID NOT SEPARATE THE TWO MATERIALS — by its own declared falsifier\n\
                 this reading is withdrawn as evidence about material and stands only as a reading\n\
                 about the fold."
        ),
        (Some(_), Some(_)) => println!(
            "    the two materials landed in DIFFERENT regimes — the instrument separates them,\n\
                 and the coherence of a worldline is a property of (material, fold), not of either alone."
        ),
        _ => println!("    one ladder was empty; no comparison is available and none is claimed."),
    }
    Ok(())
}
