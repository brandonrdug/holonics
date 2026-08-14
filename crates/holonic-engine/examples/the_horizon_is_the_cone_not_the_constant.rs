//! The horizon is a reading, not a level, and the cost of a receiver is the volume of its cone.
//!
//! **Occasion.** Brandon, 2026-08-10, on the framing this driver replaces: *"not really a 'window' I
//! don't really like that phrase, it's a light-cone, this is relativistic physics"*, and then
//! directly on the level: *"'horizon' shouldn't be a constant either if it is."*
//!
//! # What was wrong, stated so it can be checked
//!
//! `token_invariance` computes a window per occurrence — `−1, +1, −2, +2, …`, shell by shell in
//! order of `|offset|`. That is a **discrete causal diamond**: the two sides are the two sheets, the
//! shell index is proper distance along the stream, and `None` marks where the whole ends, which is
//! the material's own boundary rather than padding. The horizon is that diamond's radius.
//!
//! Every driver in this repository declared it as a constant — `FOUNDING_HORIZON: usize = 1` — and
//! the surrounding prose called a *different* constant, `DECLARED_CAPACITY: u64 = 8_192`, "the
//! aperture law". Neither is a law. The second guards `C(d, 2)`, the pair population `exhibit`
//! writes out; it bounds a `Vec`, not the work. The first is the one that decides what the receiver
//! can reach at all, and it was authored.
//!
//! # What this driver returns
//!
//! 1. **The derived horizon, per surface**, from `saturation_horizon` — the least radius whose
//!    partition is already final, binary-searched inside the material's own ceiling. Nothing is
//!    declared anywhere in this driver except the corpus root.
//! 2. **The orbit of the excision**: how many surfaces the authored `1` could not see whole, and
//!    the distinctions it missed. An excision that moves nothing is bookkeeping and says so.
//! 3. **The two costs, separated and measured**: the reading is `O(d · h)` — cone volume — and the
//!    exhibition is `C(d, 2)` — a pair product, and a presentation rather than a transport. This is
//!    the distinction the phrase "aperture law" collapsed.
//! 4. **A control**: at the material ceiling every derived horizon must already be final, and no
//!    surface may refine past its own derived horizon. If either fails, the derivation is wrong.
//!
//! # What it does NOT claim
//!
//! No speedup, and no statement about the two organs that die on large corpora. Those die for a
//! reason nobody has measured, and this driver deliberately does not lend them its figures — that
//! borrowing is exactly the error being corrected here.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

use holonic_engine::corpus_census::CorpusCensus;
use holonic_engine::token_invariance::{
    ConductAtlas, corpus_horizon, material_horizon_bound, saturation_horizons,
};

/// The horizon every driver in this repository authored for the READING. Present here **only** so
/// the excision's orbit can be measured against it. It decides nothing.
const EXCISED_AUTHORED_HORIZON: usize = 1;

/// **The founding horizon, declared by this caller and not derived.** `ConductAtlas::found` builds
/// one orthographic signature per surface at this depth, so it is a different quantity from the
/// reading horizon and has its own saturation. Deriving it is owed; declaring it and saying so is
/// lawful under `canon/THE_AUTHORED_LEVEL.md`, and pretending it was derived would not be.
const FOUNDING_DECLARATION: usize = 1;

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("..")
        });

    let census = match CorpusCensus::read(&root) {
        Ok(census) => census,
        Err(error) => {
            println!("the declared corpus could not be read: {error}");
            std::process::exit(1);
        }
    };

    println!("THE HORIZON IS THE CONE, NOT THE CONSTANT");
    println!("=========================================");
    println!();

    let bound = material_horizon_bound(&census);
    let surfaces = census.word_surfaces();
    println!(
        "The material's own ceiling on any horizon is {bound} shells -- the longest whole in the \
         corpus.\nNo window reaches past it, so no horizon above it can refine anything. That \
         number is\nREAD OFF THE CENSUS; nobody declares it.\n"
    );
    println!("  word surfaces          {}", surfaces.len());
    println!("  wholes                 {}", census.wholes().len());
    println!(
        "  occurrences            {}",
        census
            .wholes()
            .iter()
            .map(|w| w.stream.len())
            .sum::<usize>()
    );
    println!();

    // **The founding horizon is a SEPARATE declaration and this driver does not derive it.**
    // `token_invariance` says so in its own source: *"The founding horizon is the caller's, never
    // this organ's, and it need not be the horizon a reading runs at."* What was wrong was never
    // separating the two -- one literal stood for both, so the READING horizon, which is what
    // decides how far a receiver reaches, was authored by a constant named for founding.
    //
    // Founding at the ceiling was tried and is catastrophic for the same reason the binary search
    // was: `ConductAtlas::found` builds an orthographic signature per surface at the founding
    // horizon, so the ceiling costs `total tokens x bound`. Deriving THIS horizon by propagation
    // is owed and is not attempted here.
    let founding = Instant::now();
    let atlas = ConductAtlas::found(&census, FOUNDING_DECLARATION);
    let founding_elapsed = founding.elapsed();
    println!(
        "The conduct axis is founded at {FOUNDING_DECLARATION} -- the caller's declaration, stated \
         rather than derived.\n  Deriving the FOUNDING horizon is owed; what this driver derives \
         is the READING horizon. {:.2}s\n",
        founding_elapsed.as_secs_f64()
    );

    // ------------------------------------------------------------------ the derived horizons
    println!("1 . THE HORIZON, DERIVED PER SURFACE");
    println!("------------------------------------");
    println!();

    let deriving = Instant::now();
    let horizons = saturation_horizons(&census, &atlas);
    let deriving_elapsed = deriving.elapsed();

    let mut by_horizon: BTreeMap<usize, usize> = BTreeMap::new();
    let mut live_total = 0usize;
    let mut shells_total = 0usize;
    let mut own_ceiling_total = 0usize;
    let mut own_ceiling_below_corpus = 0usize;
    for reading in horizons.values() {
        *by_horizon.entry(reading.horizon).or_default() += 1;
        live_total += reading.active_total;
        shells_total += reading.shells;
        own_ceiling_total += reading.bound;
        if reading.bound < bound {
            own_ceiling_below_corpus += 1;
        }
    }
    let occurrences: usize = census.wholes().iter().map(|w| w.stream.len()).sum();

    println!(
        "  derived {} horizons in {:.2}s.\n  \
         COST, in work rather than in a clock: {live_total} occurrence-shells -- the live cone \
         volume,\n  summed over every surface. {shells_total} shells were propagated in total \
         against a corpus ceiling of {bound}.",
        horizons.len(),
        deriving_elapsed.as_secs_f64(),
    );
    println!(
        "  The ceiling-materializing route would have cost occurrences x 2 x bound = {} readings \
         for\n  ONE probe of ONE surface at the widest. That route reached 19.6 GB and was halted.",
        occurrences.saturating_mul(2).saturating_mul(bound)
    );
    println!();
    println!(
        "  THE CEILING IS EACH SURFACE'S OWN, not the corpus's. An occurrence at position p of a\n  \
         whole of length L reaches max(p, L-1-p) shells and reads (None, None) forever after, so\n  \
         a surface's ceiling is the maximum of that over its OWN sites.\n    \
         {own_ceiling_below_corpus} of {} surfaces have a ceiling strictly below the corpus's \
         {bound}\n    \
         {own_ceiling_total} shells, summed surface-local ceiling\n    \
         {} shells, what the corpus ceiling would have imposed on the same surfaces\n  \
         That difference is the bound that binds whenever a surface does NOT exhaust; where every\n  \
         surface exhausts it costs nothing, and this corpus is entirely of the second kind.",
        horizons.len(),
        bound.saturating_mul(horizons.len()),
    );
    println!();
    println!("  the derived horizon population:");
    for (horizon, count) in &by_horizon {
        println!("    horizon {horizon:>4}  ->  {count:>6} surfaces");
    }
    println!();

    let (deepest, forcing) = corpus_horizon(&horizons);
    println!(
        "  the corpus horizon is {deepest}, forced by {} of {} surfaces.",
        forcing.len(),
        horizons.len()
    );
    println!(
        "  A single number over a corpus is a summary, so the forcing population is returned \
         beside it:"
    );
    for surface in forcing.iter().take(8) {
        println!("    {:?}", census.surface(*surface));
    }
    if forcing.len() > 8 {
        println!("    ... and {} more", forcing.len() - 8);
    }
    println!();

    // ------------------------------------------------------------------ the orbit
    println!("2 . THE ORBIT OF THE EXCISION");
    println!("-----------------------------");
    println!();
    println!(
        "  `canon/THE_AUTHORED_LEVEL.md`: an excision is graded by its ORBIT. Lift the level, \
         re-run,\n  exhibit the difference. A wave of excisions reporting no movement has done \
         bookkeeping.\n"
    );

    let moved: Vec<_> = horizons
        .values()
        .filter(|reading| reading.horizon > EXCISED_AUTHORED_HORIZON)
        .collect();
    let unreached: usize = moved.iter().map(|reading| reading.unreached_at_one()).sum();

    println!(
        "  surfaces the authored horizon {EXCISED_AUTHORED_HORIZON} could NOT see whole: {} of {}",
        moved.len(),
        horizons.len()
    );
    println!("  distinctions it missed, summed over those surfaces: {unreached}");
    println!();

    if moved.is_empty() {
        println!(
            "  THE ORBIT IS TRIVIAL on this material: horizon 1 already saturates every surface, \
             so\n  the excision is bookkeeping HERE and this driver says so rather than presenting \
             a green\n  run as evidence. The level is still wrong in principle -- it was authored \
             -- but this\n  corpus cannot grade the repair."
        );
    } else {
        let mut widest: Vec<_> = moved.clone();
        widest.sort_by_key(|reading| std::cmp::Reverse(reading.unreached_at_one()));
        println!("  the surfaces whose cone reaches furthest past the authored level:");
        println!(
            "    {:<24} {:>8} {:>10} {:>10} {:>10}",
            "surface", "horizon", "classes", "at h=1", "unreached"
        );
        for reading in widest.iter().take(12) {
            println!(
                "    {:<24} {:>8} {:>10} {:>10} {:>10}",
                format!("{:?}", census.surface(reading.surface)),
                reading.horizon,
                reading.classes,
                reading.classes_at_one,
                reading.unreached_at_one(),
            );
        }
    }
    println!();

    // ------------------------------------------------------------------ the two costs
    println!("3 . THE TWO COSTS, WHICH ARE DIFFERENT OBJECTS");
    println!("----------------------------------------------");
    println!();
    println!(
        "  reading     O(d . h)   the volume of the causal diamond the window enumerates\n  \
         exhibition  C(d, 2)    the pair product -- a PRESENTATION, not a transport\n"
    );
    println!(
        "  A caller's declared capacity guards only the second. Calling it \"the aperture law\" \
         promoted\n  an output-buffer guard to a law. Measured here, on the same surfaces:\n"
    );
    println!(
        "    {:<24} {:>8} {:>12} {:>18} {:>10}",
        "surface", "horizon", "d (classes)", "C(d,2) to exhibit", "d . h"
    );
    let mut widest: Vec<_> = horizons.values().collect();
    widest.sort_by_key(|reading| std::cmp::Reverse(reading.classes));
    for reading in widest.iter().take(10) {
        let d = reading.classes as u128;
        println!(
            "    {:<24} {:>8} {:>12} {:>18} {:>10}",
            format!("{:?}", census.surface(reading.surface)),
            reading.horizon,
            d,
            d * d.saturating_sub(1) / 2,
            d * reading.horizon as u128,
        );
    }
    println!();
    let worst = widest.first().copied();
    if let Some(reading) = worst {
        let d = reading.classes as u128;
        let pairs = d * d.saturating_sub(1) / 2;
        let cone = d * reading.horizon as u128;
        println!(
            "  the widest surface costs {cone} to READ and {pairs} to EXHIBIT -- a ratio of {:.0}x.",
            pairs as f64 / cone.max(1) as f64
        );
        println!(
            "  The organ already returns its verdict off the reading and never materializes the \
             pairs."
        );
    }
    println!();

    // ------------------------------------------------------------------ the controls
    println!("4 . CONTROLS");
    println!("------------");
    println!();

    // **No control probes at the ceiling.** The first version of this block re-read each surface
    // at `bound` to check that nothing refines past the derived horizon -- which is the exact
    // catastrophic path the derivation was rebuilt to avoid, reintroduced by the control written to
    // guard it. Every check below is answered from evidence the propagation already carries.

    let all_least = horizons.values().all(|reading| reading.is_least());
    let stalled = horizons.values().filter(|r| r.stalled()).count();
    let interior_quiet: usize = horizons.values().map(|r| r.interior_quiet_shells).sum();
    let exhausted = horizons.values().filter(|r| r.exhausted).count();
    let at_ceiling = horizons.len() - exhausted;
    let never_separated = horizons.values().filter(|r| r.horizon == 0).count();

    println!(
        "  termination species -- and only one of the two is a proof:\n    \
         {exhausted:>6} surfaces exhausted to singletons (no deeper shell CAN split: a theorem)\n    \
         {at_ceiling:>6} surfaces reached their own ceiling with classes still plural\n           \
         (those occurrences are indistinguishable to this receiver at ANY depth)\n"
    );
    println!(
        "  {never_separated} of {} surfaces derive horizon 0 -- NO shell ever split them.\n  \
         That reading was reported as horizon 1 until 2026-08-11, by a `last_split.max(1)` inside \
         the\n  organ: an authored floor that no `const` audit could see, and whose unit test was \
         written\n  `if horizon > 1`, excluding exactly the case the floor decided. A surface with \
         one\n  occurrence has nothing to separate, and the honest least final radius of the empty \
         cone is 0.\n",
        horizons.len()
    );
    println!(
        "  {stalled} of {} surfaces have an INTERIOR QUIET shell -- one that split nothing and was\n  \
         followed by a later shell that DID split; {interior_quiet} such shells in total.\n  \
         **THIS MATERIAL DOES GRADE THE LOOP'S SOUNDNESS, and this line said the opposite until\n  \
         2026-08-11.** It read `0 of 29587 surfaces had a QUIET shell before their last split` and \
         then\n  concluded that a sound loop and an unsound one are indistinguishable here. The \
         zero came\n  from `walked_past()`, which returned `shells > horizon` -- FALSE on every \
         propagation that\n  exhausts to singletons, because the last shell walked is the last \
         shell that split. It\n  measured no interior quiet shell at all, so it read zero on \
         material carrying {interior_quiet} of\n  them, and returned FALSE even on the fixture \
         built expressly to exhibit one. A loop halting at\n  the first quiet shell would return \
         the wrong horizon on {stalled} real surfaces of this corpus.\n  The declared control \
         remains, because it exhibits the WITNESS rather than the count:\n  \
         `token_invariance::tests::refinement_stalls_and_the_horizon_is_not_the_first_quiet_shell`\n  \
         writes the unsound loop out and requires it to return 1 where the truth is 3.\n",
        horizons.len()
    );
    // The witnesses, named. A count says a stall happened; these say WHICH two occurrences an
    // early halt would have failed to tell apart, on this corpus, by whole and position.
    println!("  the deepest resumptions, with the pair each one separated:");
    let mut resumptions: Vec<_> = horizons
        .values()
        .filter_map(|reading| reading.first_resumption.map(|r| (reading.surface, r)))
        .collect();
    resumptions.sort_by_key(|(surface, r)| {
        (
            std::cmp::Reverse(r.resumed_at - r.quiet_shell),
            std::cmp::Reverse(r.classes_after - r.classes_before),
            *surface,
        )
    });
    for (surface, r) in resumptions.iter().take(8) {
        println!(
            "    {:<16} quiet at {:>3}, resumed at {:>3}: classes {} -> {}, separating \
             (whole {}, position {}) from (whole {}, position {})",
            format!("{:?}", census.surface(*surface)),
            r.quiet_shell,
            r.resumed_at,
            r.classes_before,
            r.classes_after,
            r.separated.0.0,
            r.separated.0.1,
            r.separated.1.0,
            r.separated.1.1,
        );
    }
    println!();

    let controls = [
        (
            "every derived horizon is LEAST -- one shell shallower was still refining\n       \
             (definition-grade: this CANNOT come out false, see `SaturationHorizon::is_least`;\n       \
             leastness is graded independently by the unit test that rebuilds the shallower\n       \
             partition through `SeparationComplex::read`)",
            all_least,
            "would fail if: nothing -- it is a theorem about the loop, reported as what it is.",
        ),
        (
            "the horizon is final by a theorem on some surfaces, not assumed on all",
            exhausted > 0,
            "would fail if: no surface exhausted to singletons, leaving every horizon resting on \
             the ceiling rather than on a proof.",
        ),
        (
            "the orbit is non-trivial",
            !moved.is_empty(),
            "would fail if: horizon 1 saturated everything, in which case this corpus cannot grade \
             the excision and the run must SAY so rather than read as a repair.",
        ),
        (
            "the cost is the LIVE cone and not the cone",
            live_total < occurrences.saturating_mul(shells_total.max(1)),
            "would fail if: the propagation touched singleton classes, which cannot split -- the \
             work would then be the whole cone rather than the part still carrying difference.",
        ),
        (
            "this material EXERCISES the stall law rather than merely permitting it",
            stalled > 0 && interior_quiet >= stalled,
            "would fail if: no surface here had a quiet shell followed by a splitting one, in \
             which case a loop halting on the first quiet shell would return the same answer as \
             the sound one and this corpus could not tell them apart. It reported exactly that \
             until 2026-08-11, from a gauge that could not see a stall.",
        ),
        (
            "every surface's ceiling is its own and none exceeds the corpus's",
            own_ceiling_total < bound.saturating_mul(horizons.len())
                && horizons.values().all(|r| r.bound <= bound),
            "would fail if: the propagation ran against a corpus-global ceiling, which is one \
             unrelated long document deciding an unrelated surface's cost.",
        ),
    ];

    let mut all = true;
    for (claim, held, why) in controls {
        println!("  [{}] {claim}", if held { "HELD" } else { "FAILED" });
        println!("       {why}");
        all &= held;
    }
    println!();
    println!("ALL CONTROLS HELD: {all}");
    println!();
    println!(
        "The cone is the receiver's relation to its material: apex at the occurrence, two sheets \
         along\nthe stream, and a null boundary where the returned difference is exactly zero. \
         That boundary\nis what `saturation_horizon` computes, and it was a literal `1` in every \
         driver until today."
    );
}
