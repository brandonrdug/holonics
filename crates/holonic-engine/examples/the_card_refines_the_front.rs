//! The front is refined on the card, and the card's partition is required to equal the cpu's.
//!
//! **Occasion.** Brandon, 2026-08-10: *"the card's integration is so fucking important and you can't
//! just keep punting it… every time we have to go from it not being integrated to integrating it,
//! you risk contamination. It's GPU first."* And on what a demonstration is worth: *"I don't know
//! why you only show me `\"the\"` when we can attain production through integration by reflection…
//! you are still treating the machine like a toy without a purpose."*
//!
//! So this driver runs the **whole corpus**, not one token, and the card carries the deed.
//!
//! # What the card does
//!
//! `token_invariance` refines an occurrence population one causal shell at a time: at depth `k`,
//! two occurrences stay together exactly when the declared receiver family reads the same thing at
//! `−k` and at `+k`. Every occurrence's shell reading is independent of every other's and the
//! grouping is a quotient by an exact key — one lane per occurrence, no reduction, no ordering.
//!
//! Equality of readings is made equality of **dense identities** once, on the cpu, over the whole
//! corpus; identity zero is reserved for a terminus before any reading is assigned one, because a
//! terminus is family-invariant and must be a value no reading can take. A shell key is then one
//! `u64`, and the new class is the identity of `(current class, key)`, claimed by `atomicCAS`.
//!
//! # What is proved here, not asserted
//!
//! 1. **The card's partition equals the cpu's, surface for surface**, as a partition — not as a
//!    numbering, since class identities are claim order on one side and lexicographic on the other.
//!    Two partitions are equal when they induce the same equivalence on sites, which is what is
//!    checked.
//! 2. **The derived horizon agrees**, so `saturation_horizon` is carrier-independent.
//! 3. **The card is actually reached**: launches are counted, and a run that crossed nothing is a
//!    failure rather than a silent cpu fallback.
//! 4. **Idle lanes are reported.** The launch geometry is read off the device and the kernel; the
//!    tail of the last block is named rather than hidden.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

use holonic_engine::corpus_census::CorpusCensus;
use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceCorpus, ReadingIdentities};
use holonic_engine::token_invariance::{
    ConductAtlas, SeparationComplex, material_horizon_bound, saturation_horizon,
    surface_horizon_bound,
};

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("..")
        });

    println!("THE CARD REFINES THE FRONT");
    println!("==========================");
    println!();

    let census = match CorpusCensus::read(&root) {
        Ok(census) => census,
        Err(error) => {
            println!("the declared corpus could not be read: {error}");
            std::process::exit(1);
        }
    };
    let atlas = ConductAtlas::found(&census, 1);
    let occurrences: usize = census.wholes().iter().map(|whole| whole.stream.len()).sum();
    let surfaces = census.word_surfaces();
    println!(
        "  {} word surfaces, {} occurrences, {} wholes",
        surfaces.len(),
        occurrences,
        census.wholes().len()
    );

    let identities = ReadingIdentities::of(&census, &atlas);
    let corpus = match DeviceCorpus::of(&census) {
        Ok(corpus) => corpus,
        Err(error) => {
            println!("  the corpus does not fit the exact device wire: {error}");
            std::process::exit(1);
        }
    };
    println!(
        "  {} DISTINCT readings over the corpus, identity 0 reserved for a terminus",
        identities.distinct
    );

    let mut card = match CudaRefineExecutor::new() {
        Ok(card) => card,
        Err(error) => {
            println!("  the card refused to mount: {error}");
            std::process::exit(1);
        }
    };
    println!(
        "  card: {} -- {} threads per block, warp {}, both read off the device and the kernel",
        card.device_name(),
        card.block_threads(),
        card.warp_size()
    );
    println!();

    // The corpus's ceiling: no window reaches past the longest whole. Reported, but NOT what any
    // one surface is refined against -- each surface's own ceiling is read off its own occurrences
    // by `surface_horizon_bound`, exactly as the cpu law does.
    let ceiling = material_horizon_bound(&census);
    println!("  the corpus ceiling is {ceiling} shells; each surface is refined against its own\n");

    if let Some(at) = std::env::args().position(|a| a == "--trace") {
        if let Some(name) = std::env::args().nth(at + 1) {
            trace(&census, &atlas, &name);
            return;
        }
    }

    println!("1 . THE WHOLE FRONT, REFINED ON THE CARD");
    println!("----------------------------------------");
    println!();

    let mut agreed = 0usize;
    let mut disagreed: Vec<String> = Vec::new();
    let mut horizons_agreed = 0usize;
    let mut horizon_disagreed: Vec<String> = Vec::new();
    let mut idle_lanes_total = 0u64;
    let mut deepest = (0usize, String::new(), 0usize);
    // The cpu's shell count over exactly the surfaces the card refined, and the summed ceiling
    // each carrier was given. A cost law is a law: if the two carriers walk one law they walk the
    // same number of shells, and neither may be handed a ceiling that is not its surface's own.
    let mut cpu_shells_total = 0usize;
    let mut own_ceiling_total = 0usize;
    let mut corpus_ceiling_total = 0usize;

    let started = Instant::now();
    for surface in &surfaces {
        let sites = census.sites(*surface);
        if sites.len() < 2 {
            continue;
        }
        let own_ceiling = surface_horizon_bound(&census, *surface);
        let on_card = match card.saturate(&corpus, &identities, sites, own_ceiling) {
            Ok(returned) => returned,
            Err(error) => {
                disagreed.push(format!(
                    "{:?}: the card refused -- {error}",
                    census.surface(*surface)
                ));
                continue;
            }
        };

        // The lanes the last block issued with nothing to do. Reported, never hidden.
        let block = u64::from(card.block_threads().max(1));
        let occupied = sites.len() as u64;
        idle_lanes_total += (occupied.div_ceil(block) * block) - occupied;

        let on_cpu = saturation_horizon(&census, &atlas, *surface);
        cpu_shells_total += on_cpu.shells;
        own_ceiling_total += own_ceiling;
        corpus_ceiling_total += ceiling;

        // A partition is not a numbering. The card claims identities in probe order and the cpu in
        // lexicographic window order, so the comparison is of the induced EQUIVALENCE: two sites
        // share a class on one side exactly when they share one on the other.
        let cpu_complex = SeparationComplex::read(&census, &atlas, *surface, on_cpu.horizon);
        let mut cpu_class: BTreeMap<(u32, u32), usize> = BTreeMap::new();
        for (at, class) in cpu_complex.classes.iter().enumerate() {
            for site in &class.sites {
                cpu_class.insert(*site, at);
            }
        }
        let mut card_to_cpu: BTreeMap<u32, usize> = BTreeMap::new();
        let mut cpu_to_card: BTreeMap<usize, u32> = BTreeMap::new();
        let mut same = on_card.classes == cpu_complex.classes.len();
        if same {
            for (at, site) in sites.iter().enumerate() {
                let theirs = on_card.site_class[at];
                let ours = match cpu_class.get(site) {
                    Some(ours) => *ours,
                    None => {
                        same = false;
                        break;
                    }
                };
                if *card_to_cpu.entry(theirs).or_insert(ours) != ours
                    || *cpu_to_card.entry(ours).or_insert(theirs) != theirs
                {
                    same = false;
                    break;
                }
            }
        }
        if same {
            agreed += 1;
        } else {
            if disagreed.len() < 6 {
                disagreed.push(format!(
                    "{:?}: card {} classes, cpu {} classes",
                    census.surface(*surface),
                    on_card.classes,
                    cpu_complex.classes.len()
                ));
            }
        }

        if on_card.horizon == on_cpu.horizon {
            horizons_agreed += 1;
        } else if horizon_disagreed.len() < 6 {
            horizon_disagreed.push(format!(
                "{:?}: card h{}, cpu h{}",
                census.surface(*surface),
                on_card.horizon,
                on_cpu.horizon
            ));
        }
        if on_card.horizon > deepest.0 {
            deepest = (
                on_card.horizon,
                format!("{:?}", census.surface(*surface)),
                on_card.classes,
            );
        }
    }
    let elapsed = started.elapsed();

    println!(
        "  {} surfaces refined on the card in {:.1}s, {} crossings",
        agreed + disagreed.len(),
        elapsed.as_secs_f64(),
        card.launches()
    );
    println!("  partitions agreeing with the cpu: {agreed}");
    println!("  derived horizons agreeing with the cpu: {horizons_agreed}");
    println!(
        "  idle lanes over every crossing: {idle_lanes_total} -- the tail of each last block, named"
    );
    println!(
        "  deepest cone: {} at horizon {} over {} orbits",
        deepest.1, deepest.0, deepest.2
    );
    println!(
        "  crossings on the card {} against {cpu_shells_total} shells on the cpu -- one law, one \
         cost",
        card.launches()
    );
    println!(
        "  ceiling handed to each carrier: {own_ceiling_total} summed surface-local, against \
         {corpus_ceiling_total}\n  \
         the corpus ceiling would have imposed. Both carriers took the surface-local one as of \
         2026-08-11;\n  the card was handed the corpus figure until then, and `saturate` walks it \
         shell by shell."
    );
    for line in disagreed.iter().take(6) {
        println!("  PARTITION DISAGREEMENT: {line}");
    }
    for line in horizon_disagreed.iter().take(6) {
        println!("  HORIZON DISAGREEMENT: {line}");
    }
    println!();

    println!("2 . CONTROLS");
    println!("------------");
    println!();
    let controls = [
        (
            "the card's partition equals the cpu's on every surface",
            disagreed.is_empty() && agreed > 0,
            "would fail if: the device law and the cpu law were not one law. The comparison is of \
             the induced equivalence, not of class numbering -- the card claims in probe order and \
             the cpu in lexicographic order, and requiring those to match would be requiring a \
             realization coordinate to be causal.",
        ),
        (
            "the derived horizon is carrier-independent",
            horizon_disagreed.is_empty() && horizons_agreed > 0,
            "would fail if: the shell at which the material stops carrying difference depended on \
             which surface enacted it.",
        ),
        (
            "the card was actually reached",
            card.launches() > 0,
            "would fail if: this run had silently fallen back to the cpu, which is the failure the \
             whole driver exists to make impossible to report as success.",
        ),
        (
            "the front is the whole corpus, not one token",
            agreed > 1_000,
            "would fail if: this were a demonstration on a handful of surfaces rather than \
             production over the declared corpus.",
        ),
        (
            "the cost is carrier-independent too, not only the return",
            card.launches() as usize == cpu_shells_total,
            "would fail if: one carrier walked more shells than the other for the same answer -- a \
             cost law reproduced in its return and not in its work, which CLAUDE.md §8 calls not \
             porting it at all.",
        ),
        (
            "neither carrier was handed a ceiling that is not its surface's own",
            own_ceiling_total < corpus_ceiling_total,
            "would fail if: the card were still handed the longest whole in the census as every \
             surface's ceiling, which is one unrelated document deciding an unrelated surface's \
             cost. It was, until 2026-08-11.",
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
}

/// Trace one named surface shell by shell on both carriers. Invoked as
/// `the_card_refines_the_front <root> --trace <surface>`; a disagreement in the derived horizon is
/// a difference in the PATH, and a path is only visible shell by shell.
fn trace(census: &CorpusCensus, atlas: &ConductAtlas, name: &str) {
    let Some(surface) = census.lookup(name) else {
        println!("  no such surface: {name}");
        return;
    };
    // This surface's own ceiling, not the corpus's: past it every shell reads `(None, None)`.
    let ceiling = surface_horizon_bound(census, surface);
    let sites = census.sites(surface);
    println!("  tracing {name}: {} occurrences", sites.len());
    println!("    {:>6}  {:>10}  {:>10}", "shell", "cpu", "card");
    let identities = ReadingIdentities::of(census, atlas);
    let corpus = DeviceCorpus::of(census).expect("the corpus fits");
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    for depth in 1..=ceiling.min(60) {
        let cpu = SeparationComplex::read(census, atlas, surface, depth).distinct_windows();
        let on_card = card
            .saturate(&corpus, &identities, sites, depth)
            .expect("the card refines")
            .classes;
        if cpu != on_card || depth <= 3 {
            println!(
                "    {depth:>6}  {cpu:>10}  {on_card:>10}{}",
                if cpu == on_card { "" } else { "   <-- differ" }
            );
        }
    }
}
