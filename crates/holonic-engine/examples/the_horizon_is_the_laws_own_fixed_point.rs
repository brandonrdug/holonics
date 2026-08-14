//! The chronology horizon a capacitance reading conducts at, taken from the transport law's own
//! fixed point instead of from an authored guess and an authored doubling schedule.
//!
//! ```text
//! cargo run --release --example the_horizon_is_the_laws_own_fixed_point -- standing/output
//! ```
//!
//! `crates/holonic-engine/src/derivation_capacitance.rs` carried, until 2026-08-09, an authored
//! level: `HORIZON_DOUBLINGS = 64`, guarding a schedule that started the horizon at
//! `site_count * longest_characteristic_delay` and doubled it until the circuit returned whole.
//! `canon/THE_AUTHORED_LEVEL.md` §5.1 names its replacement in four words — *the transport law's own
//! fixed point* — and this driver conducts the difference.
//!
//! **What the excised schedule was, restated so it can be run rather than remembered.**
//! `holonic_engine::derivation_capacitance::excised_doubling_schedule` is that schedule verbatim,
//! parameterized by a coverage predicate, so every figure below marked *"excised"* is produced by
//! the code that was cut and not by a memory of it.
//!
//! Three claims, each measured here:
//!
//! 1. **The guess is not a bound.** `passage_delay = characteristic_delay + service_rounds - 1` and
//!    the service rounds grow with the accumulated branch population, which is multiplicative along
//!    converging routes. `doubling_ladder(base, rungs)` has `base + 2*rungs` sites and completes at
//!    `2 + base*(2^rungs - 2)`, so the guess is short by a margin that doubles with every rung.
//! 2. **The doubling quantized the return.** The reported horizon could only be `guess * 2^k`, so
//!    two circuits with one site count and one longest delay report identically however far apart
//!    their completion chronologies are. `doubling_ladder(2, 5)` and `doubling_ladder(4, 4)` are
//!    that pair, and the fixed point separates them.
//! 3. **The refusal could not fire.** From any positive guess, `saturating_mul(2)` reaches
//!    `u64::MAX` inside sixty-four steps, and at `u64::MAX` the horizon gates nothing. The `64` was
//!    guarding a state no material can reach.
//!
//! The driver exits non-zero if any declared control fails.

use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    CircuitAperture, Derivation, DerivationCircuit, found_circuit, read_derivation,
};
use holonic_engine::derivation_capacitance::{
    CapacitanceMapping, CapacityLaw, CharacteristicDelayLaw, disjoint_terrain, doubling_ladder,
    doubling_ladder_completion, excised_doubling_schedule, many_result_star, one_result_star,
};

/// Every `.lean` artifact under `root`, in a stable filename order. The same walk
/// `the_terrain_dilates_the_passage` performs, so the two drivers read one deposit.
fn artifact_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(artifact_paths(&path));
        } else if path.extension().is_some_and(|kind| kind == "lean") {
            found.push(path);
        }
    }
    found
}

/// The horizon the excised schedule reports on this mapping, and how many doublings it took.
fn excised(mapping: &CapacitanceMapping) -> (u64, u32) {
    excised_doubling_schedule(
        mapping.site_count(),
        mapping.longest_characteristic_delay(),
        |horizon| {
            mapping
                .returned_at_horizon(horizon)
                .expect("the current conducts")
                >= mapping.reachable_sites()
        },
    )
    .expect("sixty-four doublings saturate the carrier, so the schedule always covers")
}

struct Row {
    name: String,
    sites: usize,
    reachable: usize,
    guess: u64,
    reported: u64,
    doublings: u32,
    fixed: u64,
    growths: usize,
    growth_bound: usize,
    below: Option<usize>,
}

fn measure(name: &str, mapping: &CapacitanceMapping) -> Row {
    let reading = mapping.read().expect("the current conducts");
    let fixed = &reading.horizon_fixed_point;
    let (reported, doublings) = excised(mapping);
    Row {
        name: name.to_owned(),
        sites: mapping.site_count(),
        reachable: mapping.reachable_sites(),
        guess: (mapping.site_count() as u64) * mapping.longest_characteristic_delay(),
        reported,
        doublings,
        fixed: reading.horizon,
        growths: fixed.growths(),
        growth_bound: fixed.growth_bound,
        below: fixed.returned_one_below,
    }
}

fn header() {
    println!(
        "    {:<26} {:>6} {:>6} {:>8} {:>10} {:>5} {:>8} {:>8} {:>12}",
        "circuit", "sites", "reach", "guess", "excised", "x2", "FIXED", "growths", "returned<"
    );
}

fn print_row(row: &Row) {
    println!(
        "    {:<26} {:>6} {:>6} {:>8} {:>10} {:>5} {:>8} {:>3}/{:<4} {:>12}",
        row.name,
        row.sites,
        row.reachable,
        row.guess,
        row.reported,
        row.doublings,
        row.fixed,
        row.growths,
        row.growth_bound,
        row.below.map_or_else(
            || "n/a".to_owned(),
            |below| format!("{below}/{}", row.reachable)
        ),
    );
}

fn control_mapping(derivations: &[Derivation]) -> CapacitanceMapping {
    let circuit = found_circuit(derivations, CircuitAperture::DEPOSITED_READER)
        .expect("the aperture is admissible");
    // The circuit is consumed by the mapping's founding, which copies what it needs.
    CapacitanceMapping::found(
        &circuit,
        derivations,
        &[],
        CapacityLaw::DistinguishableResults,
        CharacteristicDelayLaw::Uniform,
    )
    .expect("the circuit founds a passage ecology")
}

fn deposit_mapping(
    circuit: &DerivationCircuit,
    derivations: &[Derivation],
    sources: &[String],
    delay_law: CharacteristicDelayLaw,
) -> CapacitanceMapping {
    CapacitanceMapping::found(
        circuit,
        derivations,
        sources,
        CapacityLaw::DistinguishableResults,
        delay_law,
    )
    .expect("the deposited circuit founds a passage ecology")
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output".to_owned());

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a chronology horizon is read off the transport law's own returned testimony");
    println!("excised=HORIZON_DOUBLINGS: u32 = 64  (derivation_capacitance.rs:158 at 085a9ab)");
    println!("standing={root}");

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    // ---------------------------------------------------------------------------------------------
    // What derives the horizon now
    // ---------------------------------------------------------------------------------------------

    println!("\nWHAT DERIVES THE HORIZON NOW");
    println!("----------------------------");
    println!(
        "  Three properties of `receiver_current::radiate_to_horizon`, each a statement about"
    );
    println!("  that owner rather than about this one:");
    println!();
    println!(
        "    every passage delay is positive     `characteristic_delay` is refused at zero and"
    );
    println!("                                        delay = characteristic_delay + rounds - 1");
    println!(
        "    so each site departs at most once   the schedule is popped in ascending chronology"
    );
    println!(
        "                                        and a recorded arrival is replaced only by a"
    );
    println!(
        "                                        strictly earlier one, impossible after the pop"
    );
    println!(
        "    so the horizon is monotone          the horizon is read at exactly two `> horizon`"
    );
    println!("                                        comparisons, so a larger one reproduces the");
    println!("                                        smaller run exactly below it");
    println!();
    println!(
        "  A reachable site fails to return only because its arrival crossed the deferral gate,"
    );
    println!(
        "  and that gate DEPOSITS the arrival with its chronology. So the growth reads its next"
    );
    println!("  horizon off the law; each growth returns at least one further site, because the");
    println!(
        "  smallest unreturned arrival's own predecessor arrived strictly earlier and therefore"
    );
    println!("  already returned; and the circuit's REACHABLE POPULATION bounds the growths.");
    println!();
    println!(
        "  The horizon finally reported is `max` over the reachable population of the arrival"
    );
    println!(
        "  chronology the law returned. Both sides of it being least are CONDUCTED: complete at"
    );
    println!("  the fixed point, strictly incomplete one chronology below.");

    // ---------------------------------------------------------------------------------------------
    // CLAIM 1 — the guess is not a bound
    // ---------------------------------------------------------------------------------------------

    println!(
        "\nCLAIM 1 — `site_count * longest_delay` IS NOT A BOUND, AND MISSES BY AN UNBOUNDED MARGIN"
    );
    println!(
        "-------------------------------------------------------------------------------------------"
    );
    println!(
        "  doubling_ladder(2, rungs): 2 + 2*rungs sites, completion predicted BEFORE the reading"
    );
    println!("  at 2 + 2*(2^rungs - 2) by the construction's own recurrence.");
    header();
    let mut margins: Vec<i128> = Vec::new();
    let mut predictions_hold = true;
    for rungs in 2usize..=7 {
        let derivations = doubling_ladder(2, rungs);
        let mapping = control_mapping(&derivations);
        let row = measure(&format!("doubling_ladder(2, {rungs})"), &mapping);
        let predicted = doubling_ladder_completion(2, rungs as u32);
        if row.fixed != predicted {
            predictions_hold = false;
            println!(
                "      DISAGREES: predicted {predicted}, returned {}",
                row.fixed
            );
        }
        margins.push(i128::from(row.fixed) - i128::from(row.guess));
        print_row(&row);
    }
    println!("\n  the margin the guess misses by, per rung: {margins:?}");
    let margin_grows = margins.windows(2).all(|pair| pair[1] > pair[0]);
    println!("  strictly growing: {margin_grows}   (the site count grows by 2 per rung; the");
    println!("  completion chronology doubles)");
    holds.push((
        "the ladder's completion chronology matches the construction's own prediction",
        predictions_hold,
        format!("rungs 2..=7 against 2 + 2*(2^rungs - 2)"),
    ));
    holds.push((
        "the excised starting guess undershoots by a margin that grows with the rung count",
        margin_grows,
        format!("margins {margins:?}"),
    ));

    // ---------------------------------------------------------------------------------------------
    // CLAIM 2 — the doubling quantized the return
    // ---------------------------------------------------------------------------------------------

    println!("\nCLAIM 2 — THE DISTINGUISHING WORD: ONE REPORT, TWO MATERIALS");
    println!("------------------------------------------------------------");
    println!(
        "  One site count and one longest delay, so the excised schedule's starting guess and"
    );
    println!("  every doubling of it are IDENTICAL. What the two circuits do is not.");
    header();
    let left = doubling_ladder(2, 5);
    let right = doubling_ladder(4, 4);
    let left_mapping = control_mapping(&left);
    let right_mapping = control_mapping(&right);
    let left_row = measure("doubling_ladder(2, 5)", &left_mapping);
    let right_row = measure("doubling_ladder(4, 4)", &right_mapping);
    print_row(&left_row);
    print_row(&right_row);
    let indistinguishable = left_row.sites == right_row.sites
        && left_row.guess == right_row.guess
        && left_row.reported == right_row.reported;
    let separated = left_row.fixed != right_row.fixed;
    println!(
        "\n  the excised schedule reports {} for both. The fixed point reports {} and {}.",
        left_row.reported, left_row.fixed, right_row.fixed
    );
    println!("  The schedule was reporting its own band. A horizon is a receiver coordinate, and");
    println!("  that field was carrying the SCHEDULE'S receiver rather than the material's.");
    holds.push((
        "two circuits the excised schedule reported alike are separated by the fixed point",
        indistinguishable && separated,
        format!(
            "excised {} == {}, fixed {} != {}",
            left_row.reported, right_row.reported, left_row.fixed, right_row.fixed
        ),
    ));

    // ---------------------------------------------------------------------------------------------
    // CLAIM 3 — the refusal could not fire
    // ---------------------------------------------------------------------------------------------

    println!(
        "\nCLAIM 3 — THE SIXTY-FOUR-DOUBLING REFUSAL WAS GUARDING A STATE NO MATERIAL REACHES"
    );
    println!("-----------------------------------------------------------------------------------");
    let mut saturates = true;
    for guess in [1u64, 3, 22, 121, u64::MAX / 3] {
        let mut horizon = guess;
        let mut at = 0u32;
        while horizon < u64::MAX && at < 64 {
            horizon = horizon.saturating_mul(2);
            at += 1;
        }
        println!("    guess {guess:<24} saturates to u64::MAX after {at} doublings");
        if horizon != u64::MAX {
            saturates = false;
        }
    }
    println!("  and at u64::MAX the `arrival_chronology > horizon` gate never fires, so every");
    println!("  reachable site returns or the radiation refuses on its own carrier extent. The");
    println!("  doublings actually taken above are in the `x2` column and none exceeds a handful.");
    holds.push((
        "sixty-four doublings saturate the carrier from any positive guess",
        saturates,
        "saturating_mul(2) reaches u64::MAX within 64 steps".to_owned(),
    ));

    // ---------------------------------------------------------------------------------------------
    // The declared control circuits
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE DECLARED CONTROL CIRCUITS");
    println!("-----------------------------");
    header();
    let mut control_rows = Vec::new();
    for (name, derivations) in [
        ("one_result_star(9)".to_owned(), one_result_star(9)),
        ("many_result_star(9)".to_owned(), many_result_star(9)),
        ("disjoint_terrain(9)".to_owned(), disjoint_terrain(9)),
        ("doubling_ladder(3, 4)".to_owned(), doubling_ladder(3, 4)),
    ] {
        let mapping = control_mapping(&derivations);
        let row = measure(&name, &mapping);
        print_row(&row);
        control_rows.push(row);
    }

    // ---------------------------------------------------------------------------------------------
    // The deposit
    // ---------------------------------------------------------------------------------------------

    println!("\nTHE DEPOSITED DERIVATIONS");
    println!("-------------------------");
    let paths = artifact_paths(Path::new(&root));
    let mut deposit_rows = Vec::new();
    if paths.is_empty() {
        println!("  no deposited derivations at {root} — the control circuits above still stand");
    } else {
        let sources: Vec<String> = paths
            .iter()
            .filter_map(|path| std::fs::read_to_string(path).ok())
            .collect();
        let mut derivations = Vec::new();
        let mut carried = Vec::new();
        for text in &sources {
            if let Some(derivation) = read_derivation(text) {
                derivations.push(derivation);
                carried.push(text.clone());
            }
        }
        println!(
            "  read {} artifacts, {} carrying a theorem declaration",
            paths.len(),
            derivations.len()
        );
        let deposited = found_circuit(&derivations, CircuitAperture::DEPOSITED_READER)
            .expect("the deposited reader's aperture is admissible");
        let per_route = found_circuit(&derivations, CircuitAperture::PER_ROUTE)
            .expect("the per-route aperture is admissible");

        header();
        for (name, mapping) in [
            (
                "by declaration, uniform",
                deposit_mapping(
                    &deposited,
                    &derivations,
                    &[],
                    CharacteristicDelayLaw::Uniform,
                ),
            ),
            (
                "by route, uniform",
                deposit_mapping(
                    &per_route,
                    &derivations,
                    &[],
                    CharacteristicDelayLaw::Uniform,
                ),
            ),
            (
                "by declaration, situated",
                deposit_mapping(
                    &deposited,
                    &derivations,
                    &carried,
                    CharacteristicDelayLaw::SourceContinuity,
                ),
            ),
        ] {
            let row = measure(name, &mapping);
            print_row(&row);
            deposit_rows.push(row);
        }
    }

    // ---------------------------------------------------------------------------------------------
    // CONTROL — the certificate is two-sided everywhere it was taken
    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROL — THE CERTIFICATE IS TWO-SIDED AT EVERY ROW ABOVE");
    println!("---------------------------------------------------------");
    println!("  Complete at the fixed point, and STRICTLY INCOMPLETE one chronology below it. The");
    println!("  `returned<` column is the second half; a reading whose horizon overstated the");
    println!("  material would return the whole population there and `read` would refuse.");
    let every_row: Vec<&Row> = control_rows
        .iter()
        .chain(deposit_rows.iter())
        .chain([&left_row, &right_row])
        .collect();
    let two_sided = every_row
        .iter()
        .all(|row| row.below.is_none_or(|below| below < row.reachable));
    let bounded = every_row.iter().all(|row| row.growths <= row.growth_bound);
    let never_over = every_row.iter().all(|row| row.fixed <= row.reported);
    println!("    two-sided at every row      {two_sided}");
    println!("    growths within the material's own bound   {bounded}");
    println!("    the fixed point never exceeds what the excised schedule reported   {never_over}");
    holds.push((
        "one chronology below the fixed point the circuit is strictly incomplete",
        two_sided,
        format!("{} rows", every_row.len()),
    ));
    holds.push((
        "the growths stay inside the bound the reachable population supplies",
        bounded,
        format!("{} rows", every_row.len()),
    ));
    holds.push((
        "the fixed point is never larger than the horizon the excised schedule reported",
        never_over,
        format!("{} rows", every_row.len()),
    ));

    // ---------------------------------------------------------------------------------------------

    println!("\nCONTROLS");
    println!("--------");
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        println!(
            "  [{}] {claim}\n        {evidence}",
            if *verdict { "holds" } else { "FAILED" }
        );
        if !verdict {
            failed += 1;
        }
    }
    if failed > 0 {
        println!("\n{failed} declared control(s) failed");
        std::process::exit(1);
    }
    println!("\nevery declared control holds");
}
