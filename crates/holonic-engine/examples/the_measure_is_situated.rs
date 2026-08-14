//! The measure is given a declared second body, so the read is situated rather than absolute.
//!
//! ```text
//! cargo run --release --example the_measure_is_situated
//! ```
//!
//! ## What this driver is for
//!
//! `crates/holonic-engine/src/surprisal.rs` holds an exact symbolic measure and, until this run,
//! reached nothing. Its every entry point takes **one** population, and
//! `canon/THE_HOLOBROCHOS_SPINE.md` §2 retains as mathematically exact that *"comparison is situated
//! by a frame and is therefore at least a frame/object/object relation"*. A measure computed from one
//! body alone is a one-body read; calling it a comparison is the dropped third.
//!
//! `situated_residual::situate` supplies the missing slot. This driver runs it on one declared
//! material against the declared null the project already owns —
//! `conditioned_derivation::FoundedMorphology::unconditioned()`, whose own law is that a body exposed
//! to nothing licenses no bridge and derives the empty population — and reports four controls.
//!
//! Everything below is self-contained: the deposit, the three corpora and the query are declared in
//! this file, so no run depends on a path outside the crate.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use holonic_engine::algebraic::CausalCellId;
use holonic_engine::conditioned_derivation::{
    ConditionedBody, DerivationQuery, Exposure, PassageId, expose,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::exact_value::ExactOrdering;
use holonic_engine::gluing::{Cover, read_cover};
use holonic_engine::rebase_invariants::PivotRule;
use holonic_engine::situated_residual::{
    Emission, Frame, ResidualArm, SituatedReading, Situation, emission_reaching, one_body_read,
    situate,
};
use holonic_engine::surprisal::{Grain, Support};

// -------------------------------------------------------------------------------------------------
// The declared material
// -------------------------------------------------------------------------------------------------

/// The material name every emission and every frame in this run must agree on.
const MATERIAL: &str = "the four-artifact Lean deposit, under the query below";

/// What an event is. Declared once, carried in every frame, printed in every receipt.
const RECEIVER: &str =
    "one identifier recruited by a route reaching the queried statement, at its exact multiplicity";

/// The statement both bodies are asked for a further route to.
const STATEMENT: &str = "(P : Prop) : exactCarrier P";

/// The declared grain ladder. Coarse to fine, receiver coordinates and not tuning steps: a coarser
/// grain returns a wider certified set and therefore decides fewer comparisons.
const GRAIN_LADDER: [Grain; 6] = [
    Grain::at(1, 4),
    Grain::at(2, 8),
    Grain::at(4, 16),
    Grain::at(8, 32),
    Grain::at(16, 64),
    Grain::DECLARED,
];

/// Four deposited artifacts. Three reach the queried statement; the fourth reaches another and is
/// what makes a brought identifier genuinely absent from the reference's emission.
fn deposit() -> Vec<(String, String)> {
    vec![
        (
            "carry".to_owned(),
            "namespace Soma\ntheorem carrier_transport (P : Prop) : exactCarrier P := by\n  \
             have step := exact_chart_carry\nend Soma\n"
                .to_owned(),
        ),
        (
            "carry-again".to_owned(),
            "namespace Soma\ntheorem carrier_transport (P : Prop) : exactCarrier P := by\n  \
             have step := exact_chart_carry\n  have again := exact_chart_carry\nend Soma\n"
                .to_owned(),
        ),
        (
            "relay".to_owned(),
            "namespace Soma\ntheorem relay_agrees (P : Prop) : exactCarrier P := by\n  \
             have step := formal_carry\nend Soma\n"
                .to_owned(),
        ),
        (
            "chart".to_owned(),
            "namespace Soma\ntheorem chart_agrees (Q : Prop) : chartCarrier Q := by\n  \
             have step := exact_chart_lift\nend Soma\n"
                .to_owned(),
        ),
    ]
}

/// The corpus that founds the morphology the production runs on. `exact`, `carry` and `carrier` all
/// recur across two distinct wholes and commit.
fn founding_corpus() -> Vec<Exposure> {
    vec![
        expose(
            "one",
            "an exact transport must carry the boundary. the carrier is named once here.",
        ),
        expose(
            "two",
            "exact transport, and what it must carry across. the carrier again.",
        ),
    ]
}

/// **The echo corpus.** A genuine corpus, genuinely conditioning: three words, each witnessed by two
/// distinct wholes, each committing exactly as `carrier` does. None of them occurs inside any
/// identifier this deposit recruits — which the run measures rather than assumes — so the founded
/// morphology covers nothing, licenses no bridge, and the body's emission reproduces its input.
fn echo_corpus() -> Vec<Exposure> {
    vec![
        expose("north", "lightning kindles wind"),
        expose("south", "lightning kindles wind"),
    ]
}

// -------------------------------------------------------------------------------------------------
// Receipt plumbing
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

struct Controls {
    failed: Vec<String>,
}

impl Controls {
    fn new() -> Self {
        Self { failed: Vec::new() }
    }

    fn check(&mut self, name: &str, holds: bool, saying: &str) {
        println!(
            "\n  [{}] {name}\n        {saying}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

fn print_emission(emission: &Emission) {
    println!(
        "  {} — {} events, {} occurrences",
        emission.body,
        emission.counts().len(),
        emission.total()
    );
    for (event, count) in emission.counts() {
        println!("      {count:>3}  {event}");
    }
}

fn print_one_body_read(emission: &Emission) {
    match one_body_read(emission).expect("the emission supports itself") {
        Support::Supported(form) => println!("  H({:<22}) = {}", emission.body, form.named()),
        Support::Unsupported => println!("  H({:<22}) = unsupported", emission.body),
    }
}

fn print_reading(reading: &SituatedReading) {
    println!("  {} against {}", reading.body, reading.reference);
    println!("  {}", reading.frame);
    for arm in ResidualArm::ALL {
        let members = reading.arm(arm);
        println!(
            "\n  -- {} arm: {} member(s) --",
            arm.named().to_uppercase(),
            members.len()
        );
        for member in members {
            println!(
                "     {}   emitted x{}   referenced x{}",
                member.event, member.emitted_occurrences, member.referenced_occurrences
            );
            match &member.situation {
                Situation::Founded {
                    emitted,
                    after_found,
                } => {
                    println!("         S_body            = {}", emitted.named());
                    println!("         S_reference       = UNSUPPORTED — the typed refusal");
                    println!("         after the FOUND   = {}", after_found.named());
                }
                Situation::Shared {
                    emitted,
                    carried,
                    separation,
                } => {
                    println!("         S_body            = {}", emitted.named());
                    println!("         S_reference       = {}", carried.named());
                    println!("         separation        = {}", separation.named());
                    println!(
                        "         against zero      = {:?}   at {}",
                        member
                            .against_zero(reading.frame.grain)
                            .expect("the enclosure is available at the declared grain"),
                        reading.frame.grain
                    );
                }
                Situation::Withheld { carried } => {
                    println!("         S_body            = not emitted");
                    println!("         S_reference       = {}", carried.named());
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------------------------
// Reach, measured
// -------------------------------------------------------------------------------------------------

/// One line of library code that names something `surprisal` owns.
struct ReachSite {
    file: String,
    line: usize,
    text: String,
    /// A documentation line. Counted, reported, and **never** admitted as reach: a doc comment
    /// naming a module is prose, and letting prose raise a reach figure is the same defect as a
    /// receipt overstating its code.
    is_documentation: bool,
    /// The line names the module path itself, not only one of its items.
    names_the_module: bool,
}

/// Every site under this crate's `src/` at which library code names something `surprisal` owns.
///
/// `CLAUDE.md` §8: reach is part of the grade, a mechanism that cannot state its reach has not been
/// graded, and *widening an include to raise it is the same defect as a receipt overstating its
/// code*. Two rules follow and both are enforced here:
///
/// - **Documentation lines are separated out and never admitted as reach.** Prose naming a module is
///   prose.
/// - **A name is counted only inside a file that actually imports the module.** `surprisal` is
///   declared and never glob-exported, so a file that does not name `crate::surprisal` cannot be
///   reaching it. The first form of this function skipped that resolution and matched `Grain` inside
///   `ReceiverGrainId` and `Support::` inside `VerticalFiberSupport::`, returning 171 sites across
///   eleven files — the instrument committing, on its first run, exactly the defect its own
///   documentation names.
///
/// The root is `CARGO_MANIFEST_DIR`, a build-time constant, so the measurement does not depend on the
/// working directory a run was launched from.
fn library_reach_of_surprisal() -> Vec<ReachSite> {
    /// Everything `crates/holonic-engine/src/surprisal.rs` declares publicly.
    const OWNED: [&str; 8] = [
        "surprisal",
        "SymbolicSurprisal",
        "SurprisalError",
        "read_population",
        "cross_entropy",
        "entropy(",
        "Support::",
        "Grain",
    ];

    fn walk(root: &Path, into: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(root) else {
            return;
        };
        let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
        here.sort();
        for path in here {
            if path.is_dir() {
                walk(&path, into);
            } else if path.extension().is_some_and(|carried| carried == "rs") {
                into.push(path);
            }
        }
    }

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    walk(&root, &mut files);

    let mut sites = Vec::new();
    for path in files {
        if path.file_name().is_some_and(|name| name == "surprisal.rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        // The resolution step. A file that never names the module path cannot resolve one of its
        // items, because the module is declared and never glob-exported.
        let imports = text
            .lines()
            .any(|line| !line.trim_start().starts_with("//") && line.contains("crate::surprisal"));
        if !imports {
            continue;
        }
        for (ordinal, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            if !OWNED.iter().any(|item| trimmed.contains(item)) {
                continue;
            }
            sites.push(ReachSite {
                file: path
                    .strip_prefix(&root)
                    .unwrap_or(&path)
                    .display()
                    .to_string(),
                line: ordinal + 1,
                text: trimmed.to_owned(),
                is_documentation: trimmed.starts_with("//"),
                names_the_module: trimmed.contains("crate::surprisal"),
            });
        }
    }
    sites
}

// -------------------------------------------------------------------------------------------------
// The run
// -------------------------------------------------------------------------------------------------

fn main() {
    let mut controls = Controls::new();
    let query = DerivationQuery::reaching(STATEMENT);
    let frame = Frame::new(RECEIVER, MATERIAL, Grain::DECLARED);

    rule("THE DECLARED MATERIAL");
    println!("  material : {MATERIAL}");
    println!("  event    : {RECEIVER}");
    println!("  query    : a further route reaching {STATEMENT:?}");
    println!("  grain    : {}", frame.grain);
    println!("\n  deposited artifacts:");
    for (source, text) in deposit() {
        println!("      {source:<12} {}", text.replace('\n', " ").trim());
    }

    // ---------------------------------------------------------------------------------------------
    // Three bodies on one deposit
    // ---------------------------------------------------------------------------------------------

    let reference = ConditionedBody::mount(deposit()).expect("the deposit declares theorems");
    let mut conditioned = ConditionedBody::mount(deposit()).expect("the deposit declares theorems");
    conditioned.condition(&founding_corpus());
    let mut echo = ConditionedBody::mount(deposit()).expect("the deposit declares theorems");
    echo.condition(&echo_corpus());

    rule("THREE BODIES, ONE DEPOSIT");
    for (name, body) in [
        ("the reference (declared null)", &reference),
        ("the conditioned body", &conditioned),
        ("the echo body", &echo),
    ] {
        let derived = body.derive(&query).expect("ascii identifiers");
        println!("\n  {name}");
        println!(
            "      committed stems : {:?}",
            body.morphology().committed_stems()
        );
        println!("      derived passages: {}", derived.len());
        for passage in &derived {
            println!(
                "          {}  [stem {:?} brings {}]",
                passage.name, passage.stem, passage.brought
            );
        }
    }

    // The echo's morphology is non-empty and covers nothing on this deposit. Measured, not assumed.
    let population = conditioned.recruited_population();
    let echo_covers_nothing = population.iter().all(|identifier| {
        echo.morphology()
            .cover(identifier)
            .expect("ascii")
            .occurrences
            .is_empty()
    });
    println!("\n  the echo morphology, applied to every recruited identifier:");
    for identifier in &population {
        println!(
            "      {:<20} {}",
            identifier,
            echo.morphology().cover(identifier).expect("ascii").render()
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The emissions
    // ---------------------------------------------------------------------------------------------

    let emission_of = |name: &str, body: &ConditionedBody| -> Emission {
        emission_reaching(
            name,
            MATERIAL,
            &body.passages(&query).expect("the passages read back"),
            STATEMENT,
        )
    };
    let reference_emission = emission_of("the reference", &reference);
    let conditioned_emission = emission_of("the conditioned body", &conditioned);
    let echo_emission = emission_of("the echo body", &echo);

    rule("THE EMISSIONS, ON ONE MATERIAL");
    print_emission(&reference_emission);
    println!();
    print_emission(&conditioned_emission);
    println!();
    print_emission(&echo_emission);

    rule("THE ONE-BODY READ — a measurement, and NOT a comparison");
    println!(
        "  H(P) = sum_a P(a)*S_P(a): the emission received through its own code, with no second\n  \
         body anywhere in it. It says nothing about this body relative to any other.\n"
    );
    print_one_body_read(&reference_emission);
    print_one_body_read(&conditioned_emission);
    print_one_body_read(&echo_emission);

    // ---------------------------------------------------------------------------------------------
    // The situated reads
    // ---------------------------------------------------------------------------------------------

    let null_against_null =
        situate(&reference_emission, &reference_emission, &frame).expect("one material");
    let conditioned_against_null =
        situate(&conditioned_emission, &reference_emission, &frame).expect("one material");
    let echo_against_null =
        situate(&echo_emission, &reference_emission, &frame).expect("one material");
    let null_against_conditioned =
        situate(&reference_emission, &conditioned_emission, &frame).expect("one material");

    rule("THE SITUATED READ — the conditioned body against the declared null");
    print_reading(&conditioned_against_null);

    rule("THE SAME RESIDUAL, ORIENTED THE OTHER WAY");
    println!(
        "  Reading the null against the conditioned body moves every FOUNDED member to WITHHELD.\n  \
         The residual is oriented; it is not a distance.\n"
    );
    println!(
        "  founded  forward : {:?}",
        conditioned_against_null
            .founded()
            .iter()
            .map(|member| member.event.as_str())
            .collect::<Vec<_>>()
    );
    println!(
        "  withheld reversed: {:?}",
        null_against_conditioned
            .withheld()
            .iter()
            .map(|member| member.event.as_str())
            .collect::<Vec<_>>()
    );

    // ---------------------------------------------------------------------------------------------
    // The four-state ordering across the declared grain ladder
    // ---------------------------------------------------------------------------------------------

    rule("THE ORDERING, ACROSS THE DECLARED GRAIN LADDER");
    println!(
        "  Every within-arm pair, at every declared grain. The complete relation, never a sort:\n  \
         `Open` is not transitive, so no linear extension exists and any ranking would have to\n  \
         break an `Open` by picking a side.\n"
    );
    let mut open_seen: Vec<(Grain, String, String)> = Vec::new();
    for grain in GRAIN_LADDER {
        let relation = conditioned_against_null
            .orderings_at(grain)
            .expect("the enclosure is available");
        let opens = relation.iter().filter(|entry| entry.is_open()).count();
        println!("  {grain:<28} {} pair(s), {opens} Open", relation.len());
        for entry in &relation {
            println!(
                "        [{}] {:<20} vs {:<20} -> {:?}",
                entry.arm.named(),
                entry.left,
                entry.right,
                entry.verdict
            );
            if entry.is_open() {
                open_seen.push((grain, entry.left.clone(), entry.right.clone()));
            }
        }
    }

    if let Some((grain, left, right)) = open_seen.first().cloned() {
        rule("ONE OPEN PAIR, EXHIBITED WHOLE");
        let entry = conditioned_against_null
            .open_orderings_at(grain)
            .expect("the enclosure is available")
            .into_iter()
            .find(|entry| entry.left == left && entry.right == right)
            .expect("the pair was just observed");
        println!("  {}", entry.render());
        println!(
            "\n  both members are still on the reading: {} and {}",
            conditioned_against_null
                .event_names()
                .contains(left.as_str()),
            conditioned_against_null
                .event_names()
                .contains(right.as_str())
        );
        let decided = entry
            .left_form
            .compare_grain(&entry.right_form, Grain::DECLARED)
            .expect("the declared grain");
        println!(
            "  the same pair at {} -> {decided:?}\n  An `Open` is a statement about the receiver's \
             grain, never about the forms.",
            Grain::DECLARED
        );
    }

    // ---------------------------------------------------------------------------------------------
    // Control 1 — zero against the null
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 1 — ZERO AGAINST THE NULL");
    println!(
        "  The material on which nothing can be founded is the deposit read by a body exposed to\n  \
         nothing: `FoundedMorphology::unconditioned()` commits no stem, no two identifiers share\n  \
         one, and the module's own law derives the empty population. Its emission is therefore its\n  \
         input, and situating it against itself must return zero."
    );
    let one_body_null = match one_body_read(&reference_emission).expect("supported") {
        Support::Supported(form) => form,
        Support::Unsupported => panic!("a non-empty emission supports itself"),
    };
    println!(
        "\n  situated read (null against null) : returns_zero = {}",
        null_against_null.returns_zero()
    );
    println!(
        "      members {}, founded {}, withheld {}, separating {}",
        null_against_null.members.len(),
        null_against_null.founded().len(),
        null_against_null.withheld().len(),
        null_against_null.separating().len()
    );
    println!(
        "  one-body read of the SAME emission : {}",
        one_body_null.named()
    );
    println!("      is_zero = {}", one_body_null.is_zero());

    controls.check(
        "zero against the null, and the one-body read disagrees",
        null_against_null.returns_zero() && !one_body_null.is_zero(),
        "the situated read returns zero on material this body founded nothing on, while the \
         one-body read of the same emission returns a non-vanishing form. They disagree, so the \
         third body was not dropped.",
    );

    println!(
        "\n  And the non-vacuity half — a read that returned zero on everything would be a check\n  \
         that cannot fail. The same organ, same frame, same material, conditioned body:"
    );
    println!(
        "      returns_zero = {}, separating members = {}",
        conditioned_against_null.returns_zero(),
        conditioned_against_null.separating().len()
    );
    controls.check(
        "the situated read is not identically zero",
        !conditioned_against_null.returns_zero()
            && !conditioned_against_null.separating().is_empty(),
        "the gauge acts: the conditioned body separates from the null on the same material, so \
         control 1's zero is a return and not a constant.",
    );

    // ---------------------------------------------------------------------------------------------
    // Control 2 — Open is reachable and occurs
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 2 — `Open` IS REACHABLE, OCCURS, AND RETAINS BOTH MEMBERS");
    let retained = open_seen.iter().all(|(_, left, right)| {
        conditioned_against_null
            .event_names()
            .contains(left.as_str())
            && conditioned_against_null
                .event_names()
                .contains(right.as_str())
    });
    let refinable = open_seen.iter().all(|(_, left, right)| {
        let find = |event: &str| {
            conditioned_against_null
                .members
                .iter()
                .find(|member| member.event == event)
                .expect("the member is on the reading")
                .situating_form()
                .clone()
        };
        find(left)
            .compare_grain(&find(right), Grain::DECLARED)
            .expect("the declared grain")
            != ExactOrdering::Open
    });
    println!(
        "  Open occurrences across the ladder: {}\n  every Open pair retained on the reading: {}\n  \
         every Open pair decided at {}: {}",
        open_seen.len(),
        retained,
        Grain::DECLARED,
        refinable
    );
    for (grain, left, right) in &open_seen {
        println!("      {grain}  {left} vs {right}");
    }
    controls.check(
        "the four-state ordering returns Open on this material, with both members retained",
        !open_seen.is_empty() && retained && refinable,
        "a four-state carrier that never returns Open on real material has not been exercised, and \
         an Open that lost a member would be a tie-break wearing another name.",
    );

    // ---------------------------------------------------------------------------------------------
    // Control 3 — the trivial echo
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 3 — THE TRIVIAL ECHO, SEPARATED AS POPULATIONS AND NOT BY A SCORE");
    println!(
        "  The echo body is conditioned: {:?} all commit. None of them covers any recruited\n  \
         identifier, measured above: {echo_covers_nothing}. So it licenses no bridge and its\n  \
         emission reproduces its input.\n",
        echo.morphology().committed_stems()
    );
    println!(
        "  emissions equal as populations : {}",
        echo_emission.counts() == reference_emission.counts()
    );
    println!("\n  echo against the null:");
    println!(
        "      founded {}, withheld {}, separating {}, returns_zero {}",
        echo_against_null.founded().len(),
        echo_against_null.withheld().len(),
        echo_against_null.separating().len(),
        echo_against_null.returns_zero()
    );
    println!("      every shared separation vanishes by the coefficient test, no enclosure taken:");
    for member in echo_against_null.shared() {
        if let Situation::Shared { separation, .. } = &member.situation {
            println!(
                "          {:<20} separation = {:<3}  at the coarsest grain {:?}",
                member.event,
                separation.named(),
                member.against_zero(Grain::at(1, 4)).expect("exact branch")
            );
        }
    }
    println!("\n  conditioned body against the null:");
    println!(
        "      founded {}, withheld {}, separating {}, returns_zero {}",
        conditioned_against_null.founded().len(),
        conditioned_against_null.withheld().len(),
        conditioned_against_null.separating().len(),
        conditioned_against_null.returns_zero()
    );
    println!("      every shared separation moved, because the FOUND moved the denominator:");
    for member in conditioned_against_null.shared() {
        if let Situation::Shared { separation, .. } = &member.situation {
            println!(
                "          {:<20} separation = {}",
                member.event,
                separation.named()
            );
        }
    }
    let echo_shared_all_zero = echo_against_null.shared().iter().all(|member| {
        matches!(&member.situation, Situation::Shared { separation, .. } if separation.is_zero())
    });
    let founding_shared_all_move = conditioned_against_null
        .shared()
        .iter()
        .all(|member| {
            matches!(&member.situation, Situation::Shared { separation, .. } if !separation.is_zero())
        });
    controls.check(
        "an echo and a founding emission differ as populations, with nothing scored",
        echo_covers_nothing
            && echo_against_null.returns_zero()
            && echo_against_null.founded().is_empty()
            && echo_shared_all_zero
            && !conditioned_against_null.founded().is_empty()
            && founding_shared_all_move,
        "the two are separated by the SHAPE of the residual — an empty founded arm and exactly \
         vanishing separations against a non-empty founded arm and separations that all moved — and \
         by no number anywhere.",
    );

    println!(
        "\n  And the finding this control returns that was not asked for. The echo body and the\n  \
         null body have IDENTICAL emissions and therefore identical one-body reads, while their\n  \
         constructions differ by a whole founded morphology:"
    );
    println!(
        "      null committed stems : {:?}",
        reference.morphology().committed_stems()
    );
    println!(
        "      echo committed stems : {:?}",
        echo.morphology().committed_stems()
    );
    println!(
        "      one-body reads equal : {}",
        one_body_read(&echo_emission).ok() == one_body_read(&reference_emission).ok()
    );
    println!(
        "  That is receiver non-reconstruction, verbatim: equality of outputs, spectra, labels or\n  \
         magnitudes does not imply equality of complete constructions. The distinction is real and\n  \
         it lives in the construction, not in the emission — which is why the emission's measure\n  \
         must not be read as a verdict on the body."
    );

    // ---------------------------------------------------------------------------------------------
    // Control 4 — reach
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 4 — REACH, FROM A LIBRARY PATH");
    let sites = library_reach_of_surprisal();
    let code: Vec<&ReachSite> = sites.iter().filter(|site| !site.is_documentation).collect();
    let documentation = sites.len() - code.len();
    let code_files: BTreeSet<&str> = code.iter().map(|site| site.file.as_str()).collect();
    println!(
        "  Before this run `surprisal` was reached by nothing: its only mention anywhere in the\n  \
         workspace was `pub mod surprisal;` in lib.rs. Measured now over src/, excluding\n  \
         surprisal.rs itself:\n"
    );
    println!(
        "      code sites          : {}   across {} library file(s): {code_files:?}",
        code.len(),
        code_files.len()
    );
    println!("      documentation lines : {documentation}   counted, and NOT admitted as reach");
    println!("\n  the sites that name the module path itself:");
    for site in code.iter().filter(|site| site.names_the_module) {
        println!("      {}:{}  {}", site.file, site.line, site.text);
    }
    println!("\n  the first ten code sites naming an item it owns:");
    for site in code.iter().take(10) {
        println!("      {}:{}  {}", site.file, site.line, site.text);
    }
    controls.check(
        "surprisal reaches a library path",
        !code.is_empty() && !code_files.is_empty(),
        "the carrier is consumed by library code and not only by this driver, so the reach is a \
         property of the body rather than of the run.",
    );

    // ---------------------------------------------------------------------------------------------
    // The gluing question, measured
    // ---------------------------------------------------------------------------------------------

    rule("THE GLUING QUESTION — WHY THIS IS NOT EXPRESSED THROUGH `gluing.rs`, MEASURED");
    println!(
        "  Mayer-Vietoris takes ONE complex and two subcomplexes of it. Two bodies given the same\n  \
         material emit two populations, and the only complex holding both is the larger body's own,\n  \
         in which the reference's emission is NESTED. Exactness then forces the connecting map to\n  \
         vanish at every grade. That is a theorem, not an implementation gap, and here it is:\n"
    );
    let aperture = CircuitAperture::STATEMENT_INCIDENT;
    let circuit = conditioned
        .circuit(&query, aperture)
        .expect("the production founds a circuit");
    let derived_ids: BTreeSet<PassageId> = circuit
        .passages
        .iter()
        .filter(|passage| passage.is_derived())
        .map(|passage| passage.id)
        .collect();
    let claimed_by = |ids: &BTreeSet<PassageId>| -> BTreeSet<CausalCellId> {
        circuit
            .provenance
            .iter()
            .filter(|(_, claimants)| claimants.intersection(ids).next().is_some())
            .map(|(cell, _)| *cell)
            .collect()
    };
    let standing_ids: BTreeSet<PassageId> = circuit
        .passages
        .iter()
        .filter(|passage| !passage.is_derived())
        .map(|passage| passage.id)
        .collect();
    let standing_cells = claimed_by(&standing_ids);
    let derived_cells = claimed_by(&derived_ids);
    let all_cells: BTreeSet<CausalCellId> = standing_cells.union(&derived_cells).copied().collect();

    println!(
        "  circuit under {aperture:?}\n      cells {}, standing-claimed {}, derived-claimed {}, \
         provenance total {}",
        circuit.circuit.complex().cells().len(),
        standing_cells.len(),
        derived_cells.len(),
        circuit.provenance_is_total()
    );

    let nested = Cover {
        left: all_cells.clone(),
        right: standing_cells.clone(),
    };
    match read_cover(circuit.circuit.complex(), &nested, PivotRule::FirstNonzero) {
        Ok(reading) => println!(
            "\n  the TWO-BODY cover (body's emission, reference's emission), nested:\n      \
             obstruction {:?}   torsion obstruction {:?}   euler defect {}   exhibits {}",
            reading.obstruction,
            reading.torsion_obstruction,
            reading.euler_defect,
            reading.exhibits_obstruction()
        ),
        Err(refusal) => println!("\n  the two-body cover was refused: {refusal}"),
    }

    let seam = Cover {
        left: standing_cells,
        right: derived_cells,
    };
    match read_cover(circuit.circuit.complex(), &seam, PivotRule::FirstNonzero) {
        Ok(reading) => println!(
            "\n  and the cover Mayer-Vietoris IS good for here — standing against derived, which is\n  \
             a different question and not this one:\n      obstruction {:?}   torsion obstruction \
             {:?}   euler defect {}   exhibits {}",
            reading.obstruction,
            reading.torsion_obstruction,
            reading.euler_defect,
            reading.exhibits_obstruction()
        ),
        Err(refusal) => println!("\n  the standing-against-derived cover was refused: {refusal}"),
    }
    println!(
        "\n  The connecting map returns integer ranks per grade and exhibits no member. The situated\n  \
         residual returns a per-member Q-linear form over the prime axes. Neither refines the other,\n  \
         and what they share is the sentence: an invariant lives in a disagreement — of two\n  \
         RECEIVERS over one source there, of two BODIES over one material here."
    );

    // ---------------------------------------------------------------------------------------------

    rule("CONTROLS");
    if controls.failed.is_empty() {
        println!("  every declared control holds.");
    } else {
        println!("  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
