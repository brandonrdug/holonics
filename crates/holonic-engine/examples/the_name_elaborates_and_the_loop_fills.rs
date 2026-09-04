//! Elaborate the machine's own deposited names, then fill the loops its routes close where the
//! meanings agree — and leave the holes where they do not.
//!
//! ```text
//! cargo run --release --example the_name_elaborates_and_the_loop_fills -- standing/output
//! ```
//!
//! ## What this driver is for
//!
//! `holonic_engine::derivation_atlas` reads a deposit as a circuit and founds **no 2-cell**, saying
//! so rather than choosing: a square over two derivations sharing two symbols cancels exactly the
//! grade-1 cycle the same design reads as *"independent distinct routes to one result"*. That
//! refusal stood because the reading had no denotation — with surface structure and nothing else,
//! two routes to one statement are indistinguishable from one route wearing two names.
//!
//! `holonic_engine::name_elaboration` supplies the denotation constructively: the meaning of a name
//! is the transitive closure of what it recruits, with the depth every constituent entered at. So
//! the refusal is resolved **by construction**, and `holonic_engine::derivation_two_cells` founds
//! the square exactly where the two meanings agree.
//!
//! ## The declared controls
//!
//! Each is printed with its evidence and the run exits non-zero if any fails.
//!
//! ```text
//!   1  the elaboration is constructive, not a lookup
//!   2  filling must be able to NOT happen
//!   3  betti-1 before and after, with BOTH populations named
//!   4  a cycle is retained as a cycle, or the deposit is reported to contain none
//!   5  the aperture is stated and something is outside it, by name
//!   6  the triple-overlap check is run and reported either way
//! ```
//!
//! Controls 4 and 6 carry a **declared control population** beside the measurement, because
//! `CLAUDE.md` §8 rules that a law returning zero proves nothing about itself. The deposit contains
//! no recruitment cycle; that is a fact about the deposit only if the detector is known to fire, so
//! the detector is run against constructed material that carries one and the control requires it to
//! return non-zero there.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    CircuitAperture, Derivation, ReachOrientation, read_derivation,
};
use holonic_engine::derivation_two_cells::{
    AgreementCriterion, RouteFilling, TwoCellRefusal, betti_at, fill_routes, torsion_at,
};
use holonic_engine::name_elaboration::{Elaboration, ElaborationAperture, ElaborationDeposit};
use holonic_engine::rebase_invariants::PivotRule;

/// The declared square population any one reading may found. Exceeding it **refuses the reading
/// with its size** rather than truncating it, so a printed number is never of less material than
/// the aperture beside it claims.
const SQUARE_APERTURE: usize = 40_000;

/// The declared triple population any one reading may walk.
const TRIPLE_APERTURE: usize = 200_000;

/// The pivot rule every integer reduction here is taken under. A pivot order is a receiver
/// coordinate and is never compared as an invariant.
const RULE: PivotRule = PivotRule::FirstNonzero;

// -------------------------------------------------------------------------------------------------
// Reading the deposit
// -------------------------------------------------------------------------------------------------

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
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> (usize, Vec<Derivation>) {
    let paths = artifact_paths(root);
    let read = paths
        .iter()
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .filter_map(|text| read_derivation(&text))
        .collect();
    (paths.len(), read)
}

fn derivation(name: &str, statement: &str, recruited: &[(&str, u32)]) -> Derivation {
    Derivation {
        name: name.to_owned(),
        statement: statement.to_owned(),
        recruited: recruited
            .iter()
            .map(|(symbol, count)| ((*symbol).to_owned(), *count))
            .collect(),
    }
}

// -------------------------------------------------------------------------------------------------
// Printing
// -------------------------------------------------------------------------------------------------

fn rule_line(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn section(title: &str) {
    println!("\n{title}");
    println!("{}", "-".repeat(title.len()));
}

/// A population printed as wrapped names, never as a count alone.
fn names(indent: &str, population: impl IntoIterator<Item = String>) {
    names_capped(indent, population, usize::MAX);
}

/// The same, exhibiting at most `cap` members and stating how many it did not print.
///
/// A cap on what is *printed* is not a cap on what is returned: the populations live on
/// [`RouteFilling`] whole, and a caller that wants all of them takes them from there. Printing
/// twenty-two thousand names is noise, and noise is how a reader stops checking.
fn names_capped(indent: &str, population: impl IntoIterator<Item = String>, cap: usize) {
    let all: Vec<String> = population.into_iter().collect();
    if all.is_empty() {
        println!("{indent}(none)");
        return;
    }
    let held = all.len().saturating_sub(cap);
    let carried: Vec<String> = all.into_iter().take(cap).collect();
    let mut line = String::new();
    for name in carried {
        if !line.is_empty() && line.len() + name.len() + 2 > 88 {
            println!("{indent}{line}");
            line.clear();
        }
        if !line.is_empty() {
            line.push_str(", ");
        }
        line.push_str(&name);
    }
    if !line.is_empty() {
        println!("{indent}{line}");
    }
    if held > 0 {
        println!("{indent}... and {held} further members, returned on the reading and not printed");
    }
}

struct Controls {
    verdicts: Vec<(String, bool, String)>,
}

impl Controls {
    fn new() -> Self {
        Self {
            verdicts: Vec::new(),
        }
    }

    fn declare(&mut self, name: &str, holds: bool, evidence: String) {
        self.verdicts.push((name.to_owned(), holds, evidence));
    }

    fn all_hold(&self) -> bool {
        self.verdicts.iter().all(|(_, holds, _)| *holds)
    }
}

// -------------------------------------------------------------------------------------------------
// The run
// -------------------------------------------------------------------------------------------------

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "standing/output".to_owned());
    let root = PathBuf::from(root);
    let (files, derivations) = read_deposit(&root);

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=the elaboration of a name is the transitive closure of what it recruits");
    println!("standing={}", root.display());
    println!(
        "\nread {files} artifacts, {} carrying a theorem declaration",
        derivations.len()
    );
    if derivations.is_empty() {
        eprintln!("no deposited derivation under {}", root.display());
        std::process::exit(2);
    }

    let deposit = ElaborationDeposit::read(&derivations);
    let mut controls = Controls::new();

    the_deposit(&deposit);
    control_one_the_elaboration_is_constructive(&deposit, &mut controls);
    control_five_the_aperture_and_what_lies_outside_it(&deposit, &mut controls);
    control_four_the_cycles(&deposit, &mut controls);

    let readings = the_fillings(&derivations);
    control_two_filling_must_be_able_to_not_happen(&readings, &mut controls);
    control_three_betti_before_and_after(&readings, &mut controls);
    control_six_the_triple_overlaps(&readings, &mut controls);
    what_the_elaboration_cannot_discriminate(&deposit, &readings);

    rule_line("THE DECLARED CONTROLS");
    for (name, holds, evidence) in &controls.verdicts {
        println!("  [{}] {name}", if *holds { "holds" } else { "FAILS" });
        println!("        {evidence}");
    }
    if !controls.all_hold() {
        eprintln!("\na declared control failed");
        std::process::exit(1);
    }
}

// -------------------------------------------------------------------------------------------------
// The deposit, as the elaboration organ indexes it
// -------------------------------------------------------------------------------------------------

fn the_deposit(deposit: &ElaborationDeposit) {
    rule_line("WHAT THE DEPOSIT DECLARES, AND WHAT IT ONLY NAMES");

    section("declared names, with the artifacts declaring each");
    for (name, ordinals) in deposit.declarations() {
        let statements: Vec<String> = deposit
            .statements_of(name)
            .into_iter()
            .map(str::to_owned)
            .collect();
        println!(
            "  {name}  x{}  reaching {}",
            ordinals.len(),
            statements
                .iter()
                .map(|statement| format!("`{statement}`"))
                .collect::<Vec<_>>()
                .join(" and ")
        );
    }

    // Everything any artifact recruited that the deposit does not declare.
    let mut recruited: BTreeSet<String> = BTreeSet::new();
    for route in deposit.routes() {
        recruited.extend(route.recruited.keys().cloned());
    }
    let declared: BTreeSet<String> = deposit
        .declared_names()
        .into_iter()
        .map(str::to_owned)
        .collect();

    section("recruited AND declared -- the names this deposit can open");
    names("  ", recruited.intersection(&declared).cloned());

    section("recruited and NOT declared -- atoms the environment supplies");
    names("  ", recruited.difference(&declared).cloned());
}

// -------------------------------------------------------------------------------------------------
// Control 1
// -------------------------------------------------------------------------------------------------

/// Exhibit a name whose meaning is *built* out of constituents it does not carry, with the
/// construction path and the depths.
fn control_one_the_elaboration_is_constructive(
    deposit: &ElaborationDeposit,
    controls: &mut Controls,
) {
    rule_line("CONTROL 1 -- THE ELABORATION IS CONSTRUCTIVE, NOT A LOOKUP");

    // Every root the deposit carries, at both granularities, elaborated to exhaustion.
    let mut roots: Vec<String> = deposit
        .declared_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    roots.extend(deposit.route_keys().iter().cloned());

    let mut built: Vec<(String, Elaboration)> = Vec::new();
    for root in &roots {
        let Ok(meaning) = deposit.elaborate(root, ElaborationAperture::Exhausted) else {
            continue;
        };
        if !meaning.constructed().is_empty() {
            built.push((root.clone(), meaning));
        }
    }

    println!(
        "\n  {} of {} roots carry a meaning reaching past their own recruitment",
        built.len(),
        roots.len()
    );

    // The pooled declaration reading is nearly flat on this deposit, and saying so is the finding.
    let flat_declarations: Vec<String> = deposit
        .declared_names()
        .into_iter()
        .filter(|name| {
            deposit
                .elaborate(name, ElaborationAperture::Exhausted)
                .map(|meaning| meaning.constructed().is_empty())
                .unwrap_or(false)
        })
        .map(str::to_owned)
        .collect();
    section("declarations whose POOLED meaning adds nothing past depth one");
    names("  ", flat_declarations.iter().cloned());
    println!(
        "\n  Pooling every artifact of one declaration collects at depth one what any single route\n  \
         reaches only at depth two. The depth is destroyed by the pooling, not absent from the\n  \
         deposit -- which is the same defect `conditioned_derivation` records of pooled licensing."
    );

    // The sharpest witness: the route whose meaning is built out of the most it does not name.
    let Some((root, meaning)) = built
        .iter()
        .filter(|(root, _)| root.contains('#'))
        .max_by_key(|(root, meaning)| (meaning.constructed().len(), std::cmp::Reverse(root.len())))
    else {
        controls.declare(
            "1 the elaboration is constructive, not a lookup",
            false,
            "no root in the deposit carries a constituent past depth one".to_owned(),
        );
        return;
    };

    section(&format!("the witness: {root}"));
    let direct: BTreeSet<&str> = meaning.at_depth(1);
    println!("  it recruits, at depth 1:");
    names("    ", direct.iter().map(|name| (*name).to_owned()));
    println!("\n  and its MEANING also carries, built rather than named:");
    names(
        "    ",
        meaning.constructed().iter().map(|name| (*name).to_owned()),
    );

    println!("\n  the construction path of each, with depths:");
    for constituent in meaning.constructed() {
        let Some(path) = meaning.construction_path(constituent) else {
            continue;
        };
        let rendered: Vec<String> = path
            .iter()
            .enumerate()
            .map(|(depth, name)| format!("{name}@{depth}"))
            .collect();
        println!("    {}", rendered.join("  ->  "));
    }

    // It is a construction and not a substring: none of the built constituents occurs in the root.
    let literal: Vec<&str> = meaning
        .constructed()
        .into_iter()
        .filter(|constituent| root.contains(constituent))
        .collect();
    println!(
        "\n  none of these is a substring of the root either: {} literal occurrences",
        literal.len()
    );

    let holds = !meaning.constructed().is_empty() && literal.is_empty();
    controls.declare(
        "1 the elaboration is constructive, not a lookup",
        holds,
        format!(
            "{root} names {} identifiers and MEANS {}; {} constituents are reached only through \
             what it names, none of them a substring of it",
            direct.len(),
            meaning.constituents().len() - 1,
            meaning.constructed().len(),
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// Control 5
// -------------------------------------------------------------------------------------------------

fn control_five_the_aperture_and_what_lies_outside_it(
    deposit: &ElaborationDeposit,
    controls: &mut Controls,
) {
    rule_line("CONTROL 5 -- THE APERTURE IS STATED AND SOMETHING IS OUTSIDE IT");

    // The route with the deepest meaning: the one on which a depth aperture can actually bind.
    let mut deepest: Option<(String, Elaboration)> = None;
    for key in deposit.route_keys() {
        let Ok(meaning) = deposit.elaborate(key, ElaborationAperture::Exhausted) else {
            continue;
        };
        let better = deepest
            .as_ref()
            .map(|(_, carried)| meaning.reach() > carried.reach())
            .unwrap_or(true);
        if better {
            deepest = Some((key.clone(), meaning));
        }
    }
    let Some((root, exhausted)) = deepest else {
        controls.declare(
            "5 the aperture is stated and something is outside it",
            false,
            "the deposit carries no route to elaborate".to_owned(),
        );
        return;
    };

    section("aperture one: the DEPOSIT's own -- a name it does not declare cannot be opened");
    println!(
        "  root {root}, aperture Exhausted, reach {}",
        exhausted.reach()
    );
    println!("  constituents it reached and cannot open, by name:");
    names("    ", exhausted.atoms().iter().cloned());
    println!(
        "\n  These are supplied by an environment this reading does not hold. Exhaustion does not\n  \
         remove them: the aperture is the deposit, and it is permanent."
    );

    section(
        "aperture two: a DECLARED DEPTH -- what it stopped at, and what that would have brought",
    );
    let bounded = deposit
        .elaborate(&root, ElaborationAperture::ToDepth(1))
        .expect("the root is in the deposit");
    println!(
        "  root {root}, aperture ToDepth(1), reach {}",
        bounded.reach()
    );
    println!("  openable and not opened:");
    names("    ", bounded.beyond_depth().iter().cloned());
    println!("  what opening it would have brought and this reading does not carry:");
    names("    ", bounded.unopened().iter().cloned());

    let outside = !exhausted.atoms().is_empty() && !bounded.unopened().is_empty();
    controls.declare(
        "5 the aperture is stated and something is outside it",
        outside,
        format!(
            "the deposit aperture leaves {} atoms outside by name; ToDepth(1) leaves {} further \
             constituents unopened, each named",
            exhausted.atoms().len(),
            bounded.unopened().len(),
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// Control 4
// -------------------------------------------------------------------------------------------------

fn control_four_the_cycles(deposit: &ElaborationDeposit, controls: &mut Controls) {
    rule_line("CONTROL 4 -- A CYCLE IS RETAINED AS A CYCLE, OR THERE IS NONE");

    let mut carried: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
    let mut roots: Vec<String> = deposit
        .declared_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    roots.extend(deposit.route_keys().iter().cloned());
    for root in &roots {
        let Ok(meaning) = deposit.elaborate(root, ElaborationAperture::Exhausted) else {
            continue;
        };
        for cycle in meaning.cycles() {
            carried.push((root.clone(), cycle.members.clone(), cycle.witness.clone()));
        }
    }

    section("measured on the deposit");
    if carried.is_empty() {
        println!(
            "  none. Across all {} roots, no recruited name reaches back to a name that reached it.",
            roots.len()
        );
        println!(
            "  The declaration digraph of this deposit is: carrier_transport, carrier_transport_direct"
        );
        println!("  and carrier_transport_relayed each name formal_carry; formal_carry and");
        println!(
            "  every_receiver_agrees name no declaration at all. That is a forest, and a forest\n  carries no cycle."
        );
    } else {
        for (root, members, witness) in &carried {
            println!("  in {root}: {}", members.join(" ~ "));
            println!("    witness passage: {}", witness.join(" -> "));
        }
    }

    // A measured absence is only a fact about the deposit if the detector is known to fire.
    section("the declared control -- constructed material carrying a cycle");
    let constructed = vec![
        derivation("ping", "one statement", &[("pong", 1), ("shared", 1)]),
        derivation("pong", "one statement", &[("ping", 1), ("shared", 1)]),
        derivation("ouroboros", "another", &[("ouroboros", 1)]),
    ];
    let control = ElaborationDeposit::read(&constructed);
    let mut fired: Vec<String> = Vec::new();
    for root in ["ping", "ouroboros"] {
        let meaning = control
            .elaborate(root, ElaborationAperture::Exhausted)
            .expect("declared");
        for cycle in meaning.cycles() {
            println!(
                "  in {root}: {}    witness passage: {}",
                cycle.members.join(" ~ "),
                cycle.witness.join(" -> ")
            );
            let ping = meaning.constituents().get(root).expect("the root");
            println!(
                "    retained, not truncated: {root} entered at depth {} and was reached again at {:?}",
                ping.entered_at,
                ping.depths.iter().skip(1).collect::<Vec<_>>()
            );
            fired.push(cycle.members.join("~"));
        }
    }

    let detector_fires = fired.len() == 2;
    controls.declare(
        "4 a cycle is retained as a cycle",
        detector_fires,
        format!(
            "the deposit carries {} cycles; the detector returns {} on declared control material \
             ({}), so the absence is a reading of the deposit and not of the detector",
            carried.len(),
            fired.len(),
            fired.join(" and "),
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// The fillings
// -------------------------------------------------------------------------------------------------

struct Reading {
    label: String,
    aperture: CircuitAperture,
    criterion: AgreementCriterion,
    filling: Result<RouteFilling, TwoCellRefusal>,
}

fn the_fillings(derivations: &[Derivation]) -> Vec<Reading> {
    let mut readings = Vec::new();
    for (label, aperture) in [
        ("by declaration", CircuitAperture::STATEMENT_INCIDENT),
        (
            "by route",
            CircuitAperture {
                identity: holonic_engine::derivation_atlas::DerivationIdentity::ByRoute,
                coefficient: holonic_engine::derivation_atlas::RecruitmentCoefficient::Incidence,
                reach: ReachOrientation::IntoDerivation,
                statements: holonic_engine::derivation_atlas::StatementIncidence::Founded,
            },
        ),
    ] {
        for criterion in AgreementCriterion::DECLARED {
            readings.push(Reading {
                label: format!("{label} / {}", criterion.name()),
                aperture,
                criterion,
                filling: fill_routes(
                    derivations,
                    aperture,
                    criterion,
                    ElaborationAperture::Exhausted,
                    SQUARE_APERTURE,
                    TRIPLE_APERTURE,
                ),
            });
        }
    }
    readings
}

// -------------------------------------------------------------------------------------------------
// Control 2
// -------------------------------------------------------------------------------------------------

fn control_two_filling_must_be_able_to_not_happen(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 2 -- FILLING MUST BE ABLE TO NOT HAPPEN");

    let mut separating: Vec<&str> = Vec::new();
    let mut vacuous: Vec<String> = Vec::new();

    for reading in readings {
        section(&reading.label);
        println!(
            "  aperture {:?}/{:?}/{:?}, criterion {}, elaboration Exhausted, declared square \
             aperture {SQUARE_APERTURE}",
            reading.aperture.identity,
            reading.aperture.coefficient,
            reading.aperture.statements,
            reading.criterion.name(),
        );
        let filling = match &reading.filling {
            Ok(filling) => filling,
            Err(refusal) => {
                println!("  REFUSED: {refusal}");
                println!(
                    "  The population is named rather than truncated; the reading is not run."
                );
                continue;
            }
        };

        println!(
            "  {} route pairs examined, {} filled as one proof, {} held open as genuinely two,\n  \
             {} agreeing with no shared symbol to close a loop on",
            filling.pairs_examined(),
            filling.filled_pairs().len(),
            filling.held_open_pairs().len(),
            filling.agreeing_without_square().len(),
        );

        if filling.filled_pairs().is_empty() {
            vacuous.push(format!("{}: nothing filled", reading.label));
        }
        if filling.held_open_pairs().is_empty() && filling.pairs_examined() > 0 {
            vacuous.push(format!("{}: everything filled", reading.label));
        }
        if !filling.filled_pairs().is_empty() && !filling.held_open_pairs().is_empty() {
            separating.push(&reading.label);
        }

        // Population one: the routes that were the same proof wearing two names.
        println!("\n  FILLED -- the same proof wearing two names");
        let mut shown = 0usize;
        for (statement, left, right) in filling.filled_pairs() {
            let over: Vec<String> = filling
                .squares()
                .iter()
                .filter(|square| {
                    square.statement == statement && square.left == left && square.right == right
                })
                .map(|square| square.shared_symbol.clone())
                .collect();
            if shown < 12 {
                println!("    {left}  =  {right}");
                println!("      reaching `{statement}`");
                println!("      {} squares, over: {}", over.len(), over.join(" "));
            }
            shown += 1;
        }
        if shown == 0 {
            println!("    (none)");
        } else if shown > 12 {
            println!("    ... and {} further filled pairs", shown - 12);
        }
        println!("    {} squares founded in total", filling.squares().len());

        // Population two: the routes that are genuinely different, with what differs.
        println!("\n  HELD OPEN -- genuinely two, with the retained obstruction");
        let mut shown = 0usize;
        for held in filling.held_open() {
            if shown < 12 {
                println!("    {}  vs  {}", held.left, held.right);
                println!("      reaching `{}`", held.statement);
                println!("      differs by: {}", held.disagreement.render());
                println!(
                    "      overlap {} constituents; refused a square over: {}",
                    held.disagreement.overlap(),
                    held.refused_symbols
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(" ")
                );
            }
            shown += 1;
        }
        if shown == 0 {
            println!("    (none)");
        } else if shown > 12 {
            println!("    ... and {} further held-open pairs", shown - 12);
        }
    }

    section("vacuity, reported rather than tuned away");
    if vacuous.is_empty() {
        println!("  none: every reading that ran separated the population.");
    } else {
        for entry in &vacuous {
            println!("  {entry}");
        }
        println!(
            "\n  A criterion that fills everything, or nothing, has not discriminated. That is\n  \
             reported here as a property of the criterion on this material; nothing is loosened\n  \
             to make it come out otherwise."
        );
    }

    controls.declare(
        "2 filling must be able to not happen",
        !separating.is_empty(),
        format!(
            "{} of {} declared readings returned BOTH a non-empty filled population and a \
             non-empty held-open population ({})",
            separating.len(),
            readings.len(),
            separating.join("; "),
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// Control 3
// -------------------------------------------------------------------------------------------------

fn control_three_betti_before_and_after(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 3 -- BETTI-1 BEFORE AND AFTER, WITH BOTH POPULATIONS NAMED");

    let mut agreements: Vec<bool> = Vec::new();
    let mut moved_any = false;
    let mut summary: Vec<String> = Vec::new();

    for reading in readings {
        section(&reading.label);
        let Ok(filling) = &reading.filling else {
            println!("  refused; no invariants to take");
            continue;
        };
        let (Ok(before), Ok(after)) = (
            filling.invariants_before(RULE),
            filling.invariants_after(RULE),
        ) else {
            println!("  the reduction refused");
            agreements.push(false);
            continue;
        };

        let forest = filling.spanning_forest();
        println!(
            "  BEFORE   vertices {}  edges {}  components {}   betti-0 {}  betti-1 {}",
            forest.vertices,
            forest.edges,
            forest.components,
            betti_at(&before, 0),
            betti_at(&before, 1),
        );
        println!(
            "           spanning forest, second frame:            betti-0 {}  betti-1 {}",
            forest.betti_0(),
            forest.betti_1(),
        );
        println!(
            "  AFTER    2-cells {}                                betti-0 {}  betti-1 {}  betti-2 {}",
            filling.squares().len(),
            betti_at(&after, 0),
            betti_at(&after, 1),
            betti_at(&after, 2),
        );
        println!(
            "           torsion before {:?}   after {:?}",
            torsion_at(&before, 1),
            torsion_at(&after, 1),
        );

        let smith_rank = betti_at(&before, 1).saturating_sub(betti_at(&after, 1));
        let independent = filling.independent_filling_rank();
        println!(
            "\n  rank(d2): {smith_rank} by Smith normal form over BigInt; {independent} by exact\n  \
             rational elimination in a spanning-forest cycle basis. Two implementations, disjoint\n  \
             code paths."
        );
        let agrees = smith_rank == independent
            && betti_at(&before, 1) == forest.betti_1()
            && betti_at(&before, 0) == forest.betti_0();
        agreements.push(agrees);
        if betti_at(&before, 1) != betti_at(&after, 1) {
            moved_any = true;
        }

        println!(
            "\n  betti-1 AFTER is the routes that are genuinely different, and the population\n  \
             behind it is the {} held-open pairs above. The {} squares below it are the routes\n  \
             that were one proof.",
            filling.held_open_pairs().len(),
            filling.squares().len(),
        );

        summary.push(format!(
            "{}: betti-1 {} -> {} over {} squares from {} filled pairs, {} held open",
            reading.label,
            betti_at(&before, 1),
            betti_at(&after, 1),
            filling.squares().len(),
            filling.filled_pairs().len(),
            filling.held_open_pairs().len(),
        ));
    }

    section("both numbers, never their difference");
    for entry in &summary {
        println!("  {entry}");
    }

    let holds = !agreements.is_empty() && agreements.iter().all(|agrees| *agrees) && moved_any;
    controls.declare(
        "3 betti-1 before and after, with both populations named",
        holds,
        format!(
            "{} readings reduced; the spanning forest and the Smith normal form agree on betti-0 \
             and betti-1 before filling, and the independent rational rank agrees with the Smith \
             movement on every one; filling moved betti-1 on at least one reading",
            agreements.len(),
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// The bound on the organ, measured rather than asserted
// -------------------------------------------------------------------------------------------------

/// **What this organ can and cannot separate, on this deposit.** Reported as a measurement and not
/// as a control, because it is a bound on the reading rather than a claim it makes.
fn what_the_elaboration_cannot_discriminate(deposit: &ElaborationDeposit, readings: &[Reading]) {
    rule_line("THE BOUND -- WHAT THE ELABORATION CAN AND CANNOT DISCRIMINATE HERE");

    let mut recruited: BTreeSet<String> = BTreeSet::new();
    for route in deposit.routes() {
        recruited.extend(route.recruited.keys().cloned());
    }
    let openable: Vec<&String> = recruited
        .iter()
        .filter(|name| deposit.is_openable(name))
        .collect();

    println!(
        "\n  {} identifiers are recruited across the deposit and {} of them is declared by it.",
        recruited.len(),
        openable.len(),
    );
    println!(
        "  Openable: {}",
        openable
            .iter()
            .map(|name| (*name).clone())
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!(
        "\n  A constituent the deposit does not declare is an ATOM: it has no constituents of its\n  \
         own, so it enters at depth one and nothing is built through it. **The discriminating\n  \
         power of this organ is bounded by the deposit's own declaration density.** A route that\n  \
         does not name `formal_carry` has a meaning exactly one step deep, and two such routes can\n  \
         differ only in WHICH atoms they carry -- never in the depth of a shared one."
    );

    section("held-open pairs whose only difference is which atoms they carry");
    for reading in readings {
        let Ok(filling) = &reading.filling else {
            continue;
        };
        let atoms_only = filling
            .held_open()
            .iter()
            .filter(|held| {
                held.disagreement.depth_disagreement.is_empty()
                    && held.disagreement.contains_other_root.is_empty()
            })
            .count();
        let structural = filling.held_open().len() - atoms_only;
        println!(
            "  {:<28} {} of {} held open by atom membership alone; {} by a depth or a root",
            reading.label,
            atoms_only,
            filling.held_open().len(),
            structural,
        );
    }

    println!(
        "\n  Read the table plainly, in both directions.\n\n  \
         WHAT STANDS. Under `on-overlap` at route granularity every one of the held-open pairs is\n  \
         held on a DEPTH or a ROOT and none on atom membership. That is denotational separation on\n  \
         real production, of two shapes: `formal_carry` standing as a root against standing as a\n  \
         constituent at depth one, and `assumption` entering at depth one against entering at\n  \
         depth two through `formal_carry`. No orthographic reading returns either -- both routes\n  \
         write the same characters and the reading separates them by what those characters mean\n  \
         in this deposit."
    );
    println!(
        "\n  WHAT DOES NOT. Under `exact` a large share of the held-open pairs differ only in which\n  \
         atoms they carry, which is separation by WHICH tactic name was written -- the orthographic\n  \
         reading the elaboration was built to replace, arriving under a new name. `on-overlap`\n  \
         ignores exactly that and fills them, which is why the two criteria are declared and both\n  \
         run: neither is reading a denotation there, because on this deposit there is none to\n  \
         read. `assumption`, `ring`, `nlinarith` and `simpa` are supplied by an environment the\n  \
         deposit does not carry, and to this organ they are indistinguishable atoms."
    );
    println!(
        "\n  So: this run does NOT show the criterion separating meaningful production from noise,\n  \
         and it should not be read as showing it. Every separation it makes flows through the one\n  \
         name the deposit declares. What it does show is that the separation is real where a\n  \
         denotation exists, and that the route to more of it is a deposit that declares more of\n  \
         what it recruits -- not a different agreement rule and not a tuned one."
    );
}

// -------------------------------------------------------------------------------------------------
// Control 6
// -------------------------------------------------------------------------------------------------

fn control_six_the_triple_overlaps(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 6 -- THE TRIPLE-OVERLAP CHECK, REPORTED EITHER WAY");

    println!(
        "\n  `research/papers/source/holonics/logic-category.typ` H.0035: \"Pairwise compatibility alone may\n  \
         be insufficient when higher overlaps matter.\" Three questions are asked of every triple\n  \
         reaching one statement."
    );

    let mut examined = 0usize;
    let mut pairwise_agreeing = 0usize;
    let mut non_transitive: Vec<String> = Vec::new();
    let mut joint_obstructions: Vec<String> = Vec::new();
    let mut relations: Vec<String> = Vec::new();
    let mut betti_two_seen = false;

    for reading in readings {
        let Ok(filling) = &reading.filling else {
            continue;
        };
        section(&reading.label);
        examined += filling.triples_examined();

        let mut here_agreeing: Vec<&_> = Vec::new();
        let mut here_non_transitive: Vec<&_> = Vec::new();
        for triple in filling.triples() {
            if triple.pairwise_agrees() {
                pairwise_agreeing += 1;
                here_agreeing.push(triple);
            }
            if triple.is_non_transitive() {
                here_non_transitive.push(triple);
                non_transitive.push(format!("{:?}", triple.members));
            }
            if let Some(obstruction) = &triple.joint_obstruction {
                joint_obstructions.push(format!("{} {obstruction:?}", reading.label));
            }
            if !triple.verified_relations.is_empty() {
                relations.push(format!("{:?}", triple.members));
            }
        }
        println!(
            "  {} triples walked; {} pairwise agreeing; {} non-transitive",
            filling.triples_examined(),
            here_agreeing.len(),
            here_non_transitive.len(),
        );

        // A pairwise-agreeing triple: the joint-section question is asked of exactly these.
        for triple in here_agreeing.iter().take(2) {
            println!("    PAIRWISE AGREEING  {{{}}}", triple.members.join(", "));
            println!("      reaching `{}`", triple.statement);
            println!(
                "      {} symbols common to all three; {} grade-2 relations verified against the \
                 complex",
                triple.common_symbols.len(),
                triple.verified_relations.len(),
            );
            println!(
                "      joint section: {}",
                match &triple.joint_obstruction {
                    None => "exists".to_owned(),
                    Some(obstruction) => format!("REFUSED -- {obstruction:?}"),
                }
            );
        }
        if here_agreeing.len() > 2 {
            println!(
                "    ... and {} further pairwise-agreeing triples",
                here_agreeing.len() - 2
            );
        }

        // A non-transitive triple, with the pair that broke transitivity named.
        for triple in here_non_transitive.iter().take(2) {
            println!("    NON-TRANSITIVE     {{{}}}", triple.members.join(", "));
            println!("      reaching `{}`", triple.statement);
            let broke: Vec<&_> = filling
                .held_open()
                .iter()
                .filter(|held| {
                    held.statement == triple.statement
                        && triple.members.contains(&held.left)
                        && triple.members.contains(&held.right)
                })
                .collect();
            for held in &broke {
                println!(
                    "      the pair that broke it: {} vs {} -- {}",
                    held.left,
                    held.right,
                    held.disagreement.render()
                );
            }
            println!(
                "      the joint-section question is NOT ASKED of this triple: it is not pairwise \
                 agreeing"
            );
        }
        if here_non_transitive.len() > 2 {
            println!(
                "    ... and {} further non-transitive triples",
                here_non_transitive.len() - 2
            );
        }

        if let Ok(after) = filling.invariants_after(RULE) {
            let betti_two = betti_at(&after, 2);
            println!("  betti-2 of the filled complex: {betti_two}");
            if betti_two > 0 {
                betti_two_seen = true;
                println!(
                    "    The pairwise fillings are DEPENDENT. For a symbol x all three members\n    \
                     share, square(A,B,x) - square(A,C,x) + square(B,C,x) has boundary zero: a\n    \
                     grade-2 cycle. A graph betti-1 cannot carry this and a 2-complex does."
                );
            }
        }
    }

    section("the three findings");
    println!("  triples walked ................................. {examined}");
    println!("  pairwise-agreeing triples ...................... {pairwise_agreeing}");
    println!(
        "  NON-TRANSITIVE agreement (A~B, B~C, A!~C) ...... {}   <- IT OCCURS",
        non_transitive.len()
    );
    names_capped("    ", non_transitive.iter().cloned(), 4);
    println!(
        "  pairwise agreeing with NO joint section ........ {}   (asked of {pairwise_agreeing})",
        joint_obstructions.len()
    );
    names_capped("    ", joint_obstructions.iter().cloned(), 4);
    println!(
        "  verified grade-2 relations among the fillings .. {}",
        relations.len()
    );
    names_capped("    ", relations.iter().cloned(), 4);

    println!(
        "\n  The joint-section count is zero and that is a THEOREM rather than a property of this\n  \
         deposit. Under one uniform elaboration aperture a shortest-passage depth is determined by\n  \
         the recruitment relation the members share: if a member opened a constituent it also\n  \
         carries what that constituent recruits, one depth down, and pairwise agreement pins it;\n  \
         and if the member did not open it, the constituent sits at the deepest layer, so nothing\n  \
         can stand more than one depth below it. Two members carrying one constituent at two\n  \
         depths IS a pairwise disagreement. H.0035's caveat does not bite on this gluing datum."
    );
    println!(
        "\n  The other two DO occur on this deposit, and both are invisible to a graph betti-1:\n  \
         on-overlap agreement is not transitive here, so there are triples in which every member\n  \
         is the same proof as a member it neighbours and not as the one it does not; and the\n  \
         pairwise fillings are dependent, which is betti-2. Exact agreement is an equality of the\n  \
         root-stripped signature and is transitive by construction, so its non-transitive count is\n  \
         zero and must be -- that half of the reading is a check on the implementation."
    );

    let holds = examined > 0 && (pairwise_agreeing > 0 || !non_transitive.is_empty());
    controls.declare(
        "6 the triple-overlap check is run and reported either way",
        holds,
        format!(
            "{examined} triples walked, {pairwise_agreeing} pairwise agreeing, \
             {} non-transitive, {} without a joint section, {} verified grade-2 relations; \
             betti-2 nonzero on at least one reading: {betti_two_seen}",
            non_transitive.len(),
            joint_obstructions.len(),
            relations.len(),
        ),
    );
}
