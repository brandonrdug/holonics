//! Read the machine's own deposited names in **both** directions, and found the face at the
//! crossing rather than only at the agreement.
//!
//! ```text
//! cargo run --release --example the_consequent_is_the_other_half_of_a_meaning -- standing/output
//! ```
//!
//! ## The defect this driver measures against
//!
//! `holonic_engine::name_elaboration` returned a name's **transitive recruitment closure** — what it
//! is built *from*, walking downward — and on this deposit it concluded that seventeen of eighteen
//! recruited identifiers are atoms with empty elaborations and are therefore undiscriminable.
//!
//! `holonic_engine::derivation_atlas` carries the other edge species, and says so in its own header:
//! a **reach**, *this derivation proved that statement*. So:
//!
//! > **An atom's downward closure is empty and its upward closure is its whole meaning.**
//!
//! `apply` has no constituents, so its elaboration is `{}` — and `apply` participates in reaching a
//! particular population of statements, and that population is what `apply` means here.
//! Downward-empty is not meaning-empty, and the conclusion followed from walking one direction and
//! calling the other absent.
//!
//! The meaning of a name is therefore a **pair**: its antecedent closure and its consequent closure.
//! Neither alone. This driver returns both, never merged, and adds the **crossing** — the
//! intersection of two meanings — as a declared criterion beside the two agreements of the whole.
//!
//! ## The declared controls
//!
//! Each is printed with its evidence and the run exits non-zero if any fails.
//!
//! ```text
//!   1  the consequent reading is non-empty where the antecedent reading is empty
//!   2  two atoms with identical recruitment are separated by their consequents -- or the upward
//!      reading adds nothing here and that is the return
//!   3  a pair held open by whole-agreement that crosses at a named constituent
//!   4  the criteria disagree: the three families do not found one population
//!   5  betti-1 under each criterion, with the population behind each
//!   6  four apertures declared, with what lies outside each named
//! ```
//!
//! ## No float, no scalar governor
//!
//! Every number printed is a population or a depth. Nothing here compares two magnitudes to select,
//! rank, drop, or prefer: a criterion is a structural predicate, the crossing width is reported and
//! never consulted, and every criterion's population is returned whole beside every other's.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{
    CircuitAperture, Derivation, DerivationIdentity, RecruitmentCoefficient, StatementIncidence,
    read_derivation,
};
use holonic_engine::derivation_two_cells::{
    AgreementCriterion, AgreementShape, MeaningDirection, RouteFilling, TwoCellRefusal, betti_at,
    fill_routes,
};
use holonic_engine::name_elaboration::{
    ConsequentClosure, ConsequentSpecies, ElaborationAperture, ElaborationDeposit, NameMeaning,
};
use holonic_engine::rebase_invariants::PivotRule;

/// The declared square population any one reading may found. Exceeding it **refuses the reading
/// with its size** rather than truncating it.
const SQUARE_APERTURE: usize = 60_000;

/// The declared triple population any one reading may walk.
const TRIPLE_APERTURE: usize = 400_000;

/// The pivot rule every integer reduction here is taken under. A pivot order is a receiver
/// coordinate and is never compared as an invariant.
const RULE: PivotRule = PivotRule::FirstNonzero;

/// The declared depth for the bounded-aperture demonstrations, in both directions.
const BOUNDED_DEPTH: usize = 1;

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

fn names(indent: &str, population: impl IntoIterator<Item = String>) {
    names_capped(indent, population, usize::MAX);
}

/// One rendered obstruction, clipped for the page with what was clipped stated.
///
/// A cap on what is **printed** is not a cap on what is returned: the whole disagreement lives on
/// `RouteFilling::held_open` and `RouteFilling::pairs`, and a caller that wants all of it takes it
/// from there. One obstruction on this deposit names fifty-two constituents on one line.
fn clip(line: &str, width: usize) -> String {
    if line.len() <= width {
        return line.to_owned();
    }
    let mut cut = width;
    while cut > 0 && !line.is_char_boundary(cut) {
        cut -= 1;
    }
    format!(
        "{}... [{} further characters on the reading]",
        &line[..cut],
        line.len() - cut
    )
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
    println!("law=the meaning of a name is a PAIR: what it is built from, and what it reaches");
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

    let atoms = the_deposit_in_both_directions(&deposit);
    control_one_the_consequent_is_non_empty_where_the_antecedent_is_not(
        &deposit,
        &atoms,
        &mut controls,
    );
    control_two_the_atoms_recruitment_cannot_separate(&deposit, &atoms, &mut controls);

    let readings = the_fillings(&derivations);
    control_three_a_pair_held_open_that_crosses(&readings, &mut controls);
    control_four_the_criteria_disagree(&readings, &mut controls);
    control_five_betti_under_each_criterion(&readings, &mut controls);
    control_six_the_four_apertures(&deposit, &atoms, &mut controls);
    what_this_reading_does_not_show(&deposit, &readings);

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
// The deposit, read both ways
// -------------------------------------------------------------------------------------------------

/// Every recruited identifier the deposit does not declare, in read order. The population the
/// downward reading called undiscriminable.
fn the_deposit_in_both_directions(deposit: &ElaborationDeposit) -> Vec<String> {
    rule_line("THE DEPOSIT, READ IN BOTH DIRECTIONS");

    let mut recruited: BTreeSet<String> = BTreeSet::new();
    for route in deposit.routes() {
        recruited.extend(route.recruited.keys().cloned());
    }
    let declared: BTreeSet<String> = deposit
        .declared_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    let atoms: Vec<String> = recruited.difference(&declared).cloned().collect();

    println!(
        "\n  {} identifiers recruited, {} of them declared, {} of them atoms.",
        recruited.len(),
        recruited.intersection(&declared).count(),
        atoms.len(),
    );

    section("every recruited identifier, in both directions");
    println!(
        "  {:<20} {:>10} {:>10} {:>10} {:>10}  {}",
        "name", "antecedent", "a-reach", "consequent", "c-reach", "shape"
    );
    for name in &recruited {
        let Ok(meaning) = deposit.meaning(name, ElaborationAperture::Exhausted) else {
            continue;
        };
        println!(
            "  {:<20} {:>10} {:>10} {:>10} {:>10}  {}",
            name,
            meaning.antecedent().constituents().len(),
            meaning.antecedent().reach(),
            meaning.consequent().constituents().len(),
            meaning.consequent().reach(),
            meaning.shape().name(),
        );
    }

    println!(
        "\n  The `antecedent` column is the reading that returned 1 for seventeen of these and\n  \
         concluded they could not be told apart. The `consequent` column is the same names read\n  \
         the other way. **The two columns are not two views of one population; they are two\n  \
         relations, and nothing here adds them.**"
    );

    atoms
}

// -------------------------------------------------------------------------------------------------
// Control 1
// -------------------------------------------------------------------------------------------------

/// Print one consequent closure whole: species, depths, passages, and the statements it reaches.
fn exhibit(closure: &ConsequentClosure) {
    let mut by_depth: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for carried in closure.constituents().values() {
        by_depth
            .entry(carried.entered_at)
            .or_default()
            .push(format!("{} [{}]", carried.name, carried.species.name()));
    }
    for (depth, members) in by_depth {
        println!("    depth {depth}:");
        names_capped("      ", members, 24);
    }
    println!(
        "    statements reached: {}",
        closure
            .terminal_statements()
            .iter()
            .map(|statement| format!("`{statement}`"))
            .collect::<Vec<_>>()
            .join("  ")
    );
}

fn control_one_the_consequent_is_non_empty_where_the_antecedent_is_not(
    deposit: &ElaborationDeposit,
    atoms: &[String],
    controls: &mut Controls,
) {
    rule_line("CONTROL 1 -- THE CONSEQUENT IS NON-EMPTY WHERE THE ANTECEDENT IS EMPTY");

    let mut both_ways: Vec<(String, NameMeaning)> = Vec::new();
    for atom in atoms {
        let Ok(meaning) = deposit.meaning(atom, ElaborationAperture::Exhausted) else {
            continue;
        };
        if meaning.antecedent_is_empty() && !meaning.consequent_is_empty() {
            both_ways.push((atom.clone(), meaning));
        }
    }

    section("every atom whose antecedent closure is empty and whose consequent closure is not");
    names("  ", both_ways.iter().map(|(name, _)| name.clone()));

    // The named candidates the task singles out, exhibited whole.
    for wanted in ["apply", "assumption", "rw", "simpa"] {
        let Some((name, meaning)) = both_ways.iter().find(|(name, _)| name == wanted) else {
            continue;
        };
        section(&format!("`{name}` -- the full pair"));
        println!(
            "    ANTECEDENT: {} constituents, reach {}, atoms {:?}",
            meaning.antecedent().constituents().len(),
            meaning.antecedent().reach(),
            meaning
                .antecedent()
                .atoms()
                .iter()
                .cloned()
                .collect::<Vec<_>>(),
        );
        println!(
            "      -- the root alone. Nothing is built beneath it and that is what `{{}}` means.\n"
        );
        println!(
            "    CONSEQUENT: {} constituents, reach {}",
            meaning.consequent().constituents().len(),
            meaning.consequent().reach(),
        );
        exhibit(meaning.consequent());
        if let Some(path) = meaning
            .consequent()
            .constituents()
            .keys()
            .filter_map(|name| meaning.consequent().consequence_path(name))
            .max_by_key(Vec::len)
        {
            println!("    one longest consequence path: {}", path.join("  ->  "));
        }
        println!(
            "    declarations it reaches: {}",
            meaning
                .consequent()
                .of_species(ConsequentSpecies::Declaration)
                .into_iter()
                .collect::<Vec<_>>()
                .join(" ")
        );
    }

    let holds = !both_ways.is_empty();
    controls.declare(
        "1 the consequent reading is non-empty where the antecedent reading is empty",
        holds,
        if holds {
            format!(
                "{} of {} atoms carry an empty antecedent closure and a non-empty consequent one; \
                 `{}` carries {} consequents at reach {}",
                both_ways.len(),
                atoms.len(),
                both_ways[0].0,
                both_ways[0].1.consequent().constituents().len(),
                both_ways[0].1.consequent().reach(),
            )
        } else {
            "no atom carries a non-empty consequent closure; the framing is wrong and that is the \
             result"
                .to_owned()
        },
    );
}

// -------------------------------------------------------------------------------------------------
// Control 2
// -------------------------------------------------------------------------------------------------

fn control_two_the_atoms_recruitment_cannot_separate(
    deposit: &ElaborationDeposit,
    atoms: &[String],
    controls: &mut Controls,
) {
    rule_line("CONTROL 2 -- WHAT RECRUITMENT CANNOT SEPARATE, CONSEQUENTS DO OR DO NOT");

    // Downward: every atom's antecedent closure is the root alone, so the downward signature with
    // the root set aside is EMPTY for all of them. One block, seventeen members.
    let mut downward: BTreeMap<Vec<(String, usize)>, Vec<String>> = BTreeMap::new();
    let mut upward: BTreeMap<Vec<(String, usize)>, Vec<String>> = BTreeMap::new();
    for atom in atoms {
        let Ok(meaning) = deposit.meaning(atom, ElaborationAperture::Exhausted) else {
            continue;
        };
        let antecedent: Vec<(String, usize)> = meaning
            .antecedent()
            .signature()
            .into_iter()
            .filter(|(name, _)| name != atom)
            .map(|(name, depth)| (name.to_owned(), depth))
            .collect();
        let consequent: Vec<(String, usize)> = meaning
            .consequent()
            .signature()
            .into_iter()
            .filter(|(name, _)| name != atom)
            .map(|(name, depth)| (name.to_owned(), depth))
            .collect();
        downward.entry(antecedent).or_default().push(atom.clone());
        upward.entry(consequent).or_default().push(atom.clone());
    }

    section("the atoms partitioned by their ANTECEDENT closure");
    println!("  {} block(s) over {} atoms", downward.len(), atoms.len());
    for (slot, members) in downward.values().enumerate() {
        println!("  block {slot}:");
        names("    ", members.iter().cloned());
    }

    section("the atoms partitioned by their CONSEQUENT closure");
    println!("  {} block(s) over {} atoms", upward.len(), atoms.len());
    for (slot, (signature, members)) in upward.iter().enumerate() {
        println!("  block {slot} ({} consequents):", signature.len());
        names("    ", members.iter().cloned());
    }
    let collapsed: Vec<&Vec<String>> = upward
        .values()
        .filter(|members| members.len() > 1)
        .collect();
    println!(
        "\n  and what the upward reading STILL collapses, named rather than left as a difference\n  \
         of two counts:"
    );
    if collapsed.is_empty() {
        println!("    (nothing: every atom carries its own consequent closure)");
    } else {
        for members in &collapsed {
            println!(
                "    {} -- recruited by exactly the same routes, so nothing above them separates them",
                members.join(" ~ ")
            );
        }
    }

    // Exhibit a separated pair and name the separating consequent. The two roots are set aside on
    // both sides, exactly as the pair comparison sets them aside: two atoms have different names by
    // hypothesis and that is not a separation. A pair separated in BOTH directions is exhibited when
    // one exists, because a one-sided containment is a weaker witness and saying which was found is
    // part of the return.
    let mut two_sided: Option<(String, String, Vec<String>, Vec<String>)> = None;
    let mut one_sided: Option<(String, String, Vec<String>, Vec<String>)> = None;
    let blocks: Vec<&Vec<String>> = upward.values().collect();
    for (left_slot, left_block) in blocks.iter().enumerate() {
        for right_block in blocks.iter().skip(left_slot + 1) {
            let (Some(left), Some(right)) = (left_block.first(), right_block.first()) else {
                continue;
            };
            let set_aside = |name: &str| name == left.as_str() || name == right.as_str();
            let Ok(left_meaning) = deposit.meaning(left, ElaborationAperture::Exhausted) else {
                continue;
            };
            let Ok(right_meaning) = deposit.meaning(right, ElaborationAperture::Exhausted) else {
                continue;
            };
            let left_names: BTreeSet<String> = left_meaning
                .consequent()
                .signature()
                .keys()
                .filter(|name| !set_aside(name))
                .map(|name| (*name).to_owned())
                .collect();
            let right_names: BTreeSet<String> = right_meaning
                .consequent()
                .signature()
                .keys()
                .filter(|name| !set_aside(name))
                .map(|name| (*name).to_owned())
                .collect();
            let only_left: Vec<String> = left_names.difference(&right_names).cloned().collect();
            let only_right: Vec<String> = right_names.difference(&left_names).cloned().collect();
            if only_left.is_empty() && only_right.is_empty() {
                continue;
            }
            let witness = (left.clone(), right.clone(), only_left, only_right);
            if !witness.2.is_empty() && !witness.3.is_empty() {
                if two_sided.is_none() {
                    two_sided = Some(witness);
                }
            } else if one_sided.is_none() {
                one_sided = Some(witness);
            }
        }
    }
    let separated = two_sided.clone().or_else(|| one_sided.clone());

    section("a separated pair, with the separating consequent named");
    match &separated {
        Some((left, right, only_left, only_right)) => {
            println!(
                "  `{left}` and `{right}`  ({} separation; the two roots are set aside on both \
                 sides as hypothesis)",
                if two_sided.is_some() {
                    "two-sided"
                } else {
                    "one-sided containment"
                }
            );
            println!(
                "    both antecedent closures: the root alone. Recruitment cannot separate them."
            );
            println!("    consequents only `{left}` reaches:");
            names_capped("      ", only_left.iter().cloned(), 16);
            println!("    consequents only `{right}` reaches:");
            names_capped("      ", only_right.iter().cloned(), 16);
        }
        None => println!("  (none: every atom carries the same consequent closure)"),
    }

    let holds = upward.len() > 1 && separated.is_some();
    controls.declare(
        "2 two atoms with identical recruitment are separated by their consequents",
        holds,
        if holds {
            let (left, right, only_left, only_right) = separated.expect("checked");
            format!(
                "the antecedent reading returns {} block over {} atoms and the consequent reading \
                 returns {}; `{left}` and `{right}` are separated by {} consequents on the left and \
                 {} on the right, first `{}`",
                downward.len(),
                atoms.len(),
                upward.len(),
                only_left.len(),
                only_right.len(),
                only_left
                    .first()
                    .or_else(|| only_right.first())
                    .cloned()
                    .unwrap_or_default(),
            )
        } else {
            format!(
                "the consequent reading returns {} block over {} atoms, the same as the antecedent \
                 reading's {}: THE UPWARD READING ADDS NOTHING HERE and that is the measurement",
                upward.len(),
                atoms.len(),
                downward.len(),
            )
        },
    );
}

// -------------------------------------------------------------------------------------------------
// The fillings: the full criterion grid at both declared circuit apertures
// -------------------------------------------------------------------------------------------------

struct Reading {
    label: String,
    aperture_name: &'static str,
    criterion: AgreementCriterion,
    filling: Result<RouteFilling, TwoCellRefusal>,
}

const BY_ROUTE: CircuitAperture = CircuitAperture {
    identity: DerivationIdentity::ByRoute,
    coefficient: RecruitmentCoefficient::Incidence,
    statements: StatementIncidence::Founded,
};

fn the_fillings(derivations: &[Derivation]) -> Vec<Reading> {
    let mut readings = Vec::new();
    for (aperture_name, aperture) in [
        ("by declaration", CircuitAperture::STATEMENT_INCIDENT),
        ("by route", BY_ROUTE),
    ] {
        for criterion in AgreementCriterion::EVERY {
            readings.push(Reading {
                label: format!("{aperture_name} / {}", criterion.name()),
                aperture_name,
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

/// One reading per aperture is enough to read every criterion's verdict, because `pairs()` carries
/// all twelve. Take the first that ran.
fn a_reading_per_aperture(readings: &[Reading]) -> Vec<&Reading> {
    let mut taken: BTreeMap<&str, &Reading> = BTreeMap::new();
    for reading in readings {
        if reading.filling.is_ok() {
            taken.entry(reading.aperture_name).or_insert(reading);
        }
    }
    taken.into_values().collect()
}

// -------------------------------------------------------------------------------------------------
// Control 3
// -------------------------------------------------------------------------------------------------

fn control_three_a_pair_held_open_that_crosses(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 3 -- A PAIR WHOLE-AGREEMENT HOLDS OPEN THAT CROSSES AT A CONSTITUENT");

    let mut exhibited = 0usize;
    let mut evidence = String::new();
    let mut totals: Vec<String> = Vec::new();

    for reading in a_reading_per_aperture(readings) {
        let Ok(filling) = &reading.filling else {
            continue;
        };
        let crossing_while_open: Vec<_> = filling
            .pairs()
            .iter()
            .filter(|pair| {
                !pair.agrees(AgreementCriterion::Exact)
                    && !pair.agrees(AgreementCriterion::OnOverlap)
                    && pair.agrees(AgreementCriterion::Crossing)
            })
            .collect();
        totals.push(format!(
            "{}: {} of {} pairs",
            reading.aperture_name,
            crossing_while_open.len(),
            filling.pairs().len()
        ));

        section(&format!(
            "{} -- held open by BOTH agreements, and crossing anyway",
            reading.aperture_name
        ));
        if crossing_while_open.is_empty() {
            println!(
                "  (none) The intersection reading is SUBSUMED by agreement at this aperture: every\n  \
                 pair either agrees on the whole or meets nowhere. Reported, not manufactured."
            );
            continue;
        }
        println!(
            "  {} of {} examined pairs",
            crossing_while_open.len(),
            filling.pairs().len()
        );
        for pair in crossing_while_open.iter().take(3) {
            println!("\n  {}  vs  {}", pair.left, pair.right);
            println!("    reaching `{}`", pair.statement);
            println!("    the whole refused it: {}", pair.antecedent.render());
            println!(
                "    and it CROSSES at {} constituent(s): {}",
                pair.antecedent_crossing().width(),
                pair.antecedent_crossing().render()
            );
            for (name, depth) in pair.antecedent_crossing().at_one_depth.iter().take(4) {
                println!("      `{name}` at depth {depth} on both sides, entered by");
                for arrival in pair
                    .antecedent_crossing()
                    .entered_left
                    .get(name)
                    .into_iter()
                    .flatten()
                {
                    println!("        left   {arrival}");
                }
                for arrival in pair
                    .antecedent_crossing()
                    .entered_right
                    .get(name)
                    .into_iter()
                    .flatten()
                {
                    println!("        right  {arrival}");
                }
            }
            let constructed = pair.antecedent_crossing().constructed();
            println!(
                "    of those, {} are CONSTRUCTED crossings (neither side named them): {}",
                constructed.len(),
                constructed.keys().copied().collect::<Vec<_>>().join(" ")
            );
        }
        if exhibited == 0 {
            let pair = crossing_while_open[0];
            evidence = format!(
                "{} at {}: `{}` vs `{}` reaching `{}` is refused by both agreements ({}) and \
                 crosses at {}",
                crossing_while_open.len(),
                reading.aperture_name,
                pair.left,
                pair.right,
                pair.statement,
                pair.antecedent.render(),
                pair.antecedent_crossing().render(),
            );
        }
        exhibited += crossing_while_open.len();
    }

    controls.declare(
        "3 a pair held open by whole-agreement that crosses at a constituent",
        exhibited > 0,
        if exhibited > 0 {
            evidence
        } else {
            format!(
                "no such pair at any declared aperture ({}); the intersection reading is subsumed \
                 by agreement on this deposit",
                totals.join("; ")
            )
        },
    );
}

// -------------------------------------------------------------------------------------------------
// Control 4
// -------------------------------------------------------------------------------------------------

fn control_four_the_criteria_disagree(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 4 -- THE CRITERIA FOUND DIFFERENT POPULATIONS");

    let mut families_separate = false;
    let mut evidence: Vec<String> = Vec::new();

    for reading in a_reading_per_aperture(readings) {
        let Ok(filling) = &reading.filling else {
            continue;
        };

        section(&format!(
            "{} -- what each declared criterion admits, over {} examined pairs",
            reading.aperture_name,
            filling.pairs().len()
        ));
        println!("  {:<34} {:>10}", "criterion", "admitted");
        let mut populations: BTreeMap<AgreementCriterion, BTreeSet<(&str, &str, &str)>> =
            BTreeMap::new();
        for criterion in AgreementCriterion::EVERY {
            let admitted = filling.admitted_by(criterion);
            println!("  {:<34} {:>10}", criterion.name(), admitted.len());
            populations.insert(criterion, admitted);
        }
        let distinct: BTreeSet<&BTreeSet<(&str, &str, &str)>> = populations.values().collect();
        println!(
            "\n  {} declared criteria collapse onto {} distinct admitted populations here.",
            populations.len(),
            distinct.len()
        );

        // The three families the control names.
        let antecedent_agreement: BTreeSet<_> = populations[&AgreementCriterion::OnOverlap].clone();
        let consequent_agreement: BTreeSet<_> =
            populations[&AgreementCriterion::ConsequentOnOverlap].clone();
        let intersection_crossing: BTreeSet<_> = populations[&AgreementCriterion::Crossing].clone();
        let three: BTreeSet<&BTreeSet<(&str, &str, &str)>> = BTreeSet::from([
            &antecedent_agreement,
            &consequent_agreement,
            &intersection_crossing,
        ]);
        println!(
            "  the three named families -- antecedent-agreement {}, consequent-agreement {}, \
             intersection-crossing {} -- are {} distinct populations",
            antecedent_agreement.len(),
            consequent_agreement.len(),
            intersection_crossing.len(),
            three.len(),
        );
        if three.len() >= 2 {
            families_separate = true;
        }
        evidence.push(format!(
            "{}: {} of {} criteria distinct, the three named families {} distinct",
            reading.aperture_name,
            distinct.len(),
            populations.len(),
            three.len()
        ));

        // The 2x2 the task asks for by name.
        section(&format!(
            "{} -- both directions at once, as four populations",
            reading.aperture_name
        ));
        let mut quadrants: BTreeMap<(bool, bool), Vec<String>> = BTreeMap::new();
        for pair in filling.pairs() {
            let down = pair.antecedent.agrees(AgreementShape::OnOverlap);
            let up = pair.consequent.agrees(AgreementShape::OnOverlap);
            quadrants
                .entry((down, up))
                .or_default()
                .push(format!("{} ~ {}", pair.left, pair.right));
        }
        for (down, up) in [(true, true), (true, false), (false, true), (false, false)] {
            let members = quadrants.remove(&(down, up)).unwrap_or_default();
            println!(
                "  antecedents {:<8} consequents {:<8}  {} pairs",
                if down { "AGREE" } else { "differ" },
                if up { "AGREE" } else { "differ" },
                members.len()
            );
            names_capped("      ", members, 6);
        }
        println!(
            "\n  Two routes that agree on antecedents may disagree on consequents and the reverse.\n  \
             Both off-diagonal quadrants above are the evidence, and neither direction is a\n  \
             refinement of the other. **No criterion here is preferred; all twelve are returned.**"
        );
    }

    controls.declare(
        "4 the criteria found different populations",
        families_separate,
        if families_separate {
            format!(
                "{} -- the distinction is not decorative",
                evidence.join("; ")
            )
        } else {
            format!(
                "{} -- every criterion founds one population and THE DISTINCTION IS DECORATIVE",
                evidence.join("; ")
            )
        },
    );
}

// -------------------------------------------------------------------------------------------------
// Control 5
// -------------------------------------------------------------------------------------------------

fn control_five_betti_under_each_criterion(readings: &[Reading], controls: &mut Controls) {
    rule_line("CONTROL 5 -- BETTI-1 UNDER EACH CRITERION, WITH THE POPULATION BEHIND EACH");

    let mut moved: BTreeSet<usize> = BTreeSet::new();
    let mut ran = 0usize;
    let mut ranks_agree = true;

    let mut aperture = "";
    for reading in readings {
        if reading.aperture_name != aperture {
            aperture = reading.aperture_name;
            section(&format!("{aperture} -- one circuit, twelve fillings"));
            println!(
                "  {:<34} {:>7} {:>7} {:>8} {:>8} {:>8} {:>9}",
                "criterion", "b1 pre", "b1 post", "squares", "filled", "open", "rank(d2)"
            );
        }
        match &reading.filling {
            Ok(filling) => {
                let (Ok(before), Ok(after)) = (
                    filling.invariants_before(RULE),
                    filling.invariants_after(RULE),
                ) else {
                    println!("  {:<34} the invariants refused", reading.criterion.name());
                    continue;
                };
                let pre = betti_at(&before, 1);
                let post = betti_at(&after, 1);
                let rank = filling.independent_filling_rank();
                if pre - post != rank {
                    ranks_agree = false;
                }
                moved.insert(post);
                ran += 1;
                println!(
                    "  {:<34} {:>7} {:>7} {:>8} {:>8} {:>8} {:>9}",
                    reading.criterion.name(),
                    pre,
                    post,
                    filling.squares().len(),
                    filling.filled_pairs().len(),
                    filling.held_open_pairs().len(),
                    rank,
                );
            }
            Err(refusal) => {
                println!("  {:<34} REFUSED: {refusal}", reading.criterion.name());
            }
        }
    }

    // The populations behind the numbers, not the numbers alone.
    section("the population behind each number, at the declaration aperture");
    for reading in readings {
        if reading.aperture_name != "by declaration" {
            continue;
        }
        let Ok(filling) = &reading.filling else {
            continue;
        };
        println!("\n  {}", reading.criterion.name());
        println!("    FILLED -- what this criterion founded:");
        names_capped(
            "      ",
            filling
                .filled_pairs()
                .into_iter()
                .map(|(statement, left, right)| format!("{left} = {right} |- {statement}")),
            8,
        );
        println!("    HELD OPEN -- what it refused, with the obstruction:");
        names_capped(
            "      ",
            filling.held_open().iter().map(|held| {
                let obstruction = match reading.criterion.direction() {
                    MeaningDirection::Consequent => held.consequent_disagreement.render(),
                    _ => held.disagreement.render(),
                };
                format!(
                    "{} vs {} [{}]",
                    held.left,
                    held.right,
                    clip(&obstruction, 180)
                )
            }),
            8,
        );
    }

    controls.declare(
        "5 betti-1 under each criterion, with the population behind each",
        ran > 0 && moved.len() > 1 && ranks_agree,
        format!(
            "{ran} readings returned invariants; betti-1 after filling took {} distinct values \
             {:?} across the declared criteria, and the spanning-forest rank agreed with the Smith \
             normal form on {}",
            moved.len(),
            moved,
            if ranks_agree {
                "every one"
            } else {
                "NOT every one"
            },
        ),
    );
}

// -------------------------------------------------------------------------------------------------
// Control 6
// -------------------------------------------------------------------------------------------------

fn control_six_the_four_apertures(
    deposit: &ElaborationDeposit,
    atoms: &[String],
    controls: &mut Controls,
) {
    rule_line("CONTROL 6 -- FOUR APERTURES, AND WHAT LIES OUTSIDE EACH");

    // A root rich in both directions, so all four apertures have material.
    let downward_root = deposit
        .route_keys()
        .iter()
        .find(|key| {
            deposit
                .elaborate(key, ElaborationAperture::Exhausted)
                .is_ok_and(|meaning| meaning.reach() >= 2)
        })
        .cloned()
        .unwrap_or_else(|| deposit.route_keys()[0].clone());
    let upward_root = atoms
        .iter()
        .find(|atom| {
            deposit
                .consequents(atom, ElaborationAperture::Exhausted)
                .is_ok_and(|closure| closure.reach() >= 2)
        })
        .cloned()
        .unwrap_or_else(|| atoms[0].clone());

    let mut outside: Vec<(&str, usize, String)> = Vec::new();

    section("aperture one -- the DEPOSIT, downward: a name it does not declare cannot be opened");
    let down = deposit
        .elaborate(&downward_root, ElaborationAperture::Exhausted)
        .expect("the root is in the deposit");
    println!(
        "  root {downward_root}, aperture Exhausted, reach {}",
        down.reach()
    );
    println!("  reached and permanently unopenable -- the environment's own vocabulary:");
    names("    ", down.atoms().iter().cloned());
    outside.push(("deposit / downward", down.atoms().len(), "atoms".to_owned()));

    section("aperture two -- a DECLARED DEPTH, downward");
    let bounded_down = deposit
        .elaborate(&downward_root, ElaborationAperture::ToDepth(BOUNDED_DEPTH))
        .expect("the root is in the deposit");
    println!(
        "  root {downward_root}, aperture ToDepth({BOUNDED_DEPTH}), reach {}",
        bounded_down.reach()
    );
    println!("  openable and not opened:");
    names("    ", bounded_down.beyond_depth().iter().cloned());
    println!("  what opening them would have brought and this reading does not carry:");
    names("    ", bounded_down.unopened().iter().cloned());
    outside.push((
        "depth / downward",
        bounded_down.unopened().len(),
        format!("unopened past depth {BOUNDED_DEPTH}"),
    ));

    section(
        "aperture three -- the DEPOSIT, upward: a statement is terminal and a summit has nothing above it",
    );
    let up = deposit
        .consequents(&upward_root, ElaborationAperture::Exhausted)
        .expect("the root is in the deposit");
    println!(
        "  root {upward_root}, aperture Exhausted, reach {}",
        up.reach()
    );
    println!(
        "  TERMINAL STATEMENTS -- nothing recruits a statement, so the walk stops here permanently:"
    );
    names(
        "    ",
        up.terminal_statements()
            .iter()
            .map(|statement| format!("`{statement}`")),
    );
    println!(
        "  SUMMITS -- declared names and atoms no artifact of this deposit recruits. Whether\n  \
         anything above them exists is exactly what the deposit does not say:"
    );
    names("    ", up.summits().iter().cloned());
    outside.push((
        "deposit / upward",
        up.terminal_statements().len() + up.summits().len(),
        "terminal statements and summits".to_owned(),
    ));

    section("aperture four -- a DECLARED DEPTH, upward");
    let bounded_up = deposit
        .consequents(&upward_root, ElaborationAperture::ToDepth(BOUNDED_DEPTH))
        .expect("the root is in the deposit");
    println!(
        "  root {upward_root}, aperture ToDepth({BOUNDED_DEPTH}), reach {}",
        bounded_up.reach()
    );
    println!("  reached and not opened:");
    names_capped("    ", bounded_up.beyond_depth().iter().cloned(), 12);
    println!("  what opening them would have brought and this reading does not carry:");
    names_capped("    ", bounded_up.unopened().iter().cloned(), 12);
    outside.push((
        "depth / upward",
        bounded_up.unopened().len(),
        format!("unopened past depth {BOUNDED_DEPTH}"),
    ));

    section("and one exclusion that is not an aperture but is declared with them");
    println!(
        "  The statement a pair is COMPARED AT is set aside as hypothesis, exactly as the two roots\n  \
         are. Two routes compared at `S` reach `S` by hypothesis, so counting it as a shared\n  \
         consequent would make consequent-crossing a check that cannot fail. What was set aside is\n  \
         returned on every comparison as `hypothesis` rather than dropped."
    );

    let holds = outside.iter().all(|(_, population, _)| *population > 0);
    controls.declare(
        "6 four apertures declared, with something named outside each",
        holds,
        outside
            .iter()
            .map(|(name, population, what)| format!("{name}: {population} {what}"))
            .collect::<Vec<_>>()
            .join("; "),
    );
}

// -------------------------------------------------------------------------------------------------
// The bound
// -------------------------------------------------------------------------------------------------

fn what_this_reading_does_not_show(deposit: &ElaborationDeposit, readings: &[Reading]) {
    rule_line("THE BOUND -- WHAT THIS READING DOES AND DOES NOT SHOW");

    let statements = deposit.statement_keys();
    println!(
        "\n  The deposit reaches {} distinct statements and declares {} names. Every consequent\n  \
         closure here terminates in that population, so the upward reading's discriminating power\n  \
         is bounded by the deposit's own STATEMENT count exactly as the downward reading's is\n  \
         bounded by its declaration count. Two atoms recruited by the same routes are\n  \
         indistinguishable upward, and the partition in control 2 is the measurement of how far\n  \
         that bites here.",
        statements.len(),
        deposit.declarations().len(),
    );

    // Where a crossing criterion fills everything it is vacuous AS A SEPARATOR, whatever it founds.
    section("vacuity, reported rather than tuned away");
    let mut reported = false;
    for reading in readings {
        let Ok(filling) = &reading.filling else {
            continue;
        };
        if filling.pairs_examined() == 0 {
            continue;
        }
        if filling.filled_pairs().is_empty() {
            println!("  {}: fills nothing", reading.label);
            reported = true;
        } else if filling.held_open_pairs().is_empty() {
            println!("  {}: fills everything", reading.label);
            reported = true;
        }
    }
    if !reported {
        println!("  none: every reading that ran separated the population.");
    }
    println!(
        "\n  A criterion that fills everything, or nothing, has not discriminated at this aperture.\n  \
         It is still a DIFFERENT FOUNDING from one that fills a proper subset, and both facts are\n  \
         printed. Nothing is loosened to make either come out otherwise."
    );
}
