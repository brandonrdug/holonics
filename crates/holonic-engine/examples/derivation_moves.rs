//! The moves a conditioned production made, realized, placed, and returned as classes.
//!
//! ```text
//! cargo run --release --example derivation_moves -- \
//!     standing/output \
//!     reference/pureholonics-seed/src/pureholonics
//! ```
//!
//! `conditioned_derivation_body` establishes that a body conditioned on this project's own prose
//! derives passages an unconditioned twin cannot, and reads that production back as a circuit. This
//! driver asks the next question of the same circuit: **which of the classes that production founded
//! did a move pay for, and which stay open with the obstruction retained?**
//!
//! A derivation move is a substitution — a fixed boundary and a changed interior — and the three
//! species are read off the production rather than declared as a fixture:
//!
//! ```text
//!   deposit               the frame  ->  the frame carrying one passage's own cells
//!   recruitment-exchange  one passage  ->  another with the same stem and standing declaration
//!   lemma-split           one passage  ->  the two that carry the SAME bridge elsewhere
//! ```
//!
//! The split is the one this leg exists for. The two passages it deposits recruit the same symbols
//! and reach the same statement; the only thing separating them is a declaration name, and a name is
//! not a receiver coordinate. Every cell it deposits therefore arrives with a twin, the move reaches
//! those classes as `2·c` and never as `c`, and the class comes back OPEN with the factor returned.
//! Supported rationally, unsupported integrally: the failure of the integral cycle-class statement,
//! which this project reads as torsion — winding that cannot be un-deposited.
//!
//! Discharge is named by `discharge_substitutions`. `placement::discharge` reports a realizer-side
//! aperture widening as the FOUND that pays, and this driver exhibits it doing so rather than
//! avoiding it silently.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    expose, found_conditioned_circuit, ConditionedBody, DerivationQuery, Exposure, PassageId,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::derivation_skein::{
    class_of, conduct_aperture, declare_receivers, declared_contexts, deposit_moves,
    exchange_moves, moves_the_production_made, passage_interior, passages_under, place_moves,
    split_moves, DerivationMove, MoveAperture, MoveObstruction, MoveSpecies, OpenClass, PlacedMoves,
    SupportedClass,
};
use holonic_engine::placement::{discharge, Discharge};
use holonic_engine::rebase_invariants::{smith_normal_form, IntegerMatrix, PivotRule};
use holonic_engine::receiver_exact_compression::ReceiverId;
use holonic_engine::skein::read_substitution;
use holonic_engine::substitution_realizers::{
    discharge_substitutions, RealizerAdmission, SubstitutionDischarge,
};
use holonic_engine::supported_realizers::{incidence, positive_form, quadratic_value};

use num_bigint::BigInt;
use num_traits::Zero;

/// The stem length at which a licence stops being a residual letter and becomes a morpheme. The
/// declared aperture on the production, and the only number this driver chooses.
const MORPHEMIC: usize = 4;

// -------------------------------------------------------------------------------------------------
// material
// -------------------------------------------------------------------------------------------------

fn material(root: &Path, extension: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(material(&path, extension));
        } else if path.extension().is_some_and(|carried| carried == extension) {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> Vec<(String, String)> {
    material(root, "lean")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect()
}

fn read_corpus(root: &Path) -> Vec<Exposure> {
    material(root, "md")
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| expose(&path.display().to_string(), &text))
        })
        .collect()
}

// -------------------------------------------------------------------------------------------------
// printing
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(94));
    println!("{title}");
    println!("{}", "=".repeat(94));
}

/// A population, printed whole and wrapped. Names, never a count.
fn names(indent: &str, entries: &[String]) {
    if entries.is_empty() {
        println!("{indent}(none)");
        return;
    }
    let mut line = String::new();
    for entry in entries {
        if !line.is_empty() && line.len() + entry.len() + 2 > 88 {
            println!("{indent}{line}");
            line.clear();
        }
        if !line.is_empty() {
            line.push_str("  ");
        }
        line.push_str(entry);
    }
    if !line.is_empty() {
        println!("{indent}{line}");
    }
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
            "  [{}] {name}\n        {saying}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

fn move_line(declared: &DerivationMove, position: usize) -> String {
    format!(
        "    [{position:>3}] {:<20} stem {:<8} {} -> {}",
        declared.species.name(),
        format!("{:?}", declared.stem),
        if declared.withdraws.is_empty() {
            "(the frame)".to_owned()
        } else {
            declared.withdraws.join(" ")
        },
        declared.deposits.join(" ")
    )
}

fn exhibit_supported(class: &SupportedClass) {
    println!("\n    class {}  SUPPORTED", class.reading.class);
    println!("      cells");
    names("        ", &class.reading.cells);
    println!("      paid for by");
    for naming in &class.paid_by {
        println!(
            "        [{:>3}] {:<20} stem {:<8} deposits {}",
            naming.declared,
            naming.species.name(),
            format!("{:?}", naming.stem),
            naming.deposits.join(" ")
        );
    }
    println!("      founded by the passages");
    names(
        "        ",
        &class
            .reading
            .passages
            .iter()
            .map(|passage| {
                if passage.derived {
                    format!("{}*", passage.name)
                } else {
                    passage.name.clone()
                }
            })
            .collect::<Vec<String>>(),
    );
}

fn exhibit_open(class: &OpenClass) {
    match &class.obstruction {
        MoveObstruction::ReachedOnlyInMultiple { factor, reached_by } => {
            println!(
                "\n    class {}  OPEN -- reached only as {factor}·c, supported rationally and not \
                 integrally",
                class.reading.class
            );
            println!("      cells");
            names("        ", &class.reading.cells);
            println!("      reached, in multiple, by");
            for naming in reached_by {
                println!(
                    "        [{:>3}] {:<20} stem {:<8} deposits {}",
                    naming.declared,
                    naming.species.name(),
                    format!("{:?}", naming.stem),
                    naming.deposits.join(" ")
                );
            }
        }
        MoveObstruction::NoMoveReached => {
            println!(
                "\n    class {}  OPEN -- no declared move deposited into it",
                class.reading.class
            );
            println!("      cells");
            names("        ", &class.reading.cells);
        }
    }
    println!("      founded by the passages");
    names(
        "        ",
        &class
            .reading
            .passages
            .iter()
            .map(|passage| {
                if passage.derived {
                    format!("{}*", passage.name)
                } else {
                    passage.name.clone()
                }
            })
            .collect::<Vec<String>>(),
    );
}

fn tally(moves: &[DerivationMove]) -> BTreeMap<&'static str, usize> {
    let mut counted: BTreeMap<&'static str, usize> = BTreeMap::new();
    for declared in moves {
        *counted.entry(declared.species.name()).or_default() += 1;
    }
    counted
}

/// `|M x|^2`, summed directly. The independent route the positive form has to agree with.
fn squared_norm(matrix: &IntegerMatrix, probe: &[BigInt]) -> BigInt {
    let mut total = BigInt::zero();
    for row in 0..matrix.rows() {
        let mut entry = BigInt::zero();
        for column in 0..matrix.columns() {
            entry += matrix.at(row, column) * &probe[column];
        }
        total += &entry * &entry;
    }
    total
}

/// The positive form on the declared moves, checked against an incidence rebuilt here from
/// `Substitution::added()`. Returns the number of probes on which the value was not zero, so a
/// reading that agreed everywhere by being zero everywhere cannot pass as agreement.
fn positive_form_agrees(placed: &PlacedMoves) -> (bool, usize) {
    let placement = &placed.placed.placement;
    let extent = placement.class_extent;
    let realizations = placed
        .realizers
        .realizations_under(RealizerAdmission::EveryRead, &placement.compression.conduct);
    let form = positive_form(&incidence(&realizations, extent));

    let mut theirs = IntegerMatrix::zeros(placed.moves.len(), extent);
    for (row, declared) in placed.moves.iter().enumerate() {
        for cell in declared.substitution.added() {
            let Some(class) = class_of(placement, cell) else {
                continue;
            };
            let carried = theirs.at(row, class) + BigInt::from(1);
            theirs.set(row, class, carried);
        }
    }

    let mut probes: Vec<Vec<BigInt>> = vec![
        (0..extent).map(|_| BigInt::from(1)).collect(),
        (0..extent)
            .map(|index| {
                let magnitude = (index as i64) + 2;
                BigInt::from(if index % 2 == 0 { magnitude } else { -magnitude })
            })
            .collect(),
    ];
    for class in 0..extent {
        let mut probe = vec![BigInt::zero(); extent];
        probe[class] = BigInt::from(1);
        probes.push(probe);
    }

    let mut agrees = true;
    let mut nonzero = 0usize;
    for probe in &probes {
        let value = quadratic_value(&form, probe);
        if value != squared_norm(&theirs, probe) {
            agrees = false;
        }
        if !value.is_zero() {
            nonzero += 1;
        }
    }
    (agrees, nonzero)
}

fn rank_of(placed: &PlacedMoves, admission: RealizerAdmission) -> usize {
    let placement = &placed.placed.placement;
    smith_normal_form(
        &incidence(
            &placed
                .realizers
                .realizations_under(admission, &placement.compression.conduct),
            placement.class_extent,
        ),
        PivotRule::SmallestMagnitude,
    )
    .rank()
}

// -------------------------------------------------------------------------------------------------

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let deposit_root = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );
    let corpus_root = PathBuf::from(
        arguments
            .get(1)
            .cloned()
            .unwrap_or_else(|| "reference/pureholonics-seed/src/pureholonics".to_owned()),
    );

    let deposit = read_deposit(&deposit_root);
    let corpus = read_corpus(&corpus_root);
    if deposit.is_empty() || corpus.is_empty() {
        eprintln!(
            "material missing: deposit {} artifacts, corpus {} wholes",
            deposit.len(),
            corpus.len()
        );
        std::process::exit(2);
    }

    let mut controls = Controls::new();

    let mut body = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    body.condition(&corpus);

    // The query the deposit's own production reaches most often — the one route population large
    // enough for a bridge group to have three members.
    let statements = body.standing_statements();
    let query = statements
        .iter()
        .max_by_key(|statement| {
            body.derive(&DerivationQuery::reaching(statement))
                .map_or(0, |derived| derived.len())
        })
        .cloned()
        .expect("the deposit reached a statement");
    let the_query = DerivationQuery::reaching(&query);

    let whole = body.passages(&the_query).expect("the production reads back");
    let aperture = MoveAperture::morphemic(&whole, MORPHEMIC);
    let restricted = passages_under(&whole, &aperture);
    let circuit = match found_conditioned_circuit(restricted, CircuitAperture::STATEMENT_INCIDENT) {
        Ok(circuit) => circuit,
        Err(refusal) => {
            eprintln!("the circuit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let system = match declare_receivers(&circuit) {
        Ok(system) => system,
        Err(refusal) => {
            eprintln!("the receiver family was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let contexts = declared_contexts(&circuit, &query);

    // ---------------------------------------------------------------------------------------------
    rule("DERIVATION MOVES -- the production's own substitutions, realized and placed");

    println!("\nmaterial");
    println!(
        "  mathematical   {:<52} {} artifacts",
        deposit_root.display(),
        deposit.len()
    );
    println!(
        "  linguistic     {:<52} {} wholes",
        corpus_root.display(),
        corpus.len()
    );
    println!("\n  the query          {query}");
    println!(
        "\n  the declared aperture on the production: the bridges of {MORPHEMIC} characters or more"
    );
    println!("  a shorter licence is a residual letter and is a different kind of object.");
    print!("    licensing stems admitted   ");
    names("", &aperture.stems.iter().cloned().collect::<Vec<String>>());

    let derived_whole = whole.iter().filter(|p| p.is_derived()).count();
    let derived_here = circuit.passages.iter().filter(|p| p.is_derived()).count();
    println!(
        "\n    passages          whole production {derived_whole} derived + {} deposited",
        whole.len() - derived_whole
    );
    println!(
        "                      under the aperture {derived_here} derived + {} deposited",
        circuit.passages.len() - derived_here
    );
    println!("    circuit cells     {}", circuit.cell_names().len());

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE DECLARED APERTURES -- the receiver family and the conduct steps");

    println!(
        "\n  {} receivers, one dilated section per 0-cell the production recruits, plus the",
        system.receivers.len()
    );
    println!("  statement vertex. Each reads the METRIC address -- the invariant, never the walk order.\n");
    let complex = circuit.circuit.complex();
    for (index, section) in system.receivers.iter().enumerate() {
        let focus = complex
            .cell(section.lineage.focus)
            .map(|cell| cell.name.clone())
            .unwrap_or_default();
        println!("    receiver {index:<3} focused at {focus}");
    }

    // Two receivers that address every cell alike are one frame wearing two names. Exhibit a cell
    // they disagree about rather than asserting they differ.
    let first = system.addresses(ReceiverId(0));
    let mut disagreement: Option<(usize, String, u64, u64)> = None;
    for index in 1..system.receivers.len() {
        let other = system.addresses(ReceiverId(index as u64));
        if let Some((cell, here, there)) = first
            .iter()
            .zip(&other)
            .find(|((_, here), (_, there))| here != there)
            .map(|((cell, here), (_, there))| (*cell, here.0, there.0))
        {
            disagreement = Some((
                index,
                complex
                    .cell(cell)
                    .map(|body| body.name.clone())
                    .unwrap_or_default(),
                here,
                there,
            ));
            break;
        }
    }
    match &disagreement {
        Some((index, cell, here, there)) => println!(
            "\n    receivers 0 and {index} disagree: they address {cell} at {here} and {there}"
        ),
        None => println!("\n    every declared receiver addresses every cell alike"),
    }

    let admitted = conduct_aperture(&circuit);
    println!(
        "\n  {} conduct steps, all of them 1-cells the DEPOSIT founded. The production's own edges",
        admitted.len()
    );
    println!("  are the material being placed and are not admitted as steps that place it.");
    let production_edges: BTreeSet<_> = circuit
        .passages
        .iter()
        .filter(|passage| passage.is_derived())
        .flat_map(|passage| passage_interior(&circuit, passage))
        .collect();
    let leaked = admitted
        .iter()
        .filter(|cell| production_edges.contains(cell))
        .count();
    println!("    cells the production founded and the aperture admits: {leaked}");

    println!("\n  {} declared contexts, each a closed subcomplex:", contexts.len());
    for (index, context) in contexts.iter().enumerate() {
        println!("    context {index}  {} cells", context.len());
    }

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE MOVES -- read off the production, not declared as a fixture");

    let splits = split_moves(&circuit);
    let deposits = deposit_moves(&circuit);
    let exchanges = exchange_moves(&circuit);
    let every_move = moves_the_production_made(&circuit);
    println!("\n  by species: {:?}", tally(&every_move));

    println!("\n  every lemma split -- one passage replaced by the two carrying its bridge elsewhere");
    for (position, declared) in splits.iter().enumerate() {
        println!("{}", move_line(declared, position));
    }
    println!("\n  every recruitment exchange -- one brought identifier replaced by another");
    for (position, declared) in exchanges.iter().enumerate() {
        println!("{}", move_line(declared, splits.len() + deposits.len() + position));
    }
    println!("\n  every deposit -- the frame carrying one passage's own cells");
    for (position, declared) in deposits.iter().enumerate() {
        println!("{}", move_line(declared, splits.len() + position));
    }

    // Every move must be a substitution `skein` accepts, and none of them trivial.
    let refused: Vec<String> = every_move
        .iter()
        .filter(|declared| {
            read_substitution(complex, &declared.substitution, &contexts, PivotRule::SmallestMagnitude)
                .is_err()
        })
        .map(|declared| declared.deposits.join(" "))
        .collect();
    let trivial = every_move
        .iter()
        .filter(|declared| declared.substitution.is_trivial())
        .count();
    println!("\n  moves refused by `read_substitution`: {refused:?}");
    println!("  moves that change nothing:            {trivial}");

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE SPLIT FAMILY ALONE -- where the integral obstruction lives");

    let split_only = place_moves(
        &circuit,
        &system,
        &splits,
        &contexts,
        RealizerAdmission::EveryRead,
        PivotRule::SmallestMagnitude,
    );
    println!(
        "\n  {} classes the receivers distinguish; {} stand, {} open.",
        split_only.placed.placement.class_extent,
        split_only.supported.len(),
        split_only.open.len()
    );
    println!(
        "  invariant factors above one: {:?}",
        split_only.torsion()
    );

    let doubled = split_only.reached_only_in_multiple();
    println!(
        "\n  the classes reached ONLY IN MULTIPLE -- supported over the rationals, unsupported over"
    );
    println!("  the integers. This is the return; it is exhibited whole.");
    for class in &doubled {
        exhibit_open(class);
    }
    if doubled.is_empty() {
        println!("\n    (none -- the split's twins are being separated by the receiver family)");
    }

    println!("\n  the classes the split family DID pay for, integrally:");
    for class in &split_only.supported {
        exhibit_supported(class);
    }
    if split_only.supported.is_empty() {
        println!("\n    (none)");
    }

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE DISSOLUTION -- declaring one member's deposit reaches the class singly");

    let mut split_and_deposit = splits.clone();
    split_and_deposit.extend(deposits.clone());
    let dissolved = place_moves(
        &circuit,
        &system,
        &split_and_deposit,
        &contexts,
        RealizerAdmission::EveryRead,
        PivotRule::SmallestMagnitude,
    );
    println!(
        "\n    {:<34} {:>14} {:>18}",
        "", "splits alone", "splits + deposits"
    );
    println!(
        "    {:<34} {:>14} {:>18}",
        "declared moves",
        splits.len(),
        split_and_deposit.len()
    );
    println!(
        "    {:<34} {:>14} {:>18}",
        "standing classes",
        split_only.supported.len(),
        dissolved.supported.len()
    );
    println!(
        "    {:<34} {:>14} {:>18}",
        "open classes",
        split_only.open.len(),
        dissolved.open.len()
    );
    println!(
        "    {:<34} {:>14} {:>18}",
        "reached only in multiple",
        split_only.reached_only_in_multiple().len(),
        dissolved.reached_only_in_multiple().len()
    );
    let factors = |placed: &PlacedMoves| {
        let carried = placed.torsion();
        if carried.is_empty() {
            "(none)".to_owned()
        } else {
            carried
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<String>>()
                .join(" ")
        }
    };
    println!(
        "    {:<34} {:>14} {:>18}",
        "invariant factors above one",
        factors(&split_only),
        factors(&dissolved)
    );
    let founding = discharge_substitutions(&split_only.placed, &dissolved.placed);
    println!("\n    discharge_substitutions          {founding:?}");
    println!(
        "    placement::discharge             {:?}",
        discharge(&split_only.placed.placement, &dissolved.placed.placement)
    );

    println!("\n  the classes the dissolution moved from OPEN to SUPPORTED, with what paid:");
    let was_open: BTreeSet<usize> = doubled.iter().map(|class| class.reading.class).collect();
    for class in dissolved
        .supported
        .iter()
        .filter(|class| was_open.contains(&class.reading.class))
    {
        exhibit_supported(class);
    }

    // ---------------------------------------------------------------------------------------------
    rule("[5]  FOUNDING AND WIDENING -- the same family, two apertures");

    let narrow = place_moves(
        &circuit,
        &system,
        &every_move,
        &contexts,
        RealizerAdmission::Invisible,
        PivotRule::SmallestMagnitude,
    );
    let wide = place_moves(
        &circuit,
        &system,
        &every_move,
        &contexts,
        RealizerAdmission::EveryRead,
        PivotRule::SmallestMagnitude,
    );
    println!(
        "\n  one declared family of {} moves, read at two realizer apertures.",
        every_move.len()
    );
    println!(
        "    Invisible admits {} moves -- the ones no declared context can see",
        narrow.placed.admitted.len()
    );
    println!(
        "    EveryRead admits {} moves",
        wide.placed.admitted.len()
    );
    println!(
        "    open classes            {} -> {}",
        narrow.placed.placement.open.len(),
        wide.placed.placement.open.len()
    );
    let widening = discharge_substitutions(&narrow.placed, &wide.placed);
    let miscalled = discharge(&narrow.placed.placement, &wide.placed.placement);
    println!("\n    discharge_substitutions  {widening:?}");
    println!("    placement::discharge     {miscalled:?}   <- the convicted reading");

    println!("\n  the moves the invisible aperture admits -- real substitutions no declared context");
    println!("  can tell apart, which is what a compression is here:");
    for realizer in &narrow.placed.admitted {
        let position = realizer.0 as usize;
        if let Some(declared) = every_move.get(position) {
            println!("{}", move_line(declared, position));
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE WHOLE FAMILY PLACED -- every class, named");

    println!(
        "\n  {} classes; {} stand, {} open ({} unreached, {} reached only in multiple).",
        wide.placed.placement.class_extent,
        wide.supported.len(),
        wide.open.len(),
        wide.unreached().len(),
        wide.reached_only_in_multiple().len()
    );
    println!(
        "  free obstruction {}   supported rank {}   invariant factors above one {}",
        wide.placed.placement.support.free_obstruction(),
        wide.placed.placement.support.supported_rank,
        if wide.torsion().is_empty() {
            "(none)".to_owned()
        } else {
            wide.torsion()
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<String>>()
                .join(" ")
        }
    );
    println!(
        "  the free obstruction is `class_extent - rank`, a rank deficiency, and is NOT the size of"
    );
    println!(
        "  the unreached population above it: many moves land identically, so the {} rows span a",
        every_move.len()
    );
    println!("  space of dimension {}.", wide.placed.placement.support.supported_rank);
    println!("\n  a passage name marked * was derived by the conditioned body.");

    println!("\n  SUPPORTED");
    for class in &wide.supported {
        exhibit_supported(class);
    }
    println!("\n  OPEN");
    for class in &wide.open {
        exhibit_open(class);
    }

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    let restricted_properly = circuit.passages.len() < whole.len() && derived_here > 0;
    let ids_name_positions = circuit
        .passages
        .iter()
        .enumerate()
        .all(|(position, passage)| passage.id == PassageId(position as u64));
    controls.check(
        "the declared aperture restricts the production and the ids name their own positions",
        restricted_properly && ids_name_positions,
        "a filtered population whose ids named their old positions would attribute every cell to \
         the wrong passage",
    );
    controls.check(
        "every cell of the circuit traces back to a passage",
        circuit.provenance_is_total(),
        "a class whose cells no passage names cannot be reported by the passages it is made of",
    );
    controls.check(
        "the receiver family is plural and its members disagree on a named cell",
        system.receivers.len() >= 2 && disagreement.is_some(),
        "two receivers that address every cell alike are one frame wearing two names",
    );
    controls.check(
        "the conduct aperture admits no cell the production founded",
        leaked == 0,
        "admitting them would let the material under test carry the ruler that measures it",
    );
    controls.check(
        "every move the production made is read without refusal, and none is trivial",
        refused.is_empty() && trivial == 0 && !every_move.is_empty(),
        "a refusal is retained silently, and a move that changes nothing cannot be invariant",
    );

    // What a move deposits is `passage_interior`, and the circuit already knows independently which
    // cells belong to one passage alone. The two must agree, or every move is built short of what
    // the passage founded and the class it never reaches merely looks unreached.
    let mut alone: BTreeMap<String, BTreeSet<_>> = BTreeMap::new();
    for cell in complex.cells().values() {
        if let [only] = circuit.passages_founding(cell.id).as_slice() {
            alone
                .entry(only.derivation.name.clone())
                .or_default()
                .insert(cell.id);
        }
    }
    let interiors_agree = circuit
        .passages
        .iter()
        .filter(|passage| passage.is_derived())
        .all(|passage| {
            passage_interior(&circuit, passage)
                == alone
                    .get(&passage.derivation.name)
                    .cloned()
                    .unwrap_or_default()
        });
    controls.check(
        "what a move deposits agrees with the circuit's own provenance, passage by passage",
        interiors_agree && derived_here > 0,
        "two frames on one quantity; a move built short of a passage's cells leaves a class \
         looking unreached rather than unbuilt",
    );

    // Which move a class names, and not merely that it names one. The declared position must have
    // deposited into the class, and the payload must be the move at that position.
    let mut namings_checked = 0usize;
    let mut naming_positions: BTreeSet<usize> = BTreeSet::new();
    let mut namings_true = true;
    {
        let placement = &wide.placed.placement;
        let mut verify = |naming: &holonic_engine::derivation_skein::MoveNaming, class: usize| {
            let Some(declared) = every_move.get(naming.declared) else {
                namings_true = false;
                return;
            };
            let landed: BTreeSet<usize> = declared
                .substitution
                .added()
                .into_iter()
                .filter_map(|cell| class_of(placement, cell))
                .collect();
            if !landed.contains(&class)
                || naming.species != declared.species
                || naming.stem != declared.stem
                || naming.deposits != declared.deposits
                || naming.withdraws != declared.withdraws
            {
                namings_true = false;
            }
            namings_checked += 1;
            naming_positions.insert(naming.declared);
        };
        for class in &wide.supported {
            for naming in &class.paid_by {
                verify(naming, class.reading.class);
            }
        }
        for class in &wide.open {
            if let MoveObstruction::ReachedOnlyInMultiple { reached_by, .. } = &class.obstruction {
                for naming in reached_by {
                    verify(naming, class.reading.class);
                }
            }
        }
    }
    controls.check(
        "every move a class names is the move at that declared position, and it reached that class",
        namings_true && namings_checked > 0 && naming_positions.len() >= 3,
        "a reading that returns the right position with another move's payload points every class \
         at the wrong substitution, and non-emptiness alone is satisfied by doing so",
    );

    let contexts_disagree = split_and_deposit.iter().any(|declared| {
        read_substitution(complex, &declared.substitution, &contexts, PivotRule::SmallestMagnitude)
            .map(|reading| {
                reading
                    .verdicts
                    .windows(2)
                    .any(|pair| pair[0].remainder != pair[1].remainder)
            })
            .unwrap_or(false)
    });
    controls.check(
        "two declared contexts return different remainders for the same move",
        contexts_disagree,
        "a family whose members agree about every move is one context counted three times",
    );

    let factors_above_one = doubled.iter().all(|class| match &class.obstruction {
        MoveObstruction::ReachedOnlyInMultiple { factor, reached_by } => {
            *factor > BigInt::from(1)
                && !reached_by.is_empty()
                && reached_by
                    .iter()
                    .all(|naming| naming.species == MoveSpecies::LemmaSplit)
        }
        MoveObstruction::NoMoveReached => false,
    });
    controls.check(
        "the split family alone leaves classes reached only in multiple, with the factor returned",
        !doubled.is_empty() && factors_above_one && !split_only.torsion().is_empty(),
        "the integral cycle-class failure: supported over the rationals, unsupported over the \
         integers, and the winding named rather than the fact of it",
    );
    controls.check(
        "every class reached only in multiple holds a cell the production founded",
        doubled.iter().all(|class| class.reading.holds_derived()),
        "an obstruction on the deposit's own cells would be a reading of the terrain",
    );
    controls.check(
        "declaring one member's deposit dissolves it, and the discharge is named a founding",
        dissolved.reached_only_in_multiple().is_empty()
            && dissolved.torsion().is_empty()
            && dissolved.supported.len() > split_only.supported.len()
            && founding == SubstitutionDischarge::Founded,
        "reaching the class singly must remove the factor rather than add to it, or the multiple \
         is an artifact of the reduction",
    );
    controls.check(
        "relaxing the filter over one fixed family is a widening and never a founding",
        !narrow.placed.admitted.is_empty()
            && narrow.placed.admitted.len() < wide.placed.admitted.len()
            && narrow.placed.declared == wide.placed.declared
            && widening == SubstitutionDischarge::Widened,
        "and the material can vary it: the invisible aperture admits a proper, non-empty subset",
    );
    controls.check(
        "placement::discharge alone reads that widening as production",
        miscalled == Discharge::Founded,
        "the defect is exhibited rather than avoided; this is why the realizer-side aperture is in \
         the return",
    );
    controls.check(
        "a class no declared move reaches stays OPEN and names the passages it is made of",
        !wide.unreached().is_empty()
            && wide
                .unreached()
                .iter()
                .all(|class| !class.reading.passages.is_empty()),
        "the free obstruction, exhibited at named classes rather than counted",
    );
    controls.check(
        "a class the production founded stands, and names the move and the passage that paid",
        !wide.supported_from_production().is_empty()
            && wide.supported_from_production().iter().all(|class| {
                !class.paid_by.is_empty()
                    && class
                        .reading
                        .passages
                        .iter()
                        .any(|passage| passage.derived && passage.stem.is_some())
            }),
        "the conditioning's own production paid for a class, and the payment is traceable to the \
         stem that licensed it",
    );

    let (agrees, nonzero) = positive_form_agrees(&wide);
    controls.check(
        "the positive form agrees with an incidence rebuilt from the moves, and is not zero",
        agrees && nonzero >= 3,
        "two frames on one quantity; a form that is zero everywhere agrees with anything",
    );

    let narrow_rank = rank_of(&narrow, RealizerAdmission::Invisible);
    let wide_rank = rank_of(&wide, RealizerAdmission::EveryRead);
    controls.check(
        "the incidence has the rank placement computed, at two apertures whose ranks differ",
        narrow_rank == narrow.placed.placement.support.supported_rank
            && wide_rank == wide.placed.placement.support.supported_rank
            && narrow_rank != wide_rank,
        "a fixture where the two ranks agreed would let a constant pass as agreement",
    );

    let expected_species: BTreeSet<&str> = ["deposit", "lemma-split", "recruitment-exchange"]
        .into_iter()
        .collect();
    controls.check(
        "all three move species are present in the production",
        tally(&every_move).keys().copied().collect::<BTreeSet<_>>() == expected_species,
        "a species with no member is a law present in the code and absent from the evidence",
    );

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
