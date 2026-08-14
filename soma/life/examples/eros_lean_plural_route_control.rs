//! Driver: the declared control for the derivation atlas, and the loop from production back to it.
//!
//! ## Why this driver exists
//!
//! `crates/holonic-engine/examples/derivation_atlas_reader.rs` reads the machine's deposited proof
//! artifacts as a circuit and returns `betti` and `torsion`. Run on
//! `standing/output/lean-proof-production/` — thirty-one artifacts — it returns **`betti` at grade
//! one = 0**. `CLAUDE.md` §8: *a law that returns zero proves nothing about itself.* Closing a
//! production/analysis loop on that signal would close it on a quantity that has never fired, so
//! the first obligation is a **declared control that makes the reading provably nonzero**, and only
//! then the loop.
//!
//! The reason the thirty-one return zero is structural: the reader founds **one 0-cell per declared
//! theorem name**, all thirty-one artifacts declare `carrier_transport`, so they are one vertex and
//! the recruitment graph is a star. Thirty-one routes to one result cannot be counted by an
//! invariant that cannot see them as thirty-one things.
//!
//! ## The frame, and why this driver can be run twice
//!
//! **The reading BEFORE is taken from the standing with this driver's own deposit directory
//! excluded.** It used to be taken from the whole of `standing/output`, and once this driver's
//! sixty artifacts were deposited there, `after = before ∪ control = before`: four declared
//! controls failed on a clean re-run and the driver exited 1. A loop that can be traversed exactly
//! once, and only from a state that no longer exists, is not a loop. The excluded path is named
//! once, in [`DEPOSIT_NAME`], and a declared control holds the BEFORE population to it.
//!
//! ## The target comes from the reading
//!
//! `DerivationCircuit::single_vertex_statements_by_lineage` returns the statements **no second
//! declaration has ever reached**, ordered by the size of the artifact lineage behind each. The
//! first entry is this driver's target and the rest are printed beside it. Ordering by lineage is
//! the reading's own judgement twice over: a statement no second declaration reached is the one
//! worth cross-checking, and the size of its lineage is the machine's own evidence that a path to
//! it exists. The theorem headers below are then **built from the selected statement text**, so the
//! thing submitted to the kernel is the thing the analysis named.
//!
//! Until 2026-08-08 the target was the string literal
//! `"(P : Prop) (h : P) : exactCarrier P"` and the reading was asked only whether that constant was
//! in its own single-vertex population. Nothing selected.
//!
//! ## What this driver produces
//!
//! The selected statement, posed under **two declaration names**, in two environments that differ:
//!
//! ```text
//!   carrier_transport_direct    import KernelWitness; namespace Soma
//!   carrier_transport_relayed   import KernelWitness; namespace Soma; abbrev ExactRelay ...
//! ```
//!
//! The relayed environment mounts a carrier the direct one does not, so the two reach one statement
//! by recruitment populations that share and are not equal.
//!
//! Every generated path is submitted to a real exterior Lean kernel and **every path is deposited,
//! admitted or refused**. A reader ingesting only acceptances would be success-filtering wearing
//! analysis's name.
//!
//! ## The loop, and its falsifiers
//!
//! ```text
//!   read the standing MINUS this deposit -> the reading BEFORE
//!   the target comes FROM it             -> ranked single-vertex statements, first entry
//!   produce, grade, deposit
//!   read BEFORE + this run's output      -> the reading AFTER
//!   invariant_movement, route_movement   -> the populations that moved
//! ```
//!
//! - The movement population and `rebase_invariants::invariants_agree` must return one verdict.
//! - Smith normal form and a union-find spanning forest must return one pair of Betti numbers.
//! - The homological route excess and the lineage route excess must agree, and must **move**.
//! - The statement the reading selected must be reached by one declaration before and by more than
//!   one after. That is the loop closing, and it is the thing a decorative loop cannot do.
//! - The deposited artifacts of one declaration must carry more than one recruitment population, or
//!   the reading is a function of this file's preamble strings rather than of the production.
//!
//! Run (needs `lean` and `lake` on PATH):
//!
//! ```text
//! cargo run -p life --example eros_lean_plural_route_control
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
};

use holonic_engine::derivation_atlas::{
    found_circuit, invariant_movement, read_derivation, route_cycle_agreement, route_movement,
    CircuitAperture, Derivation, DerivationCircuit, DerivationIdentity, MovedField,
};
use holonic_engine::rebase_invariants::{invariants_agree, PivotRule, RebaseInvariants};
use life::lean_mathematics::{
    collect_lean_documents,
    kernel_returns::{LeanKernelOutcome, LeanKernelReturnFamily},
    LeanKernelWorld, LeanMathematicsEcology, LeanProofProblem,
};

/// This driver's own deposit directory, under `output/` while it runs and under `standing/output/`
/// once deposited. **The reading BEFORE excludes it**, which is what makes the loop traversable
/// more than once.
const DEPOSIT_NAME: &str = "lean-plural-route-control";

fn repository_root() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    root.canonicalize().unwrap_or(root)
}

/// Every `.lean` artifact under `root`, in a stable filename order, recursively.
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

fn read_population(paths: &[PathBuf]) -> Vec<Derivation> {
    paths
        .iter()
        .filter_map(|path| read_derivation(&std::fs::read_to_string(path).ok()?))
        .collect()
}

fn betti_at(invariants: &RebaseInvariants, grade: u32) -> usize {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map_or(0, |carried| carried.betti)
}

fn reading(derivations: &[Derivation]) -> RebaseInvariants {
    found_circuit(derivations, CircuitAperture::DEPOSITED_READER)
        .expect("the deposited reader's aperture is admissible")
        .invariants(PivotRule::SmallestMagnitude)
        .expect("the atlas reads")
}

fn forest_agrees(circuit: &DerivationCircuit) -> bool {
    let reading = circuit
        .invariants(PivotRule::SmallestMagnitude)
        .expect("the atlas reads");
    let forest = circuit.spanning_forest_reading();
    forest.betti_0() == betti_at(&reading, 0) && forest.betti_1() == betti_at(&reading, 1)
}

/// The distinct recruitment populations the deposit carries per declaration. More than one for some
/// declaration is the evidence that the reading depends on the proof bodies the machine composed
/// and not on this file's two preamble strings.
fn recruitment_classes(population: &[Derivation]) -> BTreeMap<&str, BTreeSet<Vec<(String, u32)>>> {
    let mut classes: BTreeMap<&str, BTreeSet<Vec<(String, u32)>>> = BTreeMap::new();
    for derivation in population {
        classes.entry(derivation.name.as_str()).or_default().insert(
            derivation
                .recruited
                .iter()
                .map(|(symbol, count)| (symbol.clone(), *count))
                .collect(),
        );
    }
    classes
}

/// The selected statement, posed directly. Its environment is the kernel witness alone.
fn direct_problem(statement: &str) -> LeanProofProblem {
    LeanProofProblem {
        identity: "carrier-transport-direct".to_owned(),
        source_scope: BTreeSet::from(["KernelWitness.lean".to_owned()]),
        prefix: "import KernelWitness\nnamespace Soma".to_owned(),
        theorem_header: format!("theorem carrier_transport_direct {statement}"),
        suffix: "end Soma".to_owned(),
    }
}

/// The SAME selected statement under a second declaration name, in an environment that additionally
/// mounts a relay carrier. The statement is identical after normalization; the recruitment is not.
fn relayed_problem(statement: &str) -> LeanProofProblem {
    LeanProofProblem {
        identity: "carrier-transport-relayed".to_owned(),
        source_scope: BTreeSet::from(["KernelWitness.lean".to_owned()]),
        prefix:
            "import KernelWitness\nnamespace Soma\nabbrev ExactRelay (Q : Prop) : Prop := exactCarrier Q"
                .to_owned(),
        theorem_header: format!("theorem carrier_transport_relayed {statement}"),
        suffix: "end Soma".to_owned(),
    }
}

fn build_kernel_project(project_root: &Path) -> bool {
    let output = Command::new("lake")
        .arg("build")
        .current_dir(project_root)
        .output()
        .expect("`lake` is on PATH");
    if !output.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&output.stderr));
    }
    output.status.success()
}

struct Failures(Vec<String>);

impl Failures {
    fn require(&mut self, held: bool, claim: &str) {
        println!("    [{}] {claim}", if held { "holds" } else { "FAILS" });
        if !held {
            self.0.push(claim.to_owned());
        }
    }
}

fn main() {
    let mut failures = Failures(Vec::new());
    let root = repository_root();
    let corpus_root = root.join("soma/formal");
    let project_root = root.join("soma/formal/kernel-witness");
    let standing_root = root.join("standing/output");
    let standing_deposit = standing_root.join(DEPOSIT_NAME);
    let scratch_root = root.join("output").join(DEPOSIT_NAME);

    // ------------------------------------------------------ the reading BEFORE, and the target
    println!("=== the reading BEFORE this production");
    let every_standing_path = artifact_paths(&standing_root);
    let standing_paths: Vec<PathBuf> = every_standing_path
        .iter()
        .filter(|path| !path.starts_with(&standing_deposit))
        .cloned()
        .collect();
    let excluded = every_standing_path.len() - standing_paths.len();
    println!(
        "    the standing carries {} artifacts; {excluded} of them are this driver's own prior\n\
         \x20   deposit under {DEPOSIT_NAME}/ and are EXCLUDED, so BEFORE is a state this run\n\
         \x20   cannot destroy and this driver can be run again",
        every_standing_path.len()
    );
    let standing_population = read_population(&standing_paths);
    let before_circuit = found_circuit(&standing_population, CircuitAperture::DEPOSITED_READER)
        .expect("the deposited reader's aperture is admissible");
    let before = before_circuit
        .invariants(PivotRule::SmallestMagnitude)
        .expect("the atlas reads");
    println!(
        "    BEFORE  {} artifacts, {} declarations, {} recruitments",
        standing_paths.len(),
        before_circuit.vertices().len(),
        before_circuit.recruitments().len()
    );
    println!(
        "    betti {:?}   torsion {:?}",
        before.betti_vector(),
        before.total_torsion()
    );
    failures.require(
        standing_paths
            .iter()
            .all(|path| !path.starts_with(&standing_deposit)),
        "the reading BEFORE is taken from a state this production cannot destroy",
    );

    println!("\n    the target population, ranked by the artifact lineage behind each");
    let ranked = before_circuit.single_vertex_statements_by_lineage();
    for (statement, lineage) in &ranked {
        println!("      {:>4} artifacts   {statement}", lineage.len());
    }
    println!("    and the statements the reading excludes, already reached by two declarations");
    for statement in before_circuit.plural_vertex_statements() {
        println!(
            "      {:?} reach   {statement}",
            before_circuit.vertices_reaching(statement)
        );
    }

    let without_reading = before_circuit.statements();
    let with_reading = before_circuit.single_vertex_statements();
    failures.require(
        with_reading != without_reading && !with_reading.is_empty(),
        "the reading strictly narrowed the target population",
    );

    let Some((target, target_lineage)) = ranked.first().map(|(s, l)| ((*s).to_owned(), l.len()))
    else {
        eprintln!("\nFAILED — the reading selected no target: every statement is already plural");
        std::process::exit(1);
    };
    println!("\n    SELECTED  {target_lineage} artifacts   {target}");
    if let Some((runner_up, lineage)) = ranked.get(1) {
        println!("    runner-up {:>4} artifacts   {runner_up}", lineage.len());
    }

    // ------------------------------------------------------ the production
    println!("\n=== the production: the selected statement, two declarations");
    let pinned = std::fs::read_to_string(project_root.join("lean-toolchain"))
        .expect("the kernel project carries a lean-toolchain pin");
    let running = String::from_utf8_lossy(
        &Command::new("lean")
            .arg("--version")
            .output()
            .expect("`lean` is on PATH; without it no kernel verdict is available at all")
            .stdout,
    )
    .trim()
    .to_owned();
    println!("    lean-toolchain   {}", pinned.trim());
    println!("    lean --version   {running}");
    let pin_holds = running.contains(
        pinned
            .trim()
            .rsplit(':')
            .next()
            .unwrap_or_default()
            .trim_start_matches('v'),
    );
    failures.require(pin_holds, "the running kernel is the pinned toolchain");
    failures.require(
        build_kernel_project(&project_root),
        "the kernel project's library builds",
    );

    let corpus = collect_lean_documents(&corpus_root).expect("the formal corpus reads");
    let ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    println!(
        "    conditioned {} declaration organs from {} documents, {} retained source surfaces",
        ecology.receipt().declaration_organs,
        ecology.receipt().source_documents_exposed,
        ecology.receipt().retained_source_surfaces
    );

    let _ = std::fs::remove_dir_all(&scratch_root);
    let kernel = LeanKernelWorld::new(&project_root, &scratch_root, 4)
        .expect("the kernel world mounts with a nonzero worker aperture");

    // A live selection can land on a statement the conditioned body has no declaration star for.
    // That is a return, not a crash: the reading named a target and the production reports that it
    // cannot reach it, with the target and the refusal both printed. Verified by running this
    // driver with the BEFORE exclusion removed, where the reading selects `(a b : Nat) : a = b`
    // and the ecology returns `NoLocalDeclarations`.
    let mut families: Vec<(LeanProofProblem, LeanKernelReturnFamily)> = Vec::new();
    let mut unreachable: Option<String> = None;
    for problem in [direct_problem(&target), relayed_problem(&target)] {
        let composed = ecology
            .materialize_kernel_problem(&problem)
            .and_then(|kernel_problem| {
                ecology
                    .generate_proof_candidates(&kernel_problem)
                    .map(|composed| (kernel_problem, composed))
            });
        let (kernel_problem, (reached, candidates)) = match composed {
            Ok(carried) => carried,
            Err(refusal) => {
                unreachable = Some(format!("{}: {refusal:?}", problem.identity));
                break;
            }
        };
        println!(
            "\n    {}\n      declaration star {:?}\n      proof paths      {}",
            problem.theorem_header,
            reached.iter().collect::<Vec<_>>(),
            candidates.len()
        );
        let returns = kernel
            .grade_all(&kernel_problem, &candidates)
            .expect("every candidate receives a kernel verdict");
        println!(
            "      kernel admitted  {}\n      kernel refused   {}",
            returns.kernel_admitted_extent(),
            returns.obstruction_extent()
        );
        families.push((kernel_problem, returns));
    }

    failures.require(
        unreachable.is_none(),
        "the conditioned body composes a proof family for the statement the reading selected",
    );
    if let Some(refusal) = unreachable {
        println!(
            "\n    the reading selected {target}\n    and the conditioned body returned {refusal}"
        );
        eprintln!(
            "\nFAILED — {} declared control(s) did not hold:",
            failures.0.len()
        );
        for claim in &failures.0 {
            eprintln!("  - {claim}");
        }
        std::process::exit(1);
    }

    let admitted: usize = families
        .iter()
        .map(|(_, returns)| returns.kernel_admitted_extent())
        .sum();
    let refused: usize = families
        .iter()
        .map(|(_, returns)| returns.obstruction_extent())
        .sum();
    failures.require(admitted > 0, "the kernel admitted at least one path");
    failures.require(
        refused > 0,
        "the kernel refused at least one path, so the deposit is not success-filtered",
    );

    // The verdict ledger. The `.lean` artifacts carry no outcome, so a reader cannot tell an
    // admitted route from a refused one. This is the material a founding would need in order to
    // make a refusal its own vertex rather than an absence; nothing reads it yet, and this driver
    // does not pretend otherwise.
    //
    // The kernel's diagnostic text is DELIBERATELY not recorded here. `lake env lean` prefixes
    // every message with the absolute path of the file it read, so a hash of a diagnostic folds
    // this checkout's location into the deposit -- the absolute frame `CLAUDE.md` §0 convicts by
    // name, and it would report drift the moment the tree moved. The outcome and the rendered
    // source's hash are path-free and are what a founding of refusals needs.
    let mut ledger = String::from(
        "law=every generated path is deposited; this records which of them the kernel admitted\n\
         columns=outcome ordinal source_sha256 artifact\n",
    );
    for (problem, returns) in &families {
        for returned in returns.members() {
            ledger.push_str(&format!(
                "{} {} {} {}-{:05}.lean\n",
                match returned.outcome() {
                    LeanKernelOutcome::KernelAdmitted => "admitted",
                    LeanKernelOutcome::Obstructed => "refused ",
                },
                returned.candidate().ordinal,
                returned.source_sha256(),
                problem.identity.replace('.', "-"),
                returned.candidate().ordinal,
            ));
        }
    }
    std::fs::write(scratch_root.join("KERNEL_VERDICTS.txt"), ledger.as_bytes())
        .expect("the verdict ledger writes beside the artifacts it describes");

    // ------------------------------------------------------ the reading AFTER
    println!("\n=== the reading on this driver's own deposit alone");
    let control_paths = artifact_paths(&scratch_root);
    let control_population = read_population(&control_paths);
    let control_circuit = found_circuit(&control_population, CircuitAperture::DEPOSITED_READER)
        .expect("the deposited reader's aperture is admissible");
    let control = control_circuit
        .invariants(PivotRule::SmallestMagnitude)
        .expect("the atlas reads");
    println!(
        "    {} artifacts, {} declarations, {} recruitments",
        control_paths.len(),
        control_circuit.vertices().len(),
        control_circuit.recruitments().len()
    );
    for grade in &control.grades {
        println!(
            "    grade {}  cells {:>4}  betti {:>3}  torsion {:?}",
            grade.grade, grade.cells, grade.betti, grade.torsion
        );
    }

    println!(
        "    declarations reaching the target statement {:?}",
        control_circuit.vertices_reaching(&target)
    );
    failures.require(
        control_circuit.vertices_reaching(&target).len() > 1,
        "two DIFFERENT declaration names reached the statement the reading selected",
    );

    // The two recruitment populations must share, and must not be equal. If they were equal the
    // relayed environment recruited nothing the direct one did not, and "different recruitment"
    // would be a description of a fixture rather than of the production.
    let recruitment_of = |name: &str| -> BTreeSet<String> {
        control_population
            .iter()
            .filter(|derivation| derivation.name == name)
            .flat_map(|derivation| {
                derivation
                    .recruited_symbols()
                    .into_iter()
                    .map(str::to_owned)
            })
            .collect()
    };
    let left = recruitment_of("carrier_transport_direct");
    let right = recruitment_of("carrier_transport_relayed");
    let shared: BTreeSet<&String> = left.intersection(&right).collect();
    println!("    direct recruits  {left:?}");
    println!("    relayed recruits {right:?}");
    println!("    shared           {shared:?}");
    failures.require(
        left != right && shared.len() > 1,
        "the two declarations recruit DIFFERENT populations sharing more than one symbol",
    );

    // The reading is a function of what the kernel was actually asked, or it is a function of the
    // two preamble strings above and sixty kernel invocations cannot move it by one bit. That was
    // true of this driver until 2026-08-08.
    println!("\n    distinct recruitment populations per declaration, in this deposit");
    let classes = recruitment_classes(&control_population);
    for (declaration, distinct) in &classes {
        println!("      {declaration}  {} distinct", distinct.len());
        for recruited in distinct {
            let rendered: Vec<String> = recruited
                .iter()
                .map(|(symbol, count)| format!("{symbol} x{count}"))
                .collect();
            println!("        {}", rendered.join(", "));
        }
    }
    failures.require(
        classes.values().any(|distinct| distinct.len() > 1),
        "CONTROL the reading is a function of the proof bodies produced, not of the preamble alone",
    );

    // The comparison the whole obligation rests on: the same reader, the same aperture, on the
    // production that has always returned zero.
    let production_paths = artifact_paths(&standing_root.join("lean-proof-production"));
    let production = reading(&read_population(&production_paths));
    println!(
        "\n    the reader's own historical deposit, same aperture: {} artifacts, betti {:?}",
        production_paths.len(),
        production.betti_vector()
    );
    failures.require(
        betti_at(&production, 1) == 0 && betti_at(&control, 1) > 0,
        "CONTROL the reading was zero on the historical deposit and is nonzero on this one",
    );

    // ------------------------------------------------------ the reflective face
    println!("\n=== the reflective face: what this production moved in the reading");
    let mut joined = standing_population.clone();
    joined.extend(control_population.iter().cloned());
    let after_circuit = found_circuit(&joined, CircuitAperture::DEPOSITED_READER)
        .expect("the deposited reader's aperture is admissible");
    let after = after_circuit
        .invariants(PivotRule::SmallestMagnitude)
        .expect("the atlas reads");

    let movement = invariant_movement(&before, &after);
    let routes = route_movement(&before_circuit, &after_circuit);
    println!(
        "    betti {:?} -> {:?}",
        before.betti_vector(),
        after.betti_vector()
    );
    println!(
        "    grades moved {:?}   fields moved {:?}",
        movement.grades_moved(),
        movement.fields_moved()
    );
    for grade in movement.moved() {
        println!(
            "      grade {}  cells {:?} -> {:?}   betti {:?} -> {:?}   torsion {:?} -> {:?}",
            grade.grade,
            grade.before.as_ref().map(|side| side.cells),
            grade.after.as_ref().map(|side| side.cells),
            grade.before.as_ref().map(|side| side.betti),
            grade.after.as_ref().map(|side| side.betti),
            grade.before.as_ref().map(|side| side.torsion.clone()),
            grade.after.as_ref().map(|side| side.torsion.clone()),
        );
    }
    println!("    statements founded {:?}", routes.founded_statements());
    println!("    became plural      {:?}", routes.became_plural());
    for (statement, founded) in routes.founded_routes() {
        println!("      {founded:?} newly reach  {statement}");
    }
    println!("    lineage deepened — the frame a deduplicated support cannot see");
    for (statement, deepened) in routes.deepened_routes() {
        println!("      {deepened:?}  further reach  {statement}");
    }

    // The routes to one result, by two disjoint paths, before and after.
    let excess_before = route_cycle_agreement(
        &standing_population,
        DerivationIdentity::ByDeclaration,
        PivotRule::SmallestMagnitude,
    )
    .expect("an incidence reading is admissible");
    let excess_after = route_cycle_agreement(
        &joined,
        DerivationIdentity::ByDeclaration,
        PivotRule::SmallestMagnitude,
    )
    .expect("an incidence reading is admissible");
    println!(
        "\n    independent routes to one result   before  homological {} lineage {}\n\
         \x20                                      after   homological {} lineage {}",
        excess_before.homological,
        excess_before.lineage,
        excess_after.homological,
        excess_after.lineage
    );

    failures.require(
        !movement.is_still(),
        "the production moved the reading -- the analysis is not blind to it",
    );
    failures.require(
        movement.is_still() == invariants_agree(&before, &after),
        "the movement population and invariants_agree return one verdict",
    );
    failures.require(
        forest_agrees(&before_circuit) && forest_agrees(&after_circuit),
        "smith normal form and an independent spanning forest return one pair of betti numbers",
    );
    failures.require(
        movement.grades_moved().contains(&1)
            && movement.fields_moved().contains(&MovedField::Betti),
        "the movement names grade 1 and names the betti field",
    );
    failures.require(
        routes
            .became_plural()
            .iter()
            .any(|statement| *statement == target),
        "the route movement names the selected statement as become-plural, as a population",
    );
    failures.require(
        !routes.deepened_routes().is_empty(),
        "the route movement reads the artifact lineage and not only the deduplicated support",
    );
    failures.require(
        excess_before.holds() && excess_after.holds(),
        "the homological and lineage accounts of the routes to one result agree",
    );
    failures.require(
        excess_after.lineage > excess_before.lineage,
        "the production ADDED an independent route to a result, by both accounts",
    );
    failures.require(
        !before_circuit
            .plural_vertex_statements()
            .contains(target.as_str())
            && after_circuit
                .plural_vertex_statements()
                .contains(target.as_str()),
        "the statement the reading selected was un-cross-checked before and is cross-checked after",
    );

    // ------------------------------------------------------ refusals
    println!("\n=== refusals are in the deposit; the VERDICT is not");
    let refused_artifact = families
        .iter()
        .flat_map(|(problem, returns)| {
            returns
                .members()
                .iter()
                .map(move |returned| (problem, returned))
        })
        .find(|(_, returned)| returned.outcome() == LeanKernelOutcome::Obstructed);
    let admitted_artifact = families
        .iter()
        .flat_map(|(problem, returns)| {
            returns
                .members()
                .iter()
                .map(move |returned| (problem, returned))
        })
        .find(|(_, returned)| returned.outcome() == LeanKernelOutcome::KernelAdmitted);
    if let (Some((refused_problem, refused_return)), Some((admitted_problem, admitted_return))) =
        (refused_artifact, admitted_artifact)
    {
        let refused_source = refused_problem
            .render(&refused_return.candidate().proof)
            .expect("a refused path renders");
        let admitted_source = admitted_problem
            .render(&admitted_return.candidate().proof)
            .expect("an admitted path renders");
        let refused_read = read_derivation(&refused_source).expect("a refused artifact parses");
        let admitted_read = read_derivation(&admitted_source).expect("an admitted artifact parses");
        println!("    a refused source, deposited verbatim:");
        for line in refused_source.lines() {
            println!("      {line}");
        }
        println!(
            "    the kernel said: {}",
            refused_return
                .diagnostic()
                .trim()
                .lines()
                .next()
                .unwrap_or("")
        );
        println!(
            "\n    the atlas reads the refused artifact as   name {:?} statement {:?}\n\
             \x20     recruiting {:?}",
            refused_read.name, refused_read.statement, refused_read.recruited
        );
        println!(
            "    the atlas reads the admitted artifact as  name {:?} statement {:?}\n\
             \x20     recruiting {:?}",
            admitted_read.name, admitted_read.statement, admitted_read.recruited
        );
        failures.require(
            refused_read.statement == admitted_read.statement,
            "a refused proof recruits into the atlas exactly as an accepted one does",
        );
        println!(
            "\n    OPEN: nothing in a deposited `.lean` says which of these the kernel admitted, so\n\
             \x20        the reading cannot distinguish them and a refusal cannot found anything of\n\
             \x20        its own. `KERNEL_VERDICTS.txt` beside the artifacts carries the outcome and\n\
             \x20        the rendered source's hash; it is deposited and NOT read. Founding refusals\n\
             \x20        would take a second vertex class in `found_circuit` -- an obstruction vertex\n\
             \x20        per (statement, diagnostic class) that refused paths recruit into -- so that\n\
             \x20        a statement reached only by refusals is a component rather than an absence.\n\
             \x20        The diagnostic class it would key on cannot be the kernel's message: that\n\
             \x20        text carries this checkout's absolute path, so it must be reduced to a\n\
             \x20        path-free species before anything hashes or deposits it."
        );
    }

    // ------------------------------------------------------ the return
    println!("\n=== the return");
    println!("    target selected from the reading  {target}");
    println!(
        "    artifacts deposited               {}",
        control_paths.len()
    );
    println!("    kernel admitted / refused         {admitted} / {refused}");
    println!(
        "    betti at grade 1, historical      {}",
        betti_at(&production, 1)
    );
    println!(
        "    betti at grade 1, this control    {}",
        betti_at(&control, 1)
    );
    println!(
        "    scratch                           {}",
        scratch_root.display()
    );

    if failures.0.is_empty() {
        println!(
            "\nThe reading was zero on the machine's own production because thirty-one routes to one\n\
             statement are one vertex under the identity the reader founds. The reading itself named\n\
             that statement as the most-produced result no second declaration had reached; this\n\
             driver posed it under two declaration names and a real kernel graded every path; and the\n\
             re-reading returns the statement as cross-checked, the lineage as deepened, and one more\n\
             independent route to one result by two disjoint computations."
        );
    } else {
        eprintln!(
            "\nFAILED — {} declared control(s) did not hold:",
            failures.0.len()
        );
        for claim in &failures.0 {
            eprintln!("  - {claim}");
        }
        std::process::exit(1);
    }
}
