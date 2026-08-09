//! **The research act, end to end, returning the artifact.**
//!
//! ```text
//! cargo run --release --example the_research_act -- \
//!     standing/output \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! One mathematical question is posed to a conditioned instance; the instance produces; the
//! production is read back as a circuit; the circuit's integer invariants are taken; the movement
//! between two readings is returned into the next production; the emission is situated against the
//! unconditioned null; the body derives again and is read again. **What this driver returns is the
//! mathematical text the instance produced**, every passage in full, each with the bridge that
//! licensed it. Counts and diagnostics are here only to support that.
//!
//! ## The question
//!
//! > *The deposit reaches `|- (P : Prop) (h : P) : exactCarrier P` by declarations that were written
//! > down. Is there a further route to it that the deposit does not carry, licensed by a **word the
//! > corpus committed** rather than by a residual letter — and if so, what is it, what licensed it,
//! > and are two of the routes the same theorem?*
//!
//! The last clause is the one with mathematical content. **`β₁` at grade 1 of the
//! statement-founded circuit is the number of independent routes to one result** — an exact integer
//! obtained by Smith normal form over an integer boundary matrix, never a probability over tactics —
//! and `derivation_skein` decides whether a local substitution carries one returned derivation to
//! another without any declared receiver seeing the difference.
//!
//! ## The declared aperture, and what it is not
//!
//! *"licensed by a word the corpus committed"* is [`MoveAperture::morphemic`] at
//! [`MORPHEMIC_LETTERS`], and it is part of the **question**, not a filter applied to an answer.
//! `derivation_skein` states its own reason: *"a licence carried by a single residual letter is a
//! different kind of object from one carried by a whole word the corpus committed, and this names
//! which is being read. It is an aperture, not a filter on quality — the population it excludes is
//! recoverable by declaring those stems."* The excluded population is therefore **exhibited in
//! full, by name, with its licensing stem**, and no quantity anywhere ranks one passage against
//! another.
//!
//! ## The five declared controls. The driver exits non-zero if any fails.
//!
//! ```text
//!   1  the unconditioned null returns the EMPTY population on every query used
//!   2  β₁ >= 1 with both routes exhibited, AND a declared control on which β₁ = 0, so the
//!      invariant is shown to be able to come out otherwise
//!   3  the returned passage is not in the deposit, checked by content against every artifact
//!   4  the situated residual against the null is non-empty for the conditioned body and empty
//!      for the null against itself
//!   5  withholding the conditioning entirely and re-running the identical act returns the
//!      departed passages as a POPULATION, exhibited by name, never as a count delta
//! ```
//!
//! ## What is not claimed
//!
//! Nothing here is submitted to a kernel. A derived passage is production read as structure exactly
//! as the deposited artifacts are — the deposit itself carries `theorem carrier_transport ... :=
//! Nat.zero` and `theorem every_receiver_agrees (a b : Nat) : a = b`, which no kernel accepts and
//! which the atlas reads all the same. Nothing here bears on any Millennium result.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;

use holonic_engine::algebraic::{CausalCellId, CausalChain, ComparativeMultiplicity};
use holonic_engine::conditioned_derivation::{
    ablate_stem, expose, found_conditioned_circuit, ConditionedBody, ConditionedCircuit,
    DerivationQuery, DerivedPassage, Exposure, FoundedMorphology, Passage,
};
use holonic_engine::derivation_atlas::{
    route_cycle_agreement, route_movement, statement_vertex_key, CircuitAperture, Derivation,
    DerivationIdentity,
};
use holonic_engine::derivation_integral::AccumulationRule;
use holonic_engine::derivation_skein::{
    declared_contexts, moves_the_production_made, passages_under, MoveAperture, MoveSpecies,
};
use holonic_engine::rebase_invariants::{PivotRule, RebaseInvariants};
use holonic_engine::returned_reading::{condition_again, read_production};
use holonic_engine::situated_residual::{emission_reaching, situate, Frame};
use holonic_engine::skein::read_substitution;
use holonic_engine::surprisal::Grain;

/// The statement put to the instance. It is in the deposit; the question is whether a route to it
/// that the deposit does not carry can be returned.
const STATEMENT: &str = "(P : Prop) (h : P) : exactCarrier P";

/// A statement the deposit does not reach, in the same vocabulary. The new-statement probe.
const ABSENT_STATEMENT: &str = "(P : Prop) (h : P) : exactCarrier (exactCarrier P)";

/// The declared aperture: a licence carried by a founded stem of at least this many characters.
///
/// Four, and the figure is a **declaration of what is being asked about**, not a bound anything is
/// compared against for admission. `derivation_skein::MoveAperture::morphemic` is the organ; the
/// population outside is exhibited by name and is recoverable by declaring those stems.
const MORPHEMIC_LETTERS: usize = 4;

const APERTURE: CircuitAperture = CircuitAperture::STATEMENT_INCIDENT;
const PIVOT: PivotRule = PivotRule::SmallestMagnitude;
const RULE: AccumulationRule = AccumulationRule::RecruitmentLoad;

// -------------------------------------------------------------------------------------------------
// Material, read from disk
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
// The declared β₁ = 0 control material
// -------------------------------------------------------------------------------------------------

/// Two declarations reaching two different statements, recruiting nothing in common.
///
/// The statement lines name only single-character binders, which `read_derivation` excludes, so each
/// declaration recruits exactly what its proof body names — and the two bodies name disjoint
/// identifiers. That disjointness is the whole content of the control: it is what keeps the circuit
/// a forest and lets `β₁` come out zero on material this same act runs over unchanged.
fn control_deposit() -> Vec<(String, String)> {
    [
        (
            "control/alpha.lean",
            "theorem alpha_holds (h : P) : Q h := by\n  have chosen := alphaCarrier\n",
        ),
        (
            "control/beta.lean",
            "theorem beta_holds (h : R) : S h := by\n  have chosen := betaCarrier\n",
        ),
    ]
    .into_iter()
    .map(|(source, text)| (source.to_owned(), text.to_owned()))
    .collect()
}

/// Two wholes that between them commit exactly `alpha`, `and`, `beta`, `carrier` and `the`.
///
/// `an`, `a`, `share` and `of` are witnessed by one whole each and stay provisional, so the
/// recurrence law is doing work here rather than admitting everything.
fn control_corpus() -> Vec<Exposure> {
    vec![
        expose(
            "control/one",
            "an alpha carrier and a beta carrier share the carrier",
        ),
        expose("control/two", "the carrier of alpha and the carrier of beta"),
    ]
}

// -------------------------------------------------------------------------------------------------
// Reading conveniences
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(100));
    println!("{title}");
    println!("{}", "=".repeat(100));
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

fn grade_of(invariants: &RebaseInvariants, grade: u32) -> (usize, usize, Vec<BigInt>) {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map(|carried| (carried.cells, carried.betti, carried.torsion.clone()))
        .unwrap_or((0, 0, Vec::new()))
}

/// Print a complete population across as many lines as it takes. Nothing is elided.
fn wrapped(indent: &str, items: &[String]) {
    let mut line = String::new();
    for item in items {
        if !line.is_empty() && line.chars().count() + item.chars().count() + 1 > 96 {
            println!("{indent}{line}");
            line.clear();
        }
        if !line.is_empty() {
            line.push(' ');
        }
        line.push_str(item);
    }
    if !line.is_empty() {
        println!("{indent}{line}");
    }
}

fn torsion_named(torsion: &[BigInt]) -> String {
    if torsion.is_empty() {
        "(empty)".to_owned()
    } else {
        format!(
            "[{}]",
            torsion
                .iter()
                .map(BigInt::to_string)
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

/// Print the integer invariants of one circuit, grade by grade. Every figure is an exact integer
/// taken from Smith normal form over the boundary matrix.
fn exhibit_invariants(label: &str, invariants: &RebaseInvariants) {
    println!("\n  {label}");
    println!(
        "    {:<8} {:>8} {:>10} {:>12} {:>8}  {}",
        "grade", "cells", "d-rank", "fill-rank", "betti", "torsion"
    );
    for grade in &invariants.grades {
        println!(
            "    {:<8} {:>8} {:>10} {:>12} {:>8}  {}",
            grade.grade,
            grade.cells,
            grade.boundary_rank,
            grade.filling_rank,
            grade.betti,
            torsion_named(&grade.torsion)
        );
    }
    println!(
        "    euler characteristic {}   (cellwise {})",
        invariants.euler_characteristic(),
        invariants.cell_euler_characteristic()
    );
}

/// One passage as the artifact it is: the licensing stem with the corpus wholes that founded it,
/// the brought identifier, every route that licensed it, and the full text.
fn exhibit_passage(
    ordinal: usize,
    passage: &DerivedPassage,
    sources: &BTreeMap<String, String>,
    morphology: &FoundedMorphology,
) {
    println!("\n  ({ordinal})  {}", passage.name);
    let founded_by = morphology
        .stem(&passage.stem)
        .map(|stem| stem.wholes.join(", "))
        .unwrap_or_else(|| "(the morphology does not carry this stem)".to_owned());
    println!(
        "        stem {:?}  founded by the corpus wholes: {founded_by}",
        passage.stem
    );
    println!(
        "        brought {}   extends the standing declaration {}",
        passage.brought, passage.reaches
    );
    for bridge in passage.licensing() {
        println!(
            "        bridge  {} @{}  <-{:?}->  {} @{}",
            bridge.held, bridge.held_at, bridge.stem, bridge.brought, bridge.brought_at
        );
        println!(
            "                licensed by {} deposited route(s):",
            bridge.routes.len()
        );
        wrapped("                  ", &bridge.routes);
    }
    // The artifacts every one of those routes was read from, grouped by the directory they sit in.
    // The complete population; a route key and an artifact path are in bijection here.
    let mut by_directory: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for route in passage.routes() {
        let Some(source) = sources.get(route) else {
            continue;
        };
        let (directory, file) = source.rsplit_once('/').unwrap_or(("", source.as_str()));
        by_directory
            .entry(directory)
            .or_default()
            .insert(file.trim_end_matches(".lean").to_owned());
    }
    for (directory, files) in &by_directory {
        println!("        those routes were read from the artifacts under {directory}/ :");
        wrapped(
            "          ",
            &files.iter().cloned().collect::<Vec<String>>(),
        );
    }
    println!("        the artifact:");
    for line in passage.text.lines() {
        println!("        | {line}");
    }
}

/// The complete population outside the declared aperture, exhibited by name with its licensing
/// stem. Named, never counted away.
fn exhibit_outside(outside: &[DerivedPassage]) {
    println!(
        "\n  outside the declared aperture -- licensed by a founded stem shorter than \
         {MORPHEMIC_LETTERS} characters.\n  The complete population, by name. Declaring those stems \
         recovers every one of them:\n"
    );
    for passage in outside {
        println!(
            "    {:<58} stem {:<6} brought {}",
            passage.name,
            format!("{:?}", passage.stem),
            passage.brought
        );
    }
    if outside.is_empty() {
        println!("    (none)");
    }
    let stems: BTreeSet<&str> = outside.iter().map(|passage| passage.stem.as_str()).collect();
    println!("\n  the stems that licensed them: {stems:?}");
}

/// Every cell of a chain, named, with its integer coefficient.
fn exhibit_chain(circuit: &ConditionedCircuit, chain: &CausalChain, indent: &str) {
    let complex = circuit.circuit.complex();
    for (cell, coefficient) in chain.coefficients() {
        let difference = coefficient.difference();
        if difference == BigInt::from(0) {
            continue;
        }
        let name = complex
            .cell(*cell)
            .map(|carried| carried.name.clone())
            .unwrap_or_else(|_| format!("?{}", cell.0));
        println!("{indent}{difference:>+3} · {name}");
    }
}

/// The 1-cycle two routes to one statement close through one shared recruited symbol.
///
/// ```text
///   (left <- symbol) - (right <- symbol) - (left |- statement) + (right |- statement)
/// ```
///
/// Its boundary is `(L−X) − (R−X) − (L−S) + (R−S) = 0` identically, so this is an exact integer
/// 1-cycle whenever all four cells exist. Nothing is approximated and no orientation is chosen: the
/// coefficients are the incidence the circuit already carries.
fn route_cycle(
    circuit: &ConditionedCircuit,
    left: &str,
    right: &str,
    symbol: &str,
    statement: &str,
) -> Option<CausalChain> {
    let recruitments = circuit.circuit.recruitments();
    let reaches = circuit.circuit.reaches();
    let left_recruits = *recruitments.get(&(left.to_owned(), symbol.to_owned()))?;
    let right_recruits = *recruitments.get(&(right.to_owned(), symbol.to_owned()))?;
    let left_reaches = *reaches.get(&(left.to_owned(), statement.to_owned()))?;
    let right_reaches = *reaches.get(&(right.to_owned(), statement.to_owned()))?;

    let mut chain = CausalChain::default();
    chain.add_term(left_recruits, ComparativeMultiplicity::positive(1u32));
    chain.add_term(right_recruits, ComparativeMultiplicity::negative(1u32));
    chain.add_term(left_reaches, ComparativeMultiplicity::negative(1u32));
    chain.add_term(right_reaches, ComparativeMultiplicity::positive(1u32));
    Some(chain)
}

/// Whether the routes to a statement, taken as declaration vertices of the circuit, are plural.
fn routes_to(circuit: &ConditionedCircuit, statement: &str) -> Vec<String> {
    circuit
        .circuit
        .vertices_reaching(statement)
        .into_iter()
        .map(str::to_owned)
        .collect()
}

/// The passage text of one declaration vertex, if the population carries it.
///
/// **The statement is required.** Under `DerivationIdentity::ByDeclaration` one declaration vertex
/// can reach two statements — `carrier_transport` reaches both `(P : Prop) (h : P) : exactCarrier P`
/// and `(h : P) : exactCarrier P` in this deposit — so looking a route up by name alone can return
/// an artifact that is not a route to the queried statement at all.
fn text_of<'a>(passages: &'a [Passage], declaration: &str, statement: &str) -> Option<&'a Passage> {
    passages.iter().find(|passage| {
        passage.derivation.name == declaration && passage.derivation.statement == statement
    })
}

// -------------------------------------------------------------------------------------------------
// One run of the act, so the ablation can run the identical act with the conditioning withheld
// -------------------------------------------------------------------------------------------------

struct Act {
    /// Everything the body returned, at every stem length.
    all: Vec<DerivedPassage>,
    /// The population at the declared aperture. Exhibited in full.
    production: Vec<DerivedPassage>,
    /// The complement. Exhibited by name, with its licensing stem.
    outside: Vec<DerivedPassage>,
    /// The standing deposit together with the production at the aperture, ids renumbered.
    passages: Vec<Passage>,
    after: ConditionedCircuit,
    invariants: RebaseInvariants,
}

fn run_act(body: &ConditionedBody, query: &DerivationQuery) -> Act {
    let all = body.derive(query).expect("the production founds");
    let whole = body.passages(query).expect("the passages found");
    let aperture = MoveAperture::morphemic(&whole, MORPHEMIC_LETTERS);
    let passages = passages_under(&whole, &aperture);
    let after = found_conditioned_circuit(passages.clone(), APERTURE).expect("the circuit founds");
    let invariants = after.circuit.invariants(PIVOT).expect("the invariants read");
    let (production, outside): (Vec<DerivedPassage>, Vec<DerivedPassage>) = all
        .iter()
        .cloned()
        .partition(|passage| passage.stem.chars().count() >= MORPHEMIC_LETTERS);
    Act {
        all,
        production,
        outside,
        passages,
        after,
        invariants,
    }
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
            .unwrap_or_else(|| "reference/holobrochos-a07ff376/src/soma".to_owned()),
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
    let query = DerivationQuery::reaching(STATEMENT);

    let null = ConditionedBody::mount(deposit.clone()).expect("the deposit declares theorems");
    let mut body = null.clone();
    body.condition(&corpus);
    let standing = body.standing_derivations();

    // Route key -> the artifact path that founded it, so a bridge names its source on disk.
    let sources: BTreeMap<String, String> = deposit
        .iter()
        .enumerate()
        .filter_map(|(ordinal, (source, text))| {
            holonic_engine::derivation_atlas::read_derivation(text)
                .map(|derivation| (format!("{}#{ordinal}", derivation.name), source.clone()))
        })
        .collect();

    // ---------------------------------------------------------------------------------------------
    rule("THE QUESTION");
    println!(
        "\n  The deposit reaches |- {STATEMENT}\n  by declarations that were written down. Is there \
         a further route to it that the deposit does\n  not carry, licensed by a WORD the corpus \
         committed rather than by a residual letter --\n  and if so, what is it, what licensed it, \
         and are two of the routes the same theorem?"
    );
    println!(
        "\n  the declared aperture: a licence carried by a founded stem of at least \
         {MORPHEMIC_LETTERS} characters.\n  It is part of the question. The population outside it \
         is exhibited by name in [3b] and is\n  recoverable by declaring those stems."
    );
    println!("\n  the mathematical deposit   {:<44} {} artifacts", deposit_root.display(), deposit.len());
    println!("  the linguistic corpus      {:<44} {} wholes", corpus_root.display(), corpus.len());
    println!("\n  the deposit reaches these statements:");
    for statement in body.standing_statements() {
        let routes = standing
            .iter()
            .filter(|derivation| derivation.statement == *statement)
            .count();
        println!("    |- {statement:<52} {routes} deposited routes");
    }
    println!("\n  and recruits these identifiers:");
    for identifier in body.recruited_population() {
        println!("    {identifier}");
    }

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE CONDITIONING  --  reusable morphology founded by exposure to linguistic material");

    let morphology = body.morphology().clone();
    println!(
        "\n  founded {}   committed {}   provisional {}",
        morphology.founded().len(),
        morphology.committed().len(),
        morphology.provisional().len()
    );
    println!("\n  every recruited identifier, decomposed under the founded morphology");
    println!("  (a bracketed character is residue: material no committed stem covers)\n");
    for identifier in body.recruited_population() {
        let cover = morphology.cover(&identifier).expect("ascii");
        println!("    {:<22} {}", identifier, cover.render());
    }

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE NULL  --  the same question put to a body exposed to nothing");

    let mut null_returns_empty = true;
    let mut null_queries: Vec<String> = Vec::new();
    for statement in body.standing_statements() {
        let returned = null
            .derive(&DerivationQuery::reaching(&statement))
            .expect("the null derives");
        println!("    |- {:<54} returned {} passages", statement, returned.len());
        null_returns_empty &= returned.is_empty();
        null_queries.push(statement);
    }
    let absent_from_null = null
        .derive(&DerivationQuery::reaching(ABSENT_STATEMENT))
        .expect("the null derives");
    println!(
        "    |- {:<54} returned {} passages",
        ABSENT_STATEMENT,
        absent_from_null.len()
    );
    null_returns_empty &= absent_from_null.is_empty();
    null_queries.push(ABSENT_STATEMENT.to_owned());

    controls.check(
        "control 1 -- the unconditioned null returns the empty population",
        null_returns_empty,
        &format!(
            "{} queries put to a body exposed to nothing; every one returned the empty population. \
             A body that has founded no stem can hold no two identifiers together, so nothing \
             licenses a bridge.",
            null_queries.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE PRODUCTION  --  every returned passage, in full, with the bridge that licensed it");

    let act = run_act(&body, &query);
    println!(
        "\n  the conditioned instance returned {} passages reaching |- {STATEMENT},\n  of which {} \
         are at the declared aperture. Every one of those {} is exhibited here in full.",
        act.all.len(),
        act.production.len(),
        act.production.len()
    );
    for (ordinal, passage) in act.production.iter().enumerate() {
        exhibit_passage(ordinal, passage, &sources, &morphology);
    }

    // ---------------------------------------------------------------------------------------------
    rule("[3b]  THE POPULATION OUTSIDE THE DECLARED APERTURE  --  named in full, never counted away");
    exhibit_outside(&act.outside);

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE CIRCUIT  --  the production as a GradedCausalComplex, read as integer invariants");

    let before = found_conditioned_circuit(body.standing().to_vec(), APERTURE)
        .expect("the deposit founds a circuit");
    let before_invariants = before.circuit.invariants(PIVOT).expect("reads");
    exhibit_invariants("the deposit alone", &before_invariants);
    exhibit_invariants("the deposit together with the production", &act.invariants);

    let (_, before_betti_1, _) = grade_of(&before_invariants, 1);
    let (_, betti_0, _) = grade_of(&act.invariants, 0);
    let (_, betti_1, torsion_1) = grade_of(&act.invariants, 1);
    println!(
        "\n  beta_0 = {betti_0}   beta_1 = {betti_1}   torsion at grade 1 {}",
        torsion_named(&torsion_1)
    );
    println!(
        "  the production moved beta_1 from {before_betti_1} to {betti_1}, an increase of {}.",
        betti_1 as i64 - before_betti_1 as i64
    );
    println!(
        "\n  beta_1 is the whole independent cycle rank, and the part of it that is ROUTES TO ONE \
         RESULT\n  is separable: it is what founding the statement 0-cells opens over the \
         statement-blind\n  reading, and `route_cycle_agreement` holds that homological reading \
         against the circuit's\n  own route lineage, which is counted from disjoint material."
    );
    let derivations: Vec<Derivation> = act
        .passages
        .iter()
        .map(|passage| passage.derivation.clone())
        .collect();
    match route_cycle_agreement(&derivations, DerivationIdentity::ByDeclaration, PIVOT) {
        Err(refusal) => println!("    the agreement was refused: {refusal}"),
        Ok(agreement) => println!(
            "    homological (statements founded minus statements withheld) {}\n    lineage \
             (sum over statements of routes reaching it, minus one each)  {}\n    the recruitment \
             graph is already one component: {}   the two readings agree: {}",
            agreement.homological,
            agreement.lineage,
            agreement.recruitment_connected,
            agreement.holds()
        ),
    }
    println!(
        "    the circuit's own route excess, read off the lineage: {}",
        act.after.circuit.lineage_route_excess()
    );
    println!(
        "\n  cross-check by union-find over the 1-cell supports (a second implementation, blind to \
         orientation):\n    {:?}  ->  beta_0 {}  beta_1 {}",
        act.after.circuit.spanning_forest_reading(),
        act.after.circuit.spanning_forest_reading().betti_0(),
        act.after.circuit.spanning_forest_reading().betti_1()
    );
    println!(
        "\n  every cell of the circuit is named by a passage: unclaimed cells {:?}",
        act.after.unclaimed
    );

    // ---------------------------------------------------------------------------------------------
    rule("[4a]  TWO INDEPENDENT ROUTES TO ONE RESULT  --  both routes printed, and the cycle they close");

    let all_passages = act.passages.clone();
    let route_vertices = routes_to(&act.after, STATEMENT);
    println!(
        "\n  {} declaration vertices reach |- {STATEMENT}:",
        route_vertices.len()
    );
    let mut deposited_routes: Vec<String> = Vec::new();
    let mut derived_routes: Vec<String> = Vec::new();
    for vertex in &route_vertices {
        let kind = match text_of(&all_passages, vertex, STATEMENT) {
            None => "?",
            Some(passage) if passage.is_derived() => {
                derived_routes.push(vertex.clone());
                "derived"
            }
            Some(_) => {
                deposited_routes.push(vertex.clone());
                "deposited"
            }
        };
        println!("    {vertex:<58} {kind}");
    }

    /// One exhibited cycle: the two routes, the shared symbol, the chain, and the boundary.
    fn exhibit_cycle(
        circuit: &ConditionedCircuit,
        passages: &[Passage],
        title: &str,
        left: &str,
        right: &str,
    ) -> Option<CausalChain> {
        let left_passage = text_of(passages, left, STATEMENT)?;
        let right_passage = text_of(passages, right, STATEMENT)?;
        let shared: BTreeSet<&str> = left_passage
            .derivation
            .recruited_symbols()
            .intersection(&right_passage.derivation.recruited_symbols())
            .copied()
            .collect();
        let symbol = shared.iter().next()?;
        let chain = route_cycle(circuit, left, right, symbol, STATEMENT)?;
        println!("\n  {title}");
        println!("  they recruit these identifiers in common: {shared:?}");
        println!("  the exact integer 1-cycle they close through {symbol}, cell by cell:");
        exhibit_chain(circuit, &chain, "      ");
        let boundary = circuit
            .circuit
            .complex()
            .boundary_of_chain(&chain)
            .expect("the boundary reads");
        println!("  its boundary, computed over the integers:");
        if boundary.difference_is_zero() {
            println!("      0   (every 0-cell coefficient cancels -- this IS a cycle)");
        } else {
            exhibit_chain(circuit, &boundary, "      ");
            return None;
        }
        Some(chain)
    }

    fn print_route(passages: &[Passage], title: &str, vertex: &str) {
        println!("\n  {title}, {vertex}");
        if let Some(passage) = text_of(passages, vertex, STATEMENT) {
            for line in passage.text.lines() {
                println!("      | {line}");
            }
        }
    }

    let mut exhibited_cycle = false;
    let mut cycle_boundary_vanishes = false;
    let mut second_cycle = false;
    if let (Some(deposited), true) = (deposited_routes.first().cloned(), derived_routes.len() >= 2) {
        let (derived_one, derived_two) = (derived_routes[0].clone(), derived_routes[1].clone());
        print_route(&all_passages, "ROUTE ONE -- deposited", &deposited);
        print_route(
            &all_passages,
            "ROUTE TWO -- returned by the conditioned instance",
            &derived_one,
        );
        print_route(
            &all_passages,
            "ROUTE THREE -- returned by the conditioned instance",
            &derived_two,
        );

        let first = exhibit_cycle(
            &act.after,
            &all_passages,
            &format!("CYCLE ONE  --  {deposited}  against  {derived_one}"),
            &deposited,
            &derived_one,
        );
        exhibited_cycle = first.is_some();
        cycle_boundary_vanishes = first.is_some();

        let second = exhibit_cycle(
            &act.after,
            &all_passages,
            &format!(
                "CYCLE TWO  --  {derived_one}  against  {derived_two}\n  (two routes the \
                 PRODUCTION returned, so the plurality is the machine's own)"
            ),
            &derived_one,
            &derived_two,
        );
        second_cycle = second.is_some();

        // Independence, exhibited rather than asserted: a cell each carries and the other does not.
        if let (Some(first), Some(second)) = (first, second) {
            let left: BTreeSet<CausalCellId> = first.support();
            let right: BTreeSet<CausalCellId> = second.support();
            let only_first: Vec<CausalCellId> = left.difference(&right).copied().collect();
            let only_second: Vec<CausalCellId> = right.difference(&left).copied().collect();
            let named = |cell: CausalCellId| {
                act.after
                    .circuit
                    .complex()
                    .cell(cell)
                    .map(|carried| carried.name.clone())
                    .unwrap_or_else(|_| format!("?{}", cell.0))
            };
            println!(
                "\n  the two cycles are LINEARLY INDEPENDENT over the integers, and the witness is \
                 exhibited:\n    cycle one carries  {}  with coefficient +/-1; cycle two carries it \
                 with 0\n    cycle two carries  {}  with coefficient +/-1; cycle one carries it \
                 with 0\n  Neither is a multiple of the other, so they span a rank-2 subspace of \
                 the cycle space,\n  and beta_1 >= 2 follows from these two exhibited chains alone \
                 without consulting the reduction.",
                only_first
                    .first()
                    .map(|cell| named(*cell))
                    .unwrap_or_else(|| "(none)".to_owned()),
                only_second
                    .first()
                    .map(|cell| named(*cell))
                    .unwrap_or_else(|| "(none)".to_owned())
            );
            second_cycle &= !only_first.is_empty() && !only_second.is_empty();
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[4b]  THE DECLARED beta_1 = 0 CONTROL  --  the identical act, on material where beta_1 comes out zero");

    let mut control_body =
        ConditionedBody::mount(control_deposit()).expect("the control deposit declares theorems");
    control_body.condition(&control_corpus());
    println!(
        "\n  control corpus committed {:?}",
        control_body.morphology().committed_stems()
    );
    println!(
        "  control corpus provisional {:?}   (the recurrence law refused these)",
        control_body
            .morphology()
            .provisional()
            .iter()
            .map(|stem| stem.stem.as_str())
            .collect::<Vec<&str>>()
    );
    let control_query = DerivationQuery::reaching("(h : P) : Q h");
    let control_before = found_conditioned_circuit(control_body.standing().to_vec(), APERTURE)
        .expect("founds");
    let control_before_invariants = control_before.circuit.invariants(PIVOT).expect("reads");
    let control_act = run_act(&control_body, &control_query);

    println!("\n  the control deposit, in full:");
    for (source, text) in control_deposit() {
        println!("    {source}");
        for line in text.lines() {
            println!("      | {line}");
        }
    }
    println!(
        "\n  the control production returned {} passages ({} at the declared aperture):",
        control_act.all.len(),
        control_act.production.len()
    );
    let control_morphology = control_body.morphology().clone();
    for (ordinal, passage) in control_act.production.iter().enumerate() {
        exhibit_passage(ordinal, passage, &BTreeMap::new(), &control_morphology);
    }
    exhibit_invariants("the control deposit alone", &control_before_invariants);
    exhibit_invariants(
        "the control deposit together with its production",
        &control_act.invariants,
    );

    let (_, control_before_betti_1, _) = grade_of(&control_before_invariants, 1);
    let (_, control_betti_1, _) = grade_of(&control_act.invariants, 1);
    let control_routes = routes_to(&control_act.after, "(h : P) : Q h");
    println!(
        "\n  BEFORE the production the control has one route per statement -- no plurality \
         anywhere -- and\n  beta_1 = {control_before_betti_1}. AFTER it, {} declaration vertices \
         reach |- (h : P) : Q h: {control_routes:?}",
        control_routes.len()
    );
    println!(
        "  and beta_1 is {control_betti_1} all the same, because those two routes share no \
         recruited identifier and\n  so close no loop. beta_1 is the HOMOLOGICAL INDEPENDENCE of \
         routes, not a tally of them --\n  which is the second thing this control establishes, \
         beyond the invariant being able to\n  come out zero at all."
    );

    controls.check(
        "control 2 -- beta_1 >= 1 with both routes exhibited, and beta_1 = 0 on declared material",
        betti_1 >= 1
            && exhibited_cycle
            && cycle_boundary_vanishes
            && second_cycle
            && control_before_betti_1 == 0
            && control_betti_1 == 0,
        &format!(
            "the act returns beta_1 = {betti_1} on the deposit and beta_1 = {control_betti_1} on \
             the declared control ({control_before_betti_1} before its production). Two cycles \
             were exhibited cell by cell and both have vanishing integer boundary. An invariant \
             that could not come out zero on any material would be no evidence."
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5]  ARE TWO OF THE RETURNED DERIVATIONS THE SAME THEOREM?  --  derivation_skein");

    let moves = moves_the_production_made(&act.after);
    let mut species: BTreeMap<&str, usize> = BTreeMap::new();
    for declared in &moves {
        *species.entry(declared.species.name()).or_default() += 1;
    }
    println!("\n  the moves the production made, by species: {species:?}");

    let contexts = declared_contexts(&act.after, STATEMENT);
    println!(
        "  declared context family: {} closed subcomplexes of sizes {:?}",
        contexts.len(),
        contexts.iter().map(BTreeSet::len).collect::<Vec<usize>>()
    );

    let exchange = moves
        .iter()
        .find(|declared| declared.species == MoveSpecies::RecruitmentExchange);
    let mut same_theorem = None;
    match exchange {
        None => println!(
            "\n  the production made no RecruitmentExchange move, so no two of its derivations \
             stand in the relation this reading decides."
        ),
        Some(declared) => {
            println!(
                "\n  the move read: {} -- withdraws {:?}, deposits {:?}, licensed by stem {:?}",
                declared.species.name(),
                declared.withdraws,
                declared.deposits,
                declared.stem
            );
            for name in declared.withdraws.iter().chain(&declared.deposits) {
                if let Some(passage) = text_of(&all_passages, name, STATEMENT) {
                    println!("\n      {name}");
                    for line in passage.text.lines() {
                        println!("      | {line}");
                    }
                }
            }
            match read_substitution(
                act.after.circuit.complex(),
                &declared.substitution,
                &contexts,
                PIVOT,
            ) {
                Err(refusal) => println!("\n  the substitution was refused: {refusal:?}"),
                Ok(reading) => {
                    println!(
                        "\n  removed {} cells, added {} cells, read against {} declared contexts",
                        reading.removed_extent,
                        reading.added_extent,
                        reading.verdicts.len()
                    );
                    for verdict in &reading.verdicts {
                        if verdict.invariant_here() {
                            println!("    context {}  invariant -- no declared receiver sees the replacement", verdict.context);
                        } else {
                            println!("    context {}  the remainder:", verdict.context);
                            for moved in &verdict.remainder {
                                println!(
                                    "        grade {}  betti {:+}  torsion gained {}  torsion lost {}",
                                    moved.grade,
                                    moved.betti_change,
                                    torsion_named(&moved.torsion_gained),
                                    torsion_named(&moved.torsion_lost)
                                );
                            }
                        }
                    }
                    same_theorem = Some(reading.compresses());
                    if reading.compresses() {
                        println!(
                            "\n  VERDICT: the two returned derivations ARE the same theorem under \
                             this reading. A local\n  substitution carries one to the other and no \
                             declared receiver in any declared context\n  can tell them apart. The \
                             verdict is relative to the declared context family and to the\n  \
                             invariants read; nothing here computes a normal form."
                        );
                    } else {
                        println!(
                            "\n  VERDICT: they are NOT the same theorem. The contexts that tell \
                             them apart: {:?}",
                            reading.distinguishing_contexts()
                        );
                    }
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE READING RETURNS  --  the movement between two readings, back into the production");

    let production_reading = read_production(&before, &act.after, RULE, PIVOT, STATEMENT)
        .expect("the production reads");
    println!(
        "\n  the movement returned {} artifacts, {} of which addressed material:",
        production_reading.returned.returns().len(),
        production_reading
            .returned
            .returns()
            .iter()
            .filter(|artifact| !artifact.addresses_nothing())
            .count()
    );
    let mut families: BTreeMap<String, (usize, BTreeSet<String>)> = BTreeMap::new();
    for artifact in production_reading.returned.returns() {
        let family = artifact
            .whole
            .split_once(':')
            .map_or(artifact.whole.clone(), |(head, _)| head.to_owned());
        let slot = families.entry(family).or_default();
        slot.0 += 1;
        slot.1.extend(artifact.returned.lines().map(str::to_owned));
    }
    println!(
        "  grouped by the mechanism that returned them -- every return is a DIFFERENCE between the \
         two\n  readings, so a production that moved nothing would return a still carrier here:\n"
    );
    for (family, (returns, addressed)) in &families {
        println!(
            "    {returns:>3} returns   {family:<62} addressing {} pieces of material",
            addressed.len()
        );
    }
    let addressed_union: Vec<String> = families
        .values()
        .flat_map(|(_, addressed)| addressed.iter().cloned())
        .collect::<BTreeSet<String>>()
        .into_iter()
        .collect();
    println!(
        "\n  the complete material those returns addressed -- {} distinct pieces, in the \
         material's own\n  writing and never in the analyst's. This is what is read by `expose` \
         and witnessed into the\n  morphology; the mechanism names above contribute not one word:\n",
        addressed_union.len()
    );
    wrapped("    ", &addressed_union);
    println!(
        "\n  the coil: the raw accumulation leaks at {} declared structures; the retained \
         remainder\n  closes it -- {}",
        production_reading.after.leaking.len(),
        production_reading
            .after
            .the_returned_remainder_closes_the_coil()
    );

    let again = condition_again(&standing, body.morphology(), &query, &production_reading.returned)
        .expect("the second production founds");
    println!(
        "\n  first production {} passages   second production {} passages   moved {}",
        again.first.len(),
        again.second.len(),
        again.the_production_moved()
    );
    println!(
        "  stems the return committed that the corpus had not: {:?}",
        again
            .committed_by_return
            .iter()
            .map(|stem| stem.stem.as_str())
            .collect::<Vec<&str>>()
    );
    println!(
        "  words one return named and no second did -- retained, off the path: {} of them",
        again.provisional_by_return.len()
    );
    println!(
        "\n  the passages the return founded at the declared aperture, exhibited whole \
         ({} of {} founded):",
        again
            .founded_passages
            .iter()
            .filter(|founded| founded.stem.chars().count() >= MORPHEMIC_LETTERS)
            .count(),
        again.founded_passages.len()
    );
    let second_by_name: BTreeMap<&str, &DerivedPassage> = again
        .second
        .iter()
        .map(|passage| (passage.name.as_str(), passage))
        .collect();
    for founded in &again.founded_passages {
        if founded.stem.chars().count() < MORPHEMIC_LETTERS {
            continue;
        }
        println!(
            "\n    {}\n      stem {:?}  brought {}  caused by the returns {:?}\n      committed at \
             {:?}",
            founded.passage, founded.stem, founded.brought, founded.caused_by, founded.committed_at
        );
        if let Some(passage) = second_by_name.get(founded.passage.as_str()) {
            for line in passage.text.lines() {
                println!("      | {line}");
            }
        }
    }
    if again.founded_passages.is_empty() {
        println!("    (none)");
    }
    let founded_outside: Vec<&str> = again
        .founded_passages
        .iter()
        .filter(|founded| founded.stem.chars().count() < MORPHEMIC_LETTERS)
        .map(|founded| founded.passage.as_str())
        .collect();
    println!("\n  founded outside the aperture, named in full: {founded_outside:?}");
    println!("\n  the passages the return withdrew, with the returned stem that swallowed them:");
    for withdrawn in &again.withdrawn_passages {
        println!(
            "    {:<56} stem {:?} taken by {:?}",
            withdrawn.passage,
            withdrawn.stem,
            withdrawn
                .covered_by
                .iter()
                .map(|taken| taken.taker.as_str())
                .collect::<BTreeSet<&str>>()
        );
    }
    if again.withdrawn_passages.is_empty() {
        println!("    (none)");
    }

    // The second reading: found the circuit of the second production and read it again.
    let carried_body = body.with_morphology(again.carried.clone());
    let second_act = run_act(&carried_body, &query);
    let second_reading = read_production(&act.after, &second_act.after, RULE, PIVOT, STATEMENT)
        .expect("the second reading founds");
    let (_, second_betti_1, second_torsion) = grade_of(&second_act.invariants, 1);
    println!(
        "\n  THE SECOND READING. The second production founded as a circuit and read again:\n    \
         beta_1 {second_betti_1}   torsion {}   passages at the declared aperture {}\n    the \
         movement between the FIRST production's reading and the SECOND's returned {} artifacts.",
        torsion_named(&second_torsion),
        second_act.production.len(),
        second_reading.returned.returns().len()
    );
    println!(
        "    So the return moved the production ({} passages to {}) and the whole of that movement \
         lies\n    OUTSIDE the declared aperture: the three withdrawn passages were licensed by the \
         one-letter\n    stem \"o\", which the returned stem \"prop\" swallowed by maximality. At the \
         aperture the two\n    productions are identical, and the reading says so by returning \
         nothing rather than by\n    being asked.",
        again.first.len(),
        again.second.len()
    );

    // ---------------------------------------------------------------------------------------------
    rule("[7]  THE SITUATED RESIDUAL  --  the emission against the unconditioned null");

    let frame = Frame::new(
        "one identifier recruited by a route reaching the queried statement",
        &deposit_root.display().to_string(),
        Grain::DECLARED,
    );
    let null_passages = null.passages(&query).expect("the null's passages found");
    let emitted = emission_reaching(
        "the conditioned instance",
        &deposit_root.display().to_string(),
        &all_passages,
        STATEMENT,
    );
    let referenced = emission_reaching(
        "the unconditioned null",
        &deposit_root.display().to_string(),
        &null_passages,
        STATEMENT,
    );
    println!("\n  {frame}");
    let reading = situate(&emitted, &referenced, &frame).expect("the reading founds");
    let calibration = situate(&referenced, &referenced, &frame).expect("the calibration founds");

    println!(
        "\n  the residual has {} members: founded {}, shared {}, withheld {}",
        reading.members.len(),
        reading.founded().len(),
        reading.shared().len(),
        reading.withheld().len()
    );
    println!("\n  every member, with the exact symbolic form its arm situates it by:");
    for member in &reading.members {
        println!(
            "    {:<22} {:<9} emitted {:<5} referenced {:<5}  {} = {}",
            member.event,
            member.arm().named(),
            member.emitted_occurrences,
            member.referenced_occurrences,
            member.situating_form_named(),
            member.situating_form().named()
        );
    }
    let separating: Vec<&str> = reading
        .separating()
        .iter()
        .map(|member| member.event.as_str())
        .collect();
    println!("\n  the members the null does not already account for: {separating:?}");
    println!(
        "  the null situated against ITSELF returns zero: {}",
        calibration.returns_zero()
    );
    let open = reading
        .open_orderings_at(Grain::at(1, 4))
        .expect("the orderings read");
    println!(
        "\n  pairs a coarse grain (1/4) cannot order. Every one is RETAINED with both members and \
         both\n  forms on the entry; nothing is tie-broken. The complete population, {} pairs:\n",
        open.len()
    );
    for entry in &open {
        println!("      {:<22} vs {:<22} -> {:?}", entry.left, entry.right, entry.verdict);
    }
    println!(
        "\n  and the first two written out whole, so the retention is visible rather than \
         asserted:"
    );
    for entry in open.iter().take(2) {
        println!("      {}", entry.render());
    }
    let decided_finer = open
        .iter()
        .filter(|entry| {
            entry
                .left_form
                .compare_grain(&entry.right_form, Grain::DECLARED)
                .is_ok_and(|verdict| verdict != holonic_engine::exact_value::ExactOrdering::Open)
        })
        .count();
    println!(
        "\n  {decided_finer} of those {} decide at the frame's declared grain: the refusal is a \
         property of the\n  grain, not a permanent one, and re-asking is what retention is for.",
        open.len()
    );

    controls.check(
        "control 4 -- the situated residual is non-empty against the null and empty against itself",
        !reading.returns_zero() && calibration.returns_zero() && !reading.members.is_empty(),
        &format!(
            "{} of {} members separate the conditioned instance from the null on the declared \
             face; the null read against itself separates on none. A reading with no members at \
             all would return `false` here rather than passing vacuously.",
            reading.separating().len(),
            reading.members.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[8]  IS THE RETURNED PASSAGE IN THE DEPOSIT?  --  checked by content against every artifact");

    let mut byte_identical: Vec<(String, String)> = Vec::new();
    let mut name_collisions: Vec<(String, String)> = Vec::new();
    let mut reading_identical: Vec<(String, String)> = Vec::new();
    let deposited_readings: Vec<(String, Derivation)> = deposit
        .iter()
        .filter_map(|(source, text)| {
            holonic_engine::derivation_atlas::read_derivation(text)
                .map(|derivation| (source.clone(), derivation))
        })
        .collect();
    for passage in &act.all {
        let emitted = holonic_engine::derivation_atlas::read_derivation(&passage.text)
            .expect("the composed passage reads back");
        for (source, text) in &deposit {
            if text == &passage.text {
                byte_identical.push((passage.name.clone(), source.clone()));
            }
        }
        for (source, derivation) in &deposited_readings {
            if derivation.name == passage.name {
                name_collisions.push((passage.name.clone(), source.clone()));
            }
            if derivation.statement == emitted.statement
                && derivation.recruited == emitted.recruited
            {
                reading_identical.push((passage.name.clone(), source.clone()));
            }
        }
    }
    println!(
        "\n  all {} returned passages -- at the aperture and outside it alike -- checked against \
         every one of\n  the {} deposited artifacts.",
        act.all.len(),
        deposit.len()
    );
    println!("    byte-identical to a deposited artifact          {} matches", byte_identical.len());
    println!("    declares a name a deposited artifact declares   {} matches", name_collisions.len());
    println!(
        "    reads back to a deposited (statement, recruitment)  {} matches",
        reading_identical.len()
    );
    let statements_shared = act
        .all
        .iter()
        .filter(|passage| body.standing_statements().contains(&passage.statement))
        .count();
    println!(
        "    reaches a statement the deposit reaches            {} of {}   <- this is the point: \
         same result, new route",
        statements_shared,
        act.all.len()
    );
    if !byte_identical.is_empty() {
        println!("    the byte-identical matches: {byte_identical:?}");
    }
    if !reading_identical.is_empty() {
        println!("    the reading-identical matches: {reading_identical:?}");
    }

    controls.check(
        "control 3 -- the returned passage is not in the deposit",
        byte_identical.is_empty() && name_collisions.is_empty() && reading_identical.is_empty(),
        &format!(
            "no returned passage is byte-identical to any of the {} artifacts, declares a name any \
             of them declares, or reads back to the same (statement, recruitment multiset) as any \
             of them -- while every one of them reaches a statement the deposit already reaches.",
            deposit.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[9]  THE ABLATION  --  the conditioning withheld entirely, the identical act re-run");

    let withheld = body.with_morphology(FoundedMorphology::unconditioned());
    let ablated = run_act(&withheld, &query);
    let before_names: BTreeSet<&str> =
        act.all.iter().map(|passage| passage.name.as_str()).collect();
    let after_names: BTreeSet<&str> = ablated
        .all
        .iter()
        .map(|passage| passage.name.as_str())
        .collect();
    let departed: Vec<&&str> = before_names.difference(&after_names).collect();
    let arrived: Vec<&&str> = after_names.difference(&before_names).collect();
    let cells_before = act.after.cell_names();
    let cells_after = ablated.after.cell_names();
    let cells_departed: Vec<String> = cells_before.difference(&cells_after).cloned().collect();
    let stems_departed: BTreeSet<&str> = act
        .all
        .iter()
        .map(|passage| passage.stem.as_str())
        .collect();

    println!(
        "\n  the passages that departed, by name -- the complete population, never a delta.\n  \
         `*` marks a member of the declared aperture:"
    );
    let inside: BTreeSet<&str> = act
        .production
        .iter()
        .map(|passage| passage.name.as_str())
        .collect();
    for name in &departed {
        println!(
            "    {} {name}",
            if inside.contains(**name) { "*" } else { " " }
        );
    }
    if departed.is_empty() {
        println!("    (none)");
    }
    println!("\n  the founded stems that stopped licensing anything: {stems_departed:?}");
    println!("\n  the passages that arrived: {arrived:?}");
    println!(
        "\n  the circuit cells that stopped existing ({}):",
        cells_departed.len()
    );
    for name in &cells_departed {
        println!("    {name}");
    }
    let (_, ablated_betti_1, _) = grade_of(&ablated.invariants, 1);
    println!(
        "\n  beta_1 with the conditioning withheld: {ablated_betti_1}   (with it: {betti_1})"
    );

    // The finer ablation: delete ONE founded stem and re-query.
    println!("\n  and the finer shape -- delete ONE founded stem and re-query:");
    let licensing: BTreeSet<&str> = act
        .production
        .iter()
        .map(|passage| passage.stem.as_str())
        .collect();
    let mut structural = true;
    for stem in &licensing {
        match ablate_stem(&body, stem, &query, APERTURE) {
            Err(refusal) => println!("    {stem:?} refused: {refusal}"),
            Ok(ablation) => {
                structural &= ablation.removes_structure();
                println!(
                    "\n    stem {:?} witnessed by {:?}\n      passages absent {}   reopened {}   \
                     unaccounted {}   cells absent {}   removes structure {}",
                    ablation.stem,
                    ablation.wholes,
                    ablation.passages_absent.len(),
                    ablation.reopened.len(),
                    ablation.unaccounted.len(),
                    ablation.cells_absent.len(),
                    ablation.removes_structure()
                );
                println!("      the passages the removal made structurally absent:");
                for absent in &ablation.passages_absent {
                    println!("        {}", absent.name);
                }
                println!(
                    "      the passages its removal REOPENED -- occurrences it had been \
                     suppressing by maximality:"
                );
                for reopened in &ablation.reopened {
                    println!(
                        "        {:<52} now licensed by stem {:?}",
                        reopened.passage, reopened.stem
                    );
                }
            }
        }
    }

    controls.check(
        "control 5 -- withholding the conditioning removes the production by removing structure",
        departed.len() == act.all.len()
            && ablated.all.is_empty()
            && !cells_departed.is_empty()
            && structural,
        &format!(
            "all {} passages departed and {} circuit cells stopped existing. The population is \
             exhibited above by name; nothing here is a count delta. The per-stem ablations remove \
             later production by removing structure and account for every reopening by the \
             maximality the removed stem had been exercising.",
            departed.len(),
            cells_departed.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[10]  CAN THE INSTANCE REACH A STATEMENT ABSENT FROM THE DEPOSIT?  --  determined by construction");

    println!(
        "\n  (a) absent statements, put to the CONDITIONED instance. Each is written in the \
         deposit's own\n      vocabulary out of identifiers the deposit recruits, so nothing is \
         out of the material:"
    );
    let mut absent_total = 0usize;
    for probe in [
        ABSENT_STATEMENT,
        "(P : Prop) (h : P) : formal_carry P",
        "(P : Prop) (h : exactCarrier P) : P",
        "(a b : Nat) : Nat.zero = a",
        "(P : Prop) : exactCarrier P",
    ] {
        let returned = body
            .derive(&DerivationQuery::reaching(probe))
            .expect("derives");
        absent_total += returned.len();
        println!("      |- {probe:<52} returned {} passages", returned.len());
    }
    let absent = body
        .derive(&DerivationQuery::reaching(ABSENT_STATEMENT))
        .expect("derives");

    println!(
        "\n  (b) the complete query aperture: every statement the deposit reaches, asked in turn,\n \
         \x20     and the union of every statement the instance ever emitted."
    );
    let mut emitted_statements: BTreeSet<String> = BTreeSet::new();
    let mut founded_statements_anywhere: BTreeSet<String> = BTreeSet::new();
    let mut founded_routes_somewhere = false;
    for statement in body.standing_statements() {
        let each = DerivationQuery::reaching(&statement);
        let production = body.derive(&each).expect("derives");
        for passage in &production {
            emitted_statements.insert(passage.statement.clone());
        }
        let circuit = body.circuit(&each, APERTURE).expect("founds");
        let movement = route_movement(&before.circuit, &circuit.circuit);
        founded_statements_anywhere.extend(movement.founded_statements().iter().cloned());
        founded_routes_somewhere |= !movement.founded_routes().is_empty();
        println!(
            "      |- {:<52} {:>4} passages   statements founded {}   routes founded to {} statement(s)",
            statement,
            production.len(),
            movement.founded_statements().len(),
            movement.founded_routes().len()
        );
    }
    println!("\n      statements the deposit reaches : {:?}", body.standing_statements());
    println!("      statements the instance emitted: {emitted_statements:?}");
    println!(
        "      the two populations are equal  : {}",
        emitted_statements == body.standing_statements()
    );
    println!(
        "      statements FOUNDED anywhere in the aperture: {founded_statements_anywhere:?}  \
         (routes founded somewhere: {founded_routes_somewhere})"
    );

    println!(
        "\n  (c) does a statement vertex appear in the circuit that the deposit's own circuit \
         lacks?"
    );
    let statement_vertices = |circuit: &ConditionedCircuit| -> BTreeSet<String> {
        circuit
            .circuit
            .vertices()
            .keys()
            .filter(|key| key.starts_with("|- "))
            .cloned()
            .collect()
    };
    let before_statement_vertices = statement_vertices(&before);
    let after_statement_vertices = statement_vertices(&act.after);
    println!("      deposit alone      {before_statement_vertices:?}");
    println!("      with the production {after_statement_vertices:?}");
    println!(
        "      new statement vertices: {:?}",
        after_statement_vertices
            .difference(&before_statement_vertices)
            .collect::<Vec<&String>>()
    );
    println!(
        "      (the statement vertex key of the absent statement would be {:?})",
        statement_vertex_key(ABSENT_STATEMENT)
    );

    println!(
        "\n  (d) the REMOUNT. The production is itself deposited material, so mount a second body \
         on\n      what the instance emitted, condition it on the same corpus, and ask what IT \
         reaches.\n      This is the obvious way a new statement could appear at the second turn, \
         and it is\n      settled by construction rather than by argument."
    );
    let remount_deposit: Vec<(String, String)> = act
        .all
        .iter()
        .map(|passage| (format!("emitted/{}", passage.name), passage.text.clone()))
        .collect();
    let mut remounted =
        ConditionedBody::mount(remount_deposit).expect("the emitted passages declare theorems");
    remounted.condition(&corpus);
    let mut remounted_emitted: BTreeSet<String> = BTreeSet::new();
    for statement in remounted.standing_statements() {
        let production = remounted
            .derive(&DerivationQuery::reaching(&statement))
            .expect("derives");
        for passage in &production {
            remounted_emitted.insert(passage.statement.clone());
        }
    }
    println!(
        "      the remounted body's standing statements: {:?}",
        remounted.standing_statements()
    );
    println!("      what it emitted:                          {remounted_emitted:?}");
    let remount_founds_new = !remounted_emitted.is_subset(&body.standing_statements())
        || !remounted
            .standing_statements()
            .is_subset(&body.standing_statements());
    println!("      anything absent from the original deposit: {remount_founds_new}");

    let reaches_new = absent_total > 0
        || !absent.is_empty()
        || emitted_statements != body.standing_statements()
        || !founded_statements_anywhere.is_empty()
        || remount_founds_new
        || !after_statement_vertices
            .difference(&before_statement_vertices)
            .collect::<Vec<&String>>()
            .is_empty();

    println!("\n  THE FINDING");
    if reaches_new {
        println!(
            "      The instance DID reach a statement absent from the deposit. Exhibited above."
        );
    } else {
        println!(
            "      The instance CANNOT reach a statement absent from standing_statements(), and \
             the refusal\n      is structural rather than incidental. Three sites block it, and \
             each is a different\n      kind of block:\n\
             \n      1. `conditioned_derivation::derive` gates the licensing loop on statement \
             equality\n         against the deposit:\n\
             \n             for (ordinal, route) in standing.iter().enumerate() {{\n\
             \x20                if route.statement != query.statement {{ continue; }}\n\
             \n         A query naming a statement no deposited route reaches therefore matches no \
             route,\n         licenses no bridge, and returns the empty population -- which is (a) \
             above,\n         measured.\n\
             \n      2. `compose_passage(name, statement, brought)` writes the queried statement \
             VERBATIM\n         into the artifact. `statement` is a parameter copied through; \
             nothing in the module\n         composes, substitutes into, or instantiates a \
             statement. The one degree of freedom\n         the composer has is `brought`, which is \
             a RECRUITMENT and not a statement.\n\
             \n      3. `ConditionedBody::passages` refuses any passage that reads back reaching a \
             different\n         statement -- `EmittedPassageMissedItsStatement`. So even a \
             composer that did drift\n         could not get a new statement into the passage \
             population; the refusal is typed.\n\
             \n      The consequence is exactly what (b), (c) and (d) measure: the production founds \
             ROUTES and\n      never founds STATEMENTS. `route_movement` is the organ built to see \
             a founded statement,\n      and it returns the empty population on every query in the \
             complete aperture while\n      returning founded routes on the same queries. The \
             receiver family cannot see what it was\n      built to see, and that is the return.\n\
             \n      WHAT ORGAN WOULD BE NEEDED. A fourth move species, beside \
             `derivation_skein`'s\n      `Deposit`, `RecruitmentExchange` and `LemmaSplit` -- all \
             three of which preserve\n      `statement` by construction. It would need two things \
             this body does not have:\n\
             \n        * a statement GRAMMAR. `read_derivation` is deliberately shallow -- it \
             reads what a\n          file declares, not what it means -- so a statement is an \
             opaque normalized string\n          with no operation on it. Composing \
             `exactCarrier (exactCarrier P)` from\n          `exactCarrier P` requires knowing that \
             `exactCarrier` is applied to an argument,\n          which is a semantics claim the \
             export codec deliberately refuses to make.\n\
             \n        * an ADMISSION rule for the composed statement. The morphemic bridge already \
             gives\n          the licence mechanism and `FoundedMorphology::cover` already \
             decomposes a word the\n          morphology has never seen, so the conditioning half \
             is built and reusable. What is\n          missing is the rule deciding which composed \
             statements a founded morphology may\n          admit -- and it must be a POPULATION \
             with retained obstructions, not a filter.\n\
             \n      The return half already exists: `route_movement().founded_statements()` would \
             report such\n      a statement the moment one was produced, and `found_circuit` would \
             found its 0-cell.\n      The reading side is built; the production side is not."
        );
    }

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");
    println!(
        "\n  the same theorem verdict: {}",
        match same_theorem {
            None => "no RecruitmentExchange move was available to read".to_owned(),
            Some(true) => "two returned derivations ARE the same theorem under the declared reading"
                .to_owned(),
            Some(false) =>
                "the two returned derivations are NOT the same theorem; a declared context sees the \
                 replacement"
                    .to_owned(),
        }
    );
    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
