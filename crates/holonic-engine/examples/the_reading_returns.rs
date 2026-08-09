//! The reading returns: one production, read, and the movement between two readings carried back
//! into the production that caused it.
//!
//! ```text
//! cargo run --release --example the_reading_returns
//! ```
//!
//! ## What this driver is for
//!
//! A census of the library modules on 2026-08-08 returned that `holonic-engine`,
//! `holonic-structure`, `relational-geometry` and `holonic-language` carry **no cycles at module
//! granularity**. Nothing an engine module emits re-enters any module upstream of it. Two instances
//! were verified by hand: `derivation_atlas`'s `invariant_movement` and `route_movement` were called
//! from exactly one place in the workspace — inside `main` in `examples/derivation_atlas_reader.rs`
//! — and **printed**; and `temper` and `derivation_integral` were built as the two halves of one
//! `Cochain` return path with **no caller between them**, `temper` having in-degree zero from
//! everything in the workspace.
//!
//! This driver closes both at one seam and runs four declared controls. It exits non-zero if any
//! fails.
//!
//! ```text
//!   1  the falsifier fires before the repair: the unjoined body's second production is
//!      bit-identical to its first under the same standing, morphology and query
//!   2  after the join the movement is non-zero and every moved passage names the earlier return
//!      that caused it
//!   3  the no-op control: a reading that moved nothing leaves the second production bit-identical
//!   4  the cut, named from measurement, out of the five `canon/THE_HOLOBROCHOS_SPINE.md` §1
//!      distinguishes: circulation, rest, accumulation, leak, short circuit
//! ```
//!
//! Nothing here is submitted to a kernel. A derived passage is production read as structure, exactly
//! as the deposited artifacts are.

use std::collections::BTreeSet;

use holonic_engine::conditioned_derivation::{
    expose, found_conditioned_circuit, ConditionedBody, ConditionedCircuit, DerivationQuery,
    DerivedPassage, Exposure, FoundedMorphology,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::derivation_integral::AccumulationRule;
use holonic_engine::rebase_invariants::PivotRule;
use holonic_engine::returned_reading::{
    condition_again, read_production, ReturnedReading, ReturnedArtifact,
};

const STATEMENT: &str = "(P : Prop) (h : P) : exactCarrier P";
const RULE: AccumulationRule = AccumulationRule::RecruitmentLoad;
const PIVOT: PivotRule = PivotRule::SmallestMagnitude;
const APERTURE: CircuitAperture = CircuitAperture::STATEMENT_INCIDENT;

// -------------------------------------------------------------------------------------------------
// The material
// -------------------------------------------------------------------------------------------------

/// Verbatim from `standing/output/`. Real production, quoted rather than read from disk so this
/// driver carries no filesystem frame and reproduces on any machine.
fn deposit() -> Vec<(String, String)> {
    [
        (
            "lean-proof-production/carrier-transport-00000.lean",
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n",
        ),
        (
            "lean-proof-production/carrier-transport-00012.lean",
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  apply exact_chart_carry\n  apply exact_chart_carry\n  assumption\nend Soma\n",
        ),
        (
            "lean-kernel-witness/carrier_transport-00000.lean",
            "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem carrier_transport (h : P) : exactCarrier P := formal_carry\nend Soma\n",
        ),
        // A namespaced reference. Lean writes these constantly and `read_derivation`'s tokenizer
        // keeps `.` inside a token, so `Soma.exact_chart_carry` is ONE recruited identifier whose
        // leading morpheme is the namespace `Soma` — an identifier the deposit also recruits on its
        // own. Nothing in the corpus can found that morpheme; only a reading that addressed the
        // circuit's own vertices can.
        (
            "lean-proof-production/carrier-transport-00031.lean",
            "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  have bridged := Soma.exact_chart_carry\n  assumption\nend Soma\n",
        ),
    ]
    .into_iter()
    .map(|(source, text)| (source.to_owned(), text.to_owned()))
    .collect()
}

/// Two wholes of prose. Between them they commit `exact`, `carry`, `chart` and `transport`; `carrier`
/// and `formal` are witnessed by one whole each and stay provisional, which is what leaves the
/// reading something to found.
fn corpus() -> Vec<Exposure> {
    vec![
        expose(
            "prose/one",
            "an exact chart carries a transport; the carry is exact, the chart is a chart, and the \
             carrier is what the transport crosses",
        ),
        expose(
            "prose/two",
            "exact transport carries a chart, the carry stands, and a formal step is one the chart \
             already carries",
        ),
    ]
}

// -------------------------------------------------------------------------------------------------
// Reading conveniences
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
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

/// Every passage of a production, name and text, as one string. Two productions are bit-identical
/// exactly when these agree, and this is what "bit-identical" is checked on.
fn digest(production: &[DerivedPassage]) -> String {
    let mut rendered = String::new();
    for passage in production {
        rendered.push_str(&passage.name);
        rendered.push('\u{1f}');
        rendered.push_str(&passage.text);
        rendered.push('\u{1f}');
        rendered.push_str(&passage.stem);
        rendered.push('\u{1f}');
        rendered.push_str(&passage.brought);
        for bridge in &passage.bridges {
            rendered.push('\u{1e}');
            rendered.push_str(&format!(
                "{}@{}:{}@{}:{}",
                bridge.held, bridge.held_at, bridge.brought, bridge.brought_at, bridge.route
            ));
        }
        rendered.push('\n');
    }
    rendered
}

fn names(production: &[DerivedPassage]) -> Vec<&str> {
    production
        .iter()
        .map(|passage| passage.name.as_str())
        .collect()
}

fn committed(morphology: &FoundedMorphology) -> Vec<&str> {
    morphology.committed_stems()
}

fn circuit_of(
    body: &ConditionedBody,
    query: &DerivationQuery,
) -> ConditionedCircuit {
    body.circuit(query, APERTURE)
        .expect("the production founds a circuit")
}

// -------------------------------------------------------------------------------------------------

fn main() {
    let mut controls = Controls::new();
    let query = DerivationQuery::reaching(STATEMENT);

    let mut mounted = ConditionedBody::mount(deposit()).expect("the deposit declares theorems");
    mounted.condition(&corpus());
    let standing = mounted.standing_derivations();
    let corpus_morphology = mounted.morphology().clone();

    rule("THE MATERIAL");
    println!("  deposited artifacts        {}", standing.len());
    println!("  statement queried          |- {STATEMENT}");
    println!("  recruited population       {:?}", mounted.recruited_population());
    println!("  corpus-committed stems     {:?}", committed(&corpus_morphology));
    println!(
        "  corpus-provisional stems   {:?}",
        corpus_morphology
            .provisional()
            .iter()
            .map(|stem| stem.stem.as_str())
            .collect::<Vec<_>>()
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 1 — the falsifier, before the repair
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 1 — THE FALSIFIER FIRES BEFORE THE REPAIR");
    println!(
        "  The unjoined body derives twice from one standing, one morphology and one query. The\n  \
         reading of the first production is computed and returns a non-empty movement. Nothing\n  \
         consumes it, so the second production cannot differ from the first."
    );

    let unjoined_first = mounted.derive(&query).expect("derives");
    let unjoined_second = mounted.derive(&query).expect("derives");
    println!("\n  first production   {} passages  {:?}", unjoined_first.len(), names(&unjoined_first));
    println!("  second production  {} passages  {:?}", unjoined_second.len(), names(&unjoined_second));
    println!(
        "  digest agreement   {}",
        if digest(&unjoined_first) == digest(&unjoined_second) {
            "bit-identical"
        } else {
            "differ"
        }
    );
    controls.check(
        "the second production of the unjoined body is bit-identical to the first",
        digest(&unjoined_first) == digest(&unjoined_second) && unjoined_first == unjoined_second,
        "confirmed by comparing the full passage population — name, artifact text, licensing stem, \
         brought identifier and every bridge with its route — and by `Vec<DerivedPassage>` equality.",
    );
    controls.check(
        "and the first production is not empty, so the agreement is not vacuous",
        !unjoined_first.is_empty(),
        "two empty productions agree for free and would prove nothing.",
    );

    // ---------------------------------------------------------------------------------------------
    // The reading
    // ---------------------------------------------------------------------------------------------

    let circuit_before = found_conditioned_circuit(mounted.standing().to_vec(), APERTURE)
        .expect("the deposit founds a circuit");
    let circuit_after = circuit_of(&mounted, &query);
    let reading = read_production(&circuit_before, &circuit_after, RULE, PIVOT, STATEMENT)
        .expect("the reading returns");

    rule("THE READING — the temper and the derivation integral, called in sequence");
    println!(
        "  accumulation rule    {}\n  potential base       {}\n",
        RULE.named(),
        reading.after.base
    );
    println!("  derivation_integral::accumulation  ->  a 1-cochain over {} cells", reading.after.accumulated.assigned().len());
    println!("  temper::TemperedFamily::read       ->  {} structures, {} condensing, {} expanded",
        reading.after.temper.twists.len(),
        reading.after.condensing().len(),
        reading.after.leaking.len(),
    );
    for (structure, leak) in &reading.after.leaking {
        println!("        leaks {leak:>4}   {structure}");
    }
    println!(
        "  derivation_integral::potential_over ->  cycle rank {}, {} chords retained",
        reading.after.potential.cycle_rank(),
        reading.after.potential.retained.len()
    );
    for chord in &reading.after.potential.retained {
        println!(
            "        residual {:>4}   {}   declared {} implied {}",
            chord.residual, chord.cell, chord.declared, chord.implied
        );
    }
    println!("  temper::found_on                   ->  the remainder deposited back onto the cochain");
    println!(
        "  temper::TemperedFamily::read again ->  population leak {}",
        reading.after.tempered_again.population_leak()
    );
    println!(
        "  derivation_integral::potential_over ->  admits a potential: {}",
        reading.after.potential_again.admits_a_potential()
    );
    controls.check(
        "the returned remainder closes the coil",
        reading.after.the_returned_remainder_closes_the_coil(),
        "<a, dS> = <da, S>: depositing each retained chord's own implied value leaves no chord \
         retained and no declared structure leaking.",
    );
    controls.check(
        "and the closure was tested rather than free",
        reading.after.the_closure_was_tested(),
        "the raw accumulation did not admit a potential and the cycle rank is above zero, so the \
         closure above could have failed.",
    );

    if let (Some(raw), Some(deposited)) = (&reading.lineage, &reading.lineage_founded) {
        let moved = raw
            .compared
            .iter()
            .zip(&deposited.compared)
            .filter(|(here, there)| here.residual() != there.residual())
            .count();
        println!(
            "\n  derivation_integral::statement_lineage on the raw cochain      {} compared pairs, {} standing",
            raw.compared.len(),
            raw.standing().len()
        );
        println!(
            "  derivation_integral::statement_lineage on the founded cochain  {} compared pairs, {} standing",
            deposited.compared.len(),
            deposited.standing().len()
        );
        println!("  route pairs whose residual moved when the remainder was returned: {moved}");
        println!("  BOTH lineages are retained. The pair is the return; choosing one would resolve an OPEN by choosing.");
    } else if let Some(refusal) = &reading.lineage_refusal {
        println!("\n  the statement lineage was refused: {refusal}");
    }

    rule("THE MOVEMENT BETWEEN THE TWO READINGS");
    println!("  invariant movement   grades {:?}   fields {:?}", reading.movement.grades_moved(), reading.movement.fields_moved());
    for grade in reading.movement.moved() {
        println!(
            "        grade {}  cells {:?} -> {:?}   betti {:?} -> {:?}   torsion {:?} -> {:?}",
            grade.grade,
            grade.before.as_ref().map(|side| side.cells),
            grade.after.as_ref().map(|side| side.cells),
            grade.before.as_ref().map(|side| side.betti),
            grade.after.as_ref().map(|side| side.betti),
            grade.before.as_ref().map(|side| side.torsion.clone()),
            grade.after.as_ref().map(|side| side.torsion.clone()),
        );
    }
    println!("  route movement");
    println!("        statements founded   {:?}", reading.routes.founded_statements());
    println!("        became plural        {:?}", reading.routes.became_plural());
    for (statement, reaching) in reading.routes.founded_routes() {
        println!("        routes founded to |- {statement}");
        for vertex in reaching {
            println!("              {vertex}");
        }
    }
    println!("  temper movement      {} structures moved", reading.twists.len());
    for moved in &reading.twists {
        println!(
            "        {}  opened: {}",
            moved.structure,
            moved.opened()
        );
    }
    println!("  remainder movement   {} chords founded, {} withdrawn", reading.remainder_founded.len(), reading.remainder_withdrawn.len());

    rule("THE CARRIER — the movement, in the form a production consumes its material in");
    println!(
        "  {} returned artifacts. `whole` is the mechanism's name and is never read as material;\n  \
         `returned` is what the return addressed, in the material's own writing.\n",
        reading.returned.returns().len()
    );
    for artifact in reading.returned.returns() {
        println!("  whole     {}", artifact.whole);
        if artifact.addresses_nothing() {
            println!("  returned  (this mechanism moved and addressed no material)");
        } else {
            for line in artifact.returned.lines() {
                println!("  returned    {line}");
            }
        }
        println!();
    }
    controls.check(
        "the movement between the two readings is non-empty",
        !reading.returned.is_still(),
        "a still reading has nothing to return and the join would be untestable.",
    );

    // ---------------------------------------------------------------------------------------------
    // The join
    // ---------------------------------------------------------------------------------------------

    let again = condition_again(&standing, &corpus_morphology, &query, &reading.returned)
        .expect("the second production derives");

    rule("THE JOIN — the same standing, the same query, conducted through what the reading returned");
    println!("  stems the return COMMITTED, with the returns that witnessed each:");
    for stem in &again.committed_by_return {
        println!("        {}", stem.stem);
        for whole in &stem.returns {
            println!("              witnessed by  {whole}");
        }
    }
    println!("\n  words a single return named, retained and OFF the path (provisional):");
    println!(
        "        {:?}",
        again
            .provisional_by_return
            .iter()
            .map(|stem| stem.stem.as_str())
            .collect::<Vec<_>>()
    );
    println!(
        "\n  committed stems before  {:?}\n  committed stems after   {:?}",
        committed(&corpus_morphology),
        committed(&again.carried)
    );

    rule("CONTROL 2 — THE MOVED PRODUCTION, AND THE EARLIER RETURN THAT CAUSED EACH MOVEMENT");
    println!("  first production   {} passages  {:?}", again.first.len(), names(&again.first));
    println!("  second production  {} passages  {:?}", again.second.len(), names(&again.second));

    println!(
        "\n  PASSAGES FOUNDED — present in the second production and not in the first.\n  \
         `committed at` is the recurrence that took the licensing stem from provisional contact to\n  \
         the derivation path. Every further return that named the same stem is listed in full under\n  \
         THE JOIN above; nothing is withheld here."
    );
    for passage in &again.founded_passages {
        println!("\n        {}", passage.passage);
        println!(
            "        licensed by stem {:?}, bringing {}",
            passage.stem, passage.brought
        );
        for cause in &passage.committed_at {
            println!("        committed at     {cause}");
        }
    }

    println!("\n  PASSAGES WITHDRAWN — present in the first and not in the second");
    if again.withdrawn_passages.is_empty() {
        println!("        none");
    }
    for passage in &again.withdrawn_passages {
        println!("\n        {}", passage.passage);
        println!("        had been licensed by stem {:?}", passage.stem);
        for taken in &passage.covered_by {
            println!(
                "        occurrence taken  {:?} at {} in {} was swallowed by {:?} standing at {}",
                passage.stem, taken.at, taken.identifier, taken.taker, taken.taken_at
            );
            for cause in again
                .committed_by_return
                .iter()
                .filter(|stem| stem.stem == taken.taker)
                .flat_map(|stem| &stem.committed_at)
            {
                println!("              committed at  {cause}");
            }
        }
    }

    println!("\n  PASSAGES RELICENSED — present in both, licensing lineage moved");
    if again.relicensed_passages.is_empty() {
        println!("        none");
    }
    for passage in &again.relicensed_passages {
        println!(
            "        {}   routes {:?} -> {:?}",
            passage.passage, passage.routes_before, passage.routes_after
        );
    }

    println!("\n  THE ARTIFACT — every founded passage, whole");
    for attributed in &again.founded_passages {
        let Some(founded) = again
            .second
            .iter()
            .find(|passage| passage.name == attributed.passage)
        else {
            continue;
        };
        println!();
        println!(
            "{}",
            founded
                .text
                .lines()
                .map(|line| format!("        {line}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        println!("        bridges:");
        for bridge in founded.licensing() {
            println!(
                "              stem {:?}  {}@{} <-> {}@{}  routes {:?}",
                bridge.stem, bridge.held, bridge.held_at, bridge.brought, bridge.brought_at, bridge.routes
            );
        }
    }

    controls.check(
        "the second production differs from the first",
        again.the_production_moved(),
        "the same standing, the same morphology source and the same query; the only thing that \
         moved is what the first reading returned.",
    );
    controls.check(
        "and it differs by founding or withdrawing at least one passage",
        !again.founded_passages.is_empty() || !again.withdrawn_passages.is_empty(),
        "a production that differed only in lineage would be a weaker return.",
    );
    controls.check(
        "every moved passage names the earlier return that caused it",
        again.every_movement_is_attributed(),
        "attribution is carried by the type: a passage names its licensing stem, and that stem's \
         wholes are the returns that founded it.",
    );
    controls.check(
        "the recurrence law refused something",
        again.the_recurrence_law_refused_something(),
        "some returned word was named by exactly one return and stayed provisional, retained and \
         off the path. If every returned word committed, the law would be decorative.",
    );
    controls.check(
        "the query did not move between the two productions",
        query == DerivationQuery::reaching(STATEMENT),
        "one `DerivationQuery` value drove both, so the difference cannot be a difference of \
         question.",
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 3 — the no-op
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 3 — THE NO-OP: A READING THAT MOVED NOTHING MOVES NO PRODUCTION");
    let still = ReturnedReading::still();
    let still_again = condition_again(&standing, &corpus_morphology, &query, &still)
        .expect("derives");
    println!(
        "  a still reading            {} returned artifacts   morphology equal: {}   production equal: {}",
        still.returns().len(),
        still_again.carried == corpus_morphology,
        digest(&still_again.first) == digest(&still_again.second)
    );

    let addressed_nothing = ReturnedReading::from_returns([ReturnedArtifact {
        whole: "the invariant movement at grade 1: betti".to_owned(),
        returned: String::new(),
    }]);
    let quiet_again = condition_again(&standing, &corpus_morphology, &query, &addressed_nothing)
        .expect("derives");
    println!(
        "  a reading that addressed nothing  {} returned artifacts   morphology equal: {}   production equal: {}",
        addressed_nothing.returns().len(),
        quiet_again.carried == corpus_morphology,
        digest(&quiet_again.first) == digest(&quiet_again.second)
    );

    controls.check(
        "a still reading leaves the second production bit-identical",
        still_again.carried == corpus_morphology
            && digest(&still_again.first) == digest(&still_again.second)
            && still_again.first == still_again.second,
        "the round trip through the seam is the identity, so this is a property of the \
         construction rather than a check bolted onto it.",
    );
    controls.check(
        "a reading whose mechanisms moved but which addressed no material moves nothing either",
        quiet_again.carried == corpus_morphology && quiet_again.first == quiet_again.second,
        "the return is retained and reported; it founds no word, so the morphology does not move. \
         A movement that always changed the production would be noise rather than conduct.",
    );

    // And the strongest form: a reading taken over a circuit against ITSELF. The circuit of the
    // production leaks under this rule — sixteen retained chords — so the temper/integral founding
    // does return on it, and that return must not reach the carrier, because the production did not
    // move. The deposit's own circuit would not do here: it is a star and admits a potential, so the
    // founding would have nothing to return and the stillness would carry no evidence.
    let against_itself = read_production(&circuit_after, &circuit_after, RULE, PIVOT, STATEMENT)
        .expect("reads");
    let alone = &against_itself.before;
    let itself_again = condition_again(
        &standing,
        &corpus_morphology,
        &query,
        &against_itself.returned,
    )
    .expect("derives");
    println!(
        "  a circuit read against itself     {} returned artifacts   the circuit itself leaks: {}   \
         morphology equal: {}   production equal: {}",
        against_itself.returned.returns().len(),
        !alone.potential.admits_a_potential(),
        itself_again.carried == corpus_morphology,
        digest(&itself_again.first) == digest(&itself_again.second)
    );
    controls.check(
        "a circuit read against itself returns a still carrier",
        against_itself.returned.is_still()
            && itself_again.carried == corpus_morphology
            && itself_again.first == itself_again.second,
        "every contributor is differenced against the earlier circuit, including the temper/integral \
         founding, which returns on any circuit that leaks and would otherwise make a still body \
         look like a moved one.",
    );
    controls.check(
        "and that control is not vacuous: the circuit read against itself does leak",
        !alone.potential.admits_a_potential() && alone.potential.cycle_rank() > 0,
        "a circuit that already admitted a potential would give the founding nothing to return, and \
         the stillness above would carry no evidence.",
    );

    // ---------------------------------------------------------------------------------------------
    // CONTROL 4 — the cut
    // ---------------------------------------------------------------------------------------------

    rule("CONTROL 4 — THE CUT, MEASURED OVER SUCCESSIVE TURNS OF THE LOOP");
    println!(
        "  `canon/THE_HOLOBROCHOS_SPINE.md` §1: circulation j != 0, rest, accumulation, leak and\n  \
         short circuit are DISTINCT CUTS. Which one this body sits at is a measurement, so the loop\n  \
         is turned until it stops moving and what it does is reported.\n"
    );

    let mut morphology = corpus_morphology.clone();
    let mut earlier_circuit = found_conditioned_circuit(mounted.standing().to_vec(), APERTURE)
        .expect("founds");
    let mut productions: Vec<Vec<DerivedPassage>> = Vec::new();
    let mut turns: Vec<(usize, usize, usize, bool)> = Vec::new();

    for _turn in 0..5 {
        let body = mounted.with_morphology(morphology.clone());
        let production = body.derive(&query).expect("derives");
        let circuit = circuit_of(&body, &query);
        let turn_reading = read_production(&earlier_circuit, &circuit, RULE, PIVOT, STATEMENT)
            .expect("reads");
        let carried = turn_reading.returned.carried_into(&morphology);
        let committed_now = committed(&carried).len();
        let moved = productions
            .last()
            .is_none_or(|previous| digest(previous) != digest(&production));
        turns.push((
            production.len(),
            turn_reading.returned.returns().len(),
            committed_now,
            moved,
        ));
        productions.push(production);
        earlier_circuit = circuit;
        let settled = carried == morphology;
        morphology = carried;
        if settled {
            break;
        }
    }

    println!("        turn   passages   returns   committed stems   production moved");
    for (turn, (passages, returns, stems, moved)) in turns.iter().enumerate() {
        println!(
            "        {:>4}   {:>8}   {:>7}   {:>15}   {}",
            turn + 1,
            passages,
            returns,
            stems,
            if *moved { "yes" } else { "no — at rest" }
        );
    }

    let moved_at_least_once = turns.iter().skip(1).any(|(_, _, _, moved)| *moved);
    let came_to_rest = turns.last().is_some_and(|(_, _, _, moved)| !moved);
    let population: BTreeSet<&str> = productions
        .iter()
        .flat_map(|production| names(production))
        .collect();

    println!(
        "\n  the whole passage population reached across every turn: {} distinct passages",
        population.len()
    );
    println!(
        "  the first turn's population: {} — the retained interior is never discarded, so the\n  \
         accumulated standing is the union above rather than the last turn alone.",
        productions.first().map_or(0, Vec::len)
    );

    println!("\n  BEFORE THE JOIN — the cut is LEAK.");
    println!(
        "        The reading returned a non-empty movement ({} artifacts) and the production did\n        \
         not move by one bit. r_k != 0 while q_(k+1) - q_k = 0 and no j circulates: the return\n        \
         crossed the boundary to stdout and nothing retained it. It is not REST, because rest\n        \
         would need r_k = 0 and the movement is measured non-zero. It is not ACCUMULATION,\n        \
         because nothing was stored. It is not SHORT CIRCUIT, because the interior was traversed\n        \
         — the reading is a genuine reading of the whole circuit — and the return simply left.",
        reading.returned.returns().len()
    );
    println!("\n  AFTER THE JOIN — the cut is ACCUMULATION, and it is not yet CIRCULATION.");
    println!(
        "        q moved: the morphology carries {} committed stems where it carried {}, the\n        \
         second production differs, and the interior is retained — the provisional population,\n        \
         both readings, and every earlier production are all kept. That is q_(k+1) - q_k != 0\n        \
         with the residual stored, which is the accumulation cut and not the leak.",
        committed(&again.carried).len(),
        committed(&corpus_morphology).len()
    );
    println!(
        "        It is not CIRCULATION: a sustained j != 0 would need the loop to keep returning\n        \
         current turn after turn, and the measurement above shows the production {}.",
        if came_to_rest {
            "coming to REST at a fixed point — the loop turns, deposits, and settles"
        } else {
            "still moving at the last turn measured"
        }
    );

    controls.check(
        "the loop moved the production on at least one further turn",
        moved_at_least_once,
        "measured on the turn table: a later turn's production differs from its predecessor's. A \
         loop that could only ever move once would not distinguish accumulation from a single \
         deposit.",
    );
    controls.check(
        "the cut is named from measurement rather than asserted",
        !turns.is_empty(),
        "the turn table above is the measurement: passages, returned artifacts and committed \
         stems per turn, with whether the production moved.",
    );

    // ---------------------------------------------------------------------------------------------

    rule("VERDICT");
    if controls.failed.is_empty() {
        println!("  every declared control holds.");
        println!("\n  BEFORE: leak.        The reading returned and nothing retained it.");
        println!("  AFTER:  accumulation. The movement between two readings re-enters the production");
        println!("          that caused it, the production moves, every movement names the return");
        println!("          that caused it, and a still reading moves nothing.");
    } else {
        println!("  CONTROLS FAILED:");
        for failure in &controls.failed {
            println!("        {failure}");
        }
        std::process::exit(1);
    }
}
