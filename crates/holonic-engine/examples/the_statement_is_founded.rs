//! **The statement is founded.** A conditioned instance reaches a statement absent from the deposit.
//!
//! ```text
//! cargo run --release --example the_statement_is_founded -- \
//!     standing/output \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! ## The question
//!
//! `research/records/2026-08-08_THE_INSTANCE_FOUNDS_ROUTES_AND_NEVER_FOUNDS_STATEMENTS.md` §6
//! established **by construction** that the conditioned production founds routes and never founds
//! statements, and named what would be needed: a fourth move species with a **statement grammar**
//! and a **population-valued admission rule with retained obstructions**. Both now exist —
//! `holonic_engine::statement_grammar` and `holonic_engine::statement_composition` — and the
//! question this driver puts is:
//!
//! > *Can a body conditioned on linguistic material reach a statement the deposit does not carry,
//! > composed out of structure recovered from the deposit's own statements, licensed by a word the
//! > corpus committed — and can the circuit see it?*
//!
//! ## The defect this driver now answers, and what closed it
//!
//! It could, and what it reached was `exactCarrier apply`, `(a b : nlinarith) : a = b`,
//! `(P : simpa) (h : P) : exactCarrier P`. Forty-seven statements, all garbage, because the
//! composition founded from **formal grammar with nothing conditioning it**: every recruited
//! identifier into every recovered slot, admitted whenever the stem licence found the two in one
//! founded stem — and `P` and `apply` share the founded letter `p`.
//!
//! The stem licence is about the **contact**: these two identifiers belong together. It says nothing
//! about the **place**. The place is something the deposit's own reading already knows and the
//! composition was not asking: `apply` was only ever the head of a proof step, `Soma` only ever
//! named a scope, and `exactCarrier` is the only identifier the material ever stood in first
//! position of a statement's trailing region.
//!
//! `statement_composition::StatementPositionEcology` is that reading, and it is founded from two
//! things neither of which is authored:
//!
//! - **the position census** — every population `lean_development` returns at
//!   `DeclarationGrain::EveryTopLevelDeclaration`, plus the slot species `statement_grammar`
//!   recovers over **every** declaration's statement rather than the theorem statements alone;
//! - **the declared-shape cohort** — `def exactCarrier (P : Prop) : Prop` and
//!   `abbrev ExactRelay (Q : Prop) : Prop` normalize to one skeleton, so an identifier may stand
//!   where any member of its cohort stands. That is what carries `ExactRelay` — which the material
//!   never once put in a statement — into the head position `exactCarrier` occupies.
//!
//! The widening matters as much as the gate: `read_derivation` opens **one** declaration per
//! artifact, so `def exactCarrier` and `abbrev ExactRelay` were invisible to the composition that
//! was supposed to be conditioned on them.
//!
//! ## What is not weakened
//!
//! The three sites the record named all still hold and section [2] measures the first of them
//! directly: `derive` returns the **empty population** on every absent statement, exactly as it did.
//! Founding a statement is a species **beside** `derive`, never a loosening of it.
//!
//! ## The eight declared controls. The driver exits non-zero if any fails.
//!
//! ```text
//!   1  the falsifier still fires: `derive` alone returns the empty population on every absent
//!      statement, and a non-empty one on a standing statement
//!   2  a returned passage reaches a statement absent from standing_statements(), its statement
//!      0-cell appears in the circuit, and route_movement().founded_statements() reports it
//!   3  refusal is retained: at least one composed candidate is refused with its obstruction named
//!      and kept, and the admission admits neither everything nor nothing
//!   4  the unconditioned null founds nothing through the new species
//!   5  removing one founded stem removes founded routes by removing structure, and every
//!      reopening is accounted for by the maximality the removed stem was exercising
//!   6  the recovered grammar states its aperture, and a statement in the deposit's own vocabulary
//!      that it therefore cannot compose is exhibited
//!   7  the conditioning is a GAUGE and its orbit on this material is non-trivial: the two settings
//!      run over ONE candidate population and the statements the gate removes are exhibited by name
//!   8  the position licence is a conjunct and never a widener: every statement the gate admits is
//!      admitted without it, and the new obstruction species is retained with its material
//! ```
//!
//! ## What is not claimed
//!
//! Nothing here is submitted to a kernel, and nothing may be: `CLAUDE.md` §13 rule 2 refuses a
//! foreign process deciding what the body may construct. Section [7] states, structurally and
//! without shelling anything, which composed artifacts are in a state where a **batch** grade could
//! be run on them at all — every name resolving against a declaration the material itself wrote —
//! and it says in the same breath that name resolution is not type correctness and that the composed
//! body is not a proof. A founded statement is one this deposit's own grammar, morphology and
//! position ecology reach; it is not asserted to be true or provable. Nothing here bears on any
//! Millennium result.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    expose, found_conditioned_circuit, ConditionedBody, ConditionedCircuit, DerivationQuery,
    Exposure,
};
use holonic_engine::derivation_atlas::{
    route_movement, statement_vertex_key, CircuitAperture,
};
use holonic_engine::derivation_skein::{moves_the_production_made, DerivationMove, MoveSpecies};
use holonic_engine::lean_development::{join, read_development, DeclarationGrain};
use holonic_engine::statement_composition::{
    ablate_stem_for_statements_under, compose_in_scope, deposits_its_statement_vertex,
    found_statements, found_statements_under, passages_with_composed, statement_composition_moves,
    AdjudicatedCandidate, AdmittedStatements, ComposedPassage, CompositionSpecies, PositionGate,
    StatementAdmission, StatementPositionEcology,
};
use holonic_engine::statement_grammar::{recover, BodyReading, SlotSpecies};

const APERTURE: CircuitAperture = CircuitAperture::STATEMENT_INCIDENT;

/// The declared aperture on the licence: a founded stem of at least this many characters.
///
/// Four, and the figure is a **declaration of what is being exhibited in full**, not a bound
/// anything is compared against for admission. The population outside it is exhibited by name and is
/// recoverable by declaring those stems.
const MORPHEMIC_LETTERS: usize = 4;

/// The five absent statements the record put to the instance. Every one still returns nothing
/// through `derive`.
const ABSENT_STATEMENTS: [&str; 5] = [
    "(P : Prop) (h : P) : exactCarrier (exactCarrier P)",
    "(P : Prop) (h : P) : formal_carry P",
    "(P : Prop) (h : exactCarrier P) : P",
    "(a b : Nat) : Nat.zero = a",
    "(P : Prop) : exactCarrier P",
];

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

/// A candidate named by the statement it came from, the recovered site it acted at, and what it
/// brought. The statement ordinal is the deposit's own canonical order, printed in section [1], so
/// two candidates at the same offset of two different statements are never confused.
fn label(entry: &AdjudicatedCandidate, ordinals: &BTreeMap<&str, usize>) -> String {
    format!(
        "s{}:{}<-{}",
        ordinals
            .get(entry.candidate.from.as_str())
            .copied()
            .unwrap_or(usize::MAX),
        entry.candidate.site,
        entry.candidate.brought
    )
}

/// One admitted candidate as the artifact it founds: the statement, the recovered rule, the founded
/// structure that licensed it, and **every** composed artifact it presents.
fn exhibit(
    ordinal: usize,
    entry: &AdjudicatedCandidate,
    admitted: &AdmittedStatements,
    composed: &[ComposedPassage],
    ecology: &StatementPositionEcology,
) {
    println!("\n  ({ordinal})  |- {}", entry.candidate.statement);
    println!(
        "        composed from  |- {}   by {}   at the recovered site {}",
        entry.candidate.from,
        entry.candidate.species.name(),
        entry.candidate.site
    );
    println!("        the recovered rule that composed it:");
    println!("          {}", entry.candidate.rule);
    if let Some(rendered) = admitted.grammar.render(&entry.candidate.from) {
        println!("          the grammar's reading of the statement it came from: {rendered}");
    }
    let StatementAdmission::Admitted {
        licences,
        carried_aperture,
        stood_in,
    } = &entry.admission
    else {
        return;
    };
    println!(
        "        the founded structure that licensed it: {} held with {}",
        entry.candidate.held, entry.candidate.brought
    );
    for licence in licences {
        println!(
            "          stem {:?}  {} @{}  <-> {} @{}",
            licence.stem,
            entry.candidate.held,
            licence.held_at,
            entry.candidate.brought,
            licence.brought_at
        );
        println!("            founded by the corpus wholes: {}", licence.wholes.join(", "));
    }
    if !stood_in.is_empty() {
        let places: Vec<String> = stood_in.iter().map(ToString::to_string).collect();
        println!(
            "        the POSITION licence: the material stands {} at {}",
            entry.candidate.brought,
            places.join(", ")
        );
        if let Some(slot) = entry.candidate.slot {
            println!(
                "          and the composition puts it in {} position, which its declared-shape \
                 cohort {:?} was witnessed in",
                slot.name(),
                ecology.cohort(&entry.candidate.brought)
            );
        }
    }
    for bound in carried_aperture {
        println!("        the admission CARRIES this, which the grammar does not certify:");
        println!("          {bound}");
    }
    let declarations = entry.candidate.declarations.join(", ");
    println!("        the standing declarations whose routes it extends: {declarations}");
    let artifacts: Vec<&ComposedPassage> = composed
        .iter()
        .filter(|passage| {
            passage.statement == entry.candidate.statement
                && passage.site == entry.candidate.site
                && passage.brought == entry.candidate.brought
        })
        .collect();
    println!(
        "        the {} artifact(s) it presents, in full -- one per standing declaration and \
         licensing stem:",
        artifacts.len()
    );
    for artifact in artifacts {
        if !artifact.scope.is_empty() {
            println!(
                "        (the artifact carries {} founding line(s) the material wrote, so its own \
                 names resolve; complete: {})",
                artifact.scope.imports.len() + artifact.scope.founding.len(),
                artifact.scope.is_complete()
            );
        }
        for line in artifact.text.lines() {
            println!("        | {line}");
        }
        println!("        |");
    }
}

/// The whole-token population of one line, by `statement_grammar`'s own orthographic rule.
fn statement_tokens(text: &str) -> Vec<String> {
    text.split(|symbol: char| !(symbol.is_ascii_alphanumeric() || symbol == '_' || symbol == '.'))
        .filter(|token| {
            token
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        })
        .map(str::to_owned)
        .collect()
}

fn statement_vertices(circuit: &ConditionedCircuit) -> BTreeSet<String> {
    circuit
        .circuit
        .vertices()
        .keys()
        .filter(|key| key.starts_with("|- "))
        .cloned()
        .collect()
}

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
        std::process::exit(1);
    }

    let mut body = ConditionedBody::mount(deposit.clone()).expect("the deposit declares theorems");
    body.condition(&corpus);
    let null = ConditionedBody::mount(deposit.clone()).expect("the deposit declares theorems");

    // The same deposit, read at the grain that opens EVERY top-level declaration rather than one per
    // artifact. That widening is the whole construction: `def exactCarrier` and `abbrev ExactRelay`
    // are in the material and were invisible to the composition that was supposed to be conditioned
    // on it.
    let development = join(
        deposit
            .iter()
            .map(|(_, text)| read_development(text, DeclarationGrain::EveryTopLevelDeclaration))
            .collect(),
    );
    let ecology = StatementPositionEcology::found(&development, &deposit)
        .expect("the declarations carry statements a grammar can be recovered from");

    let mut controls = Controls::new();

    // ---------------------------------------------------------------------------------------------
    rule("THE QUESTION");
    println!(
        "\n  The production founds ROUTES and never founds STATEMENTS. That was established by\n  \
         construction on 2026-08-08 and it named what was missing: a statement GRAMMAR and a\n  \
         POPULATION-VALUED admission rule with retained obstructions. Both are built. Can the\n  \
         conditioned instance now reach a statement the deposit does not carry?"
    );
    println!(
        "\n  the mathematical deposit   {:<44} {} artifacts",
        deposit_root.display(),
        body.standing().len()
    );
    println!(
        "  the linguistic corpus      {:<44} {} wholes",
        corpus_root.display(),
        corpus.len()
    );
    println!("\n  the deposit reaches these statements:");
    for statement in body.standing_statements() {
        println!("    |- {statement}");
    }
    println!("\n  and recruits these identifiers:");
    wrapped(
        "    ",
        &body
            .recruited_population()
            .into_iter()
            .collect::<Vec<String>>(),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE RECOVERED GRAMMAR  --  founded from the deposit's own statements, never authored");

    // Three arms over one material. `historical` is the rule as the roadmap measured it: the narrow
    // recruited population and no position gate. `withheld` and `applied` share a candidate
    // population exactly -- the same recruited set, the same grammar, the same compositions -- and
    // differ only in whether the ecology is on the causal path. That pair is the ORBIT.
    let historical = found_statements(&body).expect("founds");
    let withheld =
        found_statements_under(&body, &ecology, PositionGate::Withheld).expect("founds");
    let founded = found_statements_under(&body, &ecology, PositionGate::Applied).expect("founds");
    let grammar = &founded.grammar;

    println!(
        "\n  the punctuation the population exhibits: {:?}",
        grammar.punctuation()
    );
    println!(
        "  every ordered pair whose depth never goes negative and ends at zero over EVERY statement:"
    );
    for (open, close) in grammar.balanced_pairs() {
        println!("    {open} ... {close}");
    }
    println!(
        "  -> the bracket pair is {:?}, recovered because exactly one pair qualifies",
        grammar.bracket()
    );
    println!(
        "\n  every character occurring EXACTLY ONCE at depth zero in EVERY statement: {:?}",
        grammar.separator_candidates()
    );
    println!(
        "  -> the separator is {:?}, and the split is the region before it and the region after",
        grammar.separator()
    );

    let ordinals: BTreeMap<&str, usize> = grammar
        .population()
        .iter()
        .enumerate()
        .map(|(at, statement)| (statement.as_str(), at))
        .collect();

    println!("\n  each statement, as the recovery reads it:");
    for (at, reading) in grammar.readings().iter().enumerate() {
        println!("\n    s{at}  |- {}", reading.statement);
        println!(
            "       {}",
            grammar
                .render(&reading.statement)
                .unwrap_or_else(|| "(no reading)".to_owned())
        );
        println!(
            "       {} bracket group(s); body {}",
            reading.binders.len(),
            match &reading.body {
                Some(BodyReading::Applied { head, arguments }) => format!(
                    "APPLIED: first position {:?}, {} argument(s) {:?}",
                    head.occupant,
                    arguments.len(),
                    arguments
                        .iter()
                        .map(|slot| slot.occupant.as_str())
                        .collect::<Vec<&str>>()
                ),
                Some(BodyReading::Undecomposed { span, .. }) =>
                    format!("UNDECOMPOSED, retained whole: {:?}", span.text(&reading.statement)),
                None => "not read".to_owned(),
            }
        );
        for residue in &reading.residue {
            println!("       residue {:?}", residue.text);
            println!("         refused by: {}", residue.refused_by);
        }
    }

    println!("\n  what the population founds about its own runs:");
    println!(
        "    leading regions witnessed at {:?} groups   -> a nonempty SEQUENCE is founded: {}",
        grammar.binder_group_lengths(),
        grammar.sequence_is_founded()
    );
    println!(
        "    name runs witnessed at {:?} tokens",
        grammar.binder_name_lengths()
    );
    println!("    first-position tokens, with the argument counts witnessed after them:");
    for (head, arities) in grammar.heads() {
        println!("      {head:<20} {arities:?}");
    }

    println!("\n  THE APERTURE  --  what this grammar CANNOT do, with the material that bounds it:");
    for bound in grammar.aperture() {
        println!("    * {bound}");
    }
    println!(
        "\n    and per identifier the deposit recruits, whose arity the statement population never founded:"
    );
    let unfounded_heads: Vec<String> = body
        .recruited_population()
        .into_iter()
        .filter(|identifier| grammar.unfounded_head_arity(identifier).is_some())
        .collect();
    wrapped("      ", &unfounded_heads);

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE FALSIFIER FROM THE RECORD, RE-RUN  --  `derive` alone still returns nothing");

    println!(
        "\n  Each of these is written in the deposit's own vocabulary out of identifiers the deposit\n  \
         recruits. `ConditionedBody::derive` is the route-founding species and it is UNCHANGED."
    );
    let mut derive_on_absent = 0usize;
    for absent in ABSENT_STATEMENTS {
        let returned = body
            .derive(&DerivationQuery::reaching(absent))
            .expect("derives");
        derive_on_absent += returned.len();
        println!("    |- {absent:<52} derive returned {} passages", returned.len());
    }
    let mut derive_on_standing = 0usize;
    println!("\n  and on the statements the deposit does reach, the same organ still returns:");
    for statement in body.standing_statements() {
        let returned = body
            .derive(&DerivationQuery::reaching(&statement))
            .expect("derives");
        derive_on_standing += returned.len();
        println!("    |- {statement:<52} derive returned {} passages", returned.len());
    }

    controls.check(
        "control 1 -- the falsifier still fires on the unjoined path",
        derive_on_absent == 0 && derive_on_standing > 0,
        &format!(
            "{} absent statements put to `derive` returned {derive_on_absent} passages between \
             them, while the standing statements returned {derive_on_standing}. The three blocking \
             sites are intact; what follows is a SPECIES BESIDE `derive`, not a weakening of it.",
            ABSENT_STATEMENTS.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE POSITION ECOLOGY  --  what conditions the composition, read off the same material");

    println!(
        "\n  The composition above founds from FORMAL GRAMMAR with nothing conditioning it: every\n  \
         recruited identifier goes into every recovered slot, and the stem licence admits\n  \
         `exactCarrier apply` because `P` and `apply` share the founded letter `p`. That licence is\n  \
         about the CONTACT -- these two identifiers belong together. It says nothing about the PLACE."
    );
    println!(
        "\n  The place is something the deposit's own reading already knows, and the reading that\n  \
         knows it is the one the composition was not using. `read_derivation` opens ONE declaration\n  \
         per artifact; `lean_development` at EveryTopLevelDeclaration opens all of them."
    );
    println!(
        "\n    declarations opened at the wider grain     {}",
        development.declarations.len()
    );
    println!(
        "    declarations the narrow grain never saw    {}",
        development.declarations.len() - body.standing().len()
    );
    println!(
        "    distinct declaration statements            {}",
        ecology.declaration_grammar().population().len()
    );
    for statement in ecology.declaration_grammar().population() {
        println!("      |- {statement}");
    }
    let narrow = body.recruited_population();
    let wide = ecology.recruited();
    let unseen: Vec<String> = wide.difference(&narrow).cloned().collect();
    println!(
        "\n    the recruited population the composition was drawing on   {} identifiers",
        narrow.len()
    );
    println!(
        "    the population the wider reading places                    {} identifiers",
        wide.len()
    );
    println!("    and these {} were invisible to it:", unseen.len());
    wrapped("      ", &unseen);

    println!("\n  THE POSITION CENSUS  --  where the material places each identifier. Nothing here is");
    println!("  a category: `apply` is not called a tactic, it is recorded as having stood in tactic");
    println!("  position, because that is the only place the reading found it.");
    for (identifier, places) in ecology.census() {
        let rendered: Vec<String> = places.iter().map(ToString::to_string).collect();
        println!("    {identifier:<28} {}", rendered.join("  "));
    }

    println!(
        "\n  THE DECLARED-SHAPE COHORTS  --  each declaration's own statement with every binder-name\n  \
         token replaced by the ordinal of the binder that founded it. Two declarations the\n  \
         material's reading cannot tell apart are ONE cohort, and an identifier may stand where any\n  \
         member of its cohort stands. That is what lets a declaration the material never USED in a\n  \
         statement position be composed into one."
    );
    for shape in ecology.shapes() {
        println!("    {:<44} {:?}", shape.skeleton, shape.members);
    }
    if !ecology.unread().is_empty() {
        println!(
            "    declarations whose statement the grammar could not read, retained: {:?}",
            ecology.unread()
        );
    }

    println!("\n  THE GATE, per recovered slot species -- who the material lets stand there:");
    for slot in [
        SlotSpecies::BinderName,
        SlotSpecies::BinderType,
        SlotSpecies::BodyHead,
        SlotSpecies::BodyArgument,
    ] {
        let admitted = ecology.admitted_into(slot);
        let named: Vec<String> = admitted
            .iter()
            .map(|(identifier, carrier)| {
                if identifier == carrier {
                    identifier.clone()
                } else {
                    format!("{identifier}(via cohort member {carrier})")
                }
            })
            .collect();
        println!("    {:<16} {}", slot.name(), named.join("  "));
    }
    println!(
        "\n  `ExactRelay` is the whole point. The material never once put it in a statement, so no\n  \
         census of occurrences could license it. Its DECLARED SHAPE is identical to `exactCarrier`'s,\n  \
         and `exactCarrier` is the only identifier the material ever stood in first position of a\n  \
         trailing region. The cohort carries it there."
    );

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE ADMISSION  --  every candidate, with its verdict, and every refusal retained");

    println!(
        "\n  candidates composed: {}   admitted: {}   refused: {}",
        founded.adjudicated.len(),
        founded.admitted().len(),
        founded.refused().len()
    );
    println!("\n  by composition species:");
    for species in CompositionSpecies::ALL {
        let all = founded
            .adjudicated
            .iter()
            .filter(|entry| entry.candidate.species == species)
            .count();
        let admitted = founded
            .admitted()
            .into_iter()
            .filter(|entry| entry.candidate.species == species)
            .count();
        println!(
            "    {:<24} {:>5} composed   {:>4} admitted   {:>5} refused",
            species.name(),
            all,
            admitted,
            all - admitted
        );
    }

    println!("\n  THE RETAINED OBSTRUCTIONS, by species, complete:");
    for (species, members) in founded.obstructions() {
        println!("\n    {species}   {} candidates", members.len());
        println!(
            "      what it says: {}",
            members[0]
                .admission
                .obstruction()
                .map_or_else(String::new, ToString::to_string)
        );
        let named: Vec<String> = members
            .iter()
            .map(|entry| label(entry, &ordinals))
            .collect();
        wrapped("      ", &named);
    }

    println!("\n  ONE REFUSAL PER SPECIES, IN FULL, so the obstruction can be checked rather than believed:");
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for entry in founded.refused() {
        let Some(obstruction) = entry.admission.obstruction() else {
            continue;
        };
        if !seen.insert(obstruction.species()) {
            continue;
        }
        println!("\n    refused: |- {}", entry.candidate.statement);
        println!(
            "      composed from |- {}   by {}   at {}",
            entry.candidate.from,
            entry.candidate.species.name(),
            entry.candidate.site
        );
        println!("      the rule: {}", entry.candidate.rule);
        println!("      the obstruction ({}):", obstruction.species());
        println!("        {obstruction}");
    }

    controls.check(
        "control 3 -- refusal is retained and exhibited, and the rule is a population",
        !founded.refused().is_empty()
            && founded.is_a_population()
            && founded.obstructions().len() >= 3,
        &format!(
            "{} candidates were refused across {} obstruction species, every one retained with the \
             material that refused it and exhibited above. {} were admitted. A rule that admitted \
             everything would be a filter inverted and one that admitted nothing would be a filter; \
             this is neither.",
            founded.refused().len(),
            founded.obstructions().len(),
            founded.admitted().len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5]  THE FOUNDED STATEMENTS  --  reached by the instance, absent from the deposit");

    let composed = compose_in_scope(&founded, Some(&ecology)).expect("composes");
    let statements = founded.founded_statements();
    println!(
        "\n  {} statements founded, none of which the deposit reaches, presented by {} artifacts.",
        statements.len(),
        composed.len()
    );
    println!("\n  every founded statement:");
    for statement in &statements {
        println!("    |- {statement}");
    }

    let morphemic = founded.admitted_at_morphemic(MORPHEMIC_LETTERS);
    let residual = founded.admitted_below_morphemic(MORPHEMIC_LETTERS);
    println!(
        "\n  of the {} admitted compositions, {} are licensed by a founded stem of at least {} \
         characters\n  -- a WORD the corpus committed rather than a residual letter. Every one of \
         those is exhibited\n  here in full. The other {} are exhibited by name below and are \
         recoverable by declaring their stems.",
        founded.admitted().len(),
        morphemic.len(),
        MORPHEMIC_LETTERS,
        residual.len()
    );

    for (ordinal, entry) in morphemic.iter().enumerate() {
        exhibit(ordinal, entry, &founded, &composed, &ecology);
    }

    println!(
        "\n  A founded statement is production read as structure, exactly as the deposited \
         artifacts are.\n  Nothing here is submitted to a kernel and no composed statement is \
         asserted to be true, provable\n  or well-typed -- the deposit itself carries \
         `theorem carrier_transport ... := Nat.zero`, which no\n  kernel accepts and which the \
         atlas reads all the same. What separates the population above from\n  the one below is \
         the licence: a whole word the corpus committed, against a residual letter."
    );
    println!("\n  the compositions outside the declared aperture, by name, with their licensing stems:");
    let named: Vec<String> = residual
        .iter()
        .map(|entry| {
            format!(
                "{}({})",
                label(entry, &ordinals),
                entry
                    .admission
                    .licences()
                    .iter()
                    .map(|licence| licence.stem.as_str())
                    .collect::<Vec<&str>>()
                    .join("/")
            )
        })
        .collect();
    wrapped("    ", &named);

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE WITHHELD CONDITIONING  --  the same candidates with the gate off. THE ORBIT.");

    println!(
        "\n  `CLAUDE.md` §8: a gauge whose group acts trivially on the declared material is not a\n  \
         gauge, and a check whose material cannot vary the property under test wears a passing\n  \
         result. So the ecology is run as a DECLARED GAUGE with two settings over ONE candidate\n  \
         population -- same recruited set, same recovered grammar, same {} compositions -- and the\n  \
         orbit is exhibited rather than asserted.",
        founded.adjudicated.len()
    );
    println!(
        "\n    {:<34} {:>5} composed   {:>4} admitted   {:>5} refused   {} species",
        "position-gate-withheld",
        withheld.adjudicated.len(),
        withheld.admitted().len(),
        withheld.refused().len(),
        withheld.obstructions().len()
    );
    println!(
        "    {:<34} {:>5} composed   {:>4} admitted   {:>5} refused   {} species",
        "position-gate-applied",
        founded.adjudicated.len(),
        founded.admitted().len(),
        founded.refused().len(),
        founded.obstructions().len()
    );
    println!(
        "\n  and for reference, the rule as the roadmap measured it -- the NARROW recruited population\n  \
         `read_derivation` returns, with no gate:"
    );
    println!(
        "    {:<34} {:>5} composed   {:>4} admitted   {:>5} refused   {} species",
        "narrow-population, no gate",
        historical.adjudicated.len(),
        historical.admitted().len(),
        historical.refused().len(),
        historical.obstructions().len()
    );

    let withheld_statements = withheld.founded_statements();
    let removed: Vec<String> = withheld_statements
        .difference(&statements)
        .cloned()
        .collect();
    let widened: Vec<String> = statements
        .difference(&withheld_statements)
        .cloned()
        .collect();
    println!(
        "\n  WHAT THE GATE REMOVED ({}) -- every one of these is what the composition returns when\n  \
         the conditioning is withheld, and it is the population the roadmap exhibits:",
        removed.len()
    );
    for statement in &removed {
        println!("    |- {statement}");
    }
    println!(
        "\n  WHAT THE GATE ADDED ({}) -- must be empty. The position licence is a CONJUNCT and can\n  \
         only ever return a subpopulation; a gate that widened anything would be a different rule\n  \
         wearing a gate's name.",
        widened.len()
    );
    for statement in &widened {
        println!("    |- {statement}");
    }
    println!(
        "\n  WHAT SURVIVED ({}) -- composed under both settings:",
        statements.len()
    );
    for statement in &statements {
        println!("    |- {statement}");
    }
    println!(
        "\n  and the widening's own contribution: identifiers the narrow reading never recruited now\n  \
         reach the composition, so the WITHHELD arm founds statements the roadmap's figure never saw."
    );
    let widening_only: Vec<String> = withheld_statements
        .difference(&historical.founded_statements())
        .cloned()
        .collect();
    for statement in &widening_only {
        println!("    |- {statement}");
    }

    controls.check(
        "control 7 -- the conditioning is a gauge whose orbit on this material is non-trivial",
        !removed.is_empty() && widened.is_empty(),
        &format!(
            "the two settings were run over one candidate population of {}. The gate refused {} \
             statements the withheld setting founds, exhibited above by name, and added none. An \
             orbit of size one would mean the ecology decides nothing on this material and the \
             agreement below would be worth nothing.",
            founded.adjudicated.len(),
            removed.len()
        ),
    );

    controls.check(
        "control 8 -- the position licence is a conjunct, never a widener",
        statements.is_subset(&withheld_statements)
            && founded.adjudicated.len() == withheld.adjudicated.len()
            && founded
                .obstructions()
                .contains_key("identifier-never-stood-in-this-position"),
        &format!(
            "every one of the {} statements the gate admits is admitted without it, the candidate \
             populations are identical at {}, and the {} refusals carrying the new obstruction are \
             retained with the places the material DID stand each identifier.",
            statements.len(),
            founded.adjudicated.len(),
            founded
                .obstructions()
                .get("identifier-never-stood-in-this-position")
                .map_or(0, Vec::len)
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[7]  WHAT A BATCH GRADER COULD BE ASKED  --  the artifact, whole, and what is NOT claimed");

    println!(
        "\n  No kernel is in this loop and none may be: `CLAUDE.md` §13 rule 2 refuses a foreign\n  \
         process deciding what the body may construct. What is returned is the POPULATION, and\n  \
         grading it is a separate batch pass -- the shape `eros_lean_proof_production` already runs.\n  \
         This section states, structurally and without shelling anything, which composed artifacts\n  \
         are in a state where that pass could be run on them at all."
    );
    println!(
        "\n  The two conditions, both checkable here, and NEITHER is type-correctness:\n    \
         1  the artifact carries a COMPLETE founding line for every declaration its statement needs\n    \
         2  every token of the composed statement is either bound by the statement's own binders or\n       \
         founded by a line the artifact carries"
    );

    let mut submittable: Vec<&ComposedPassage> = Vec::new();
    for passage in &composed {
        if !passage.scope.is_complete() {
            continue;
        }
        let Ok(reading) = recover(&BTreeSet::from([passage.statement.clone()])) else {
            continue;
        };
        let Some(read) = reading.reading(&passage.statement) else {
            continue;
        };
        let bound: BTreeSet<String> = read
            .slots()
            .into_iter()
            .filter(|slot| slot.species == SlotSpecies::BinderName)
            .map(|slot| slot.occupant)
            .collect();
        let carried: BTreeSet<String> = passage
            .scope
            .imports
            .iter()
            .chain(passage.scope.founding.iter())
            .flat_map(|line| statement_tokens(line))
            .collect();
        if statement_tokens(&passage.statement)
            .into_iter()
            .all(|token| bound.contains(&token) || carried.contains(&token))
        {
            submittable.push(passage);
        }
    }
    let submittable_statements: BTreeSet<String> = submittable
        .iter()
        .map(|passage| passage.statement.clone())
        .collect();
    println!(
        "\n  {} of the {} composed artifacts meet both, reaching {} distinct statements:",
        submittable.len(),
        composed.len(),
        submittable_statements.len()
    );
    for statement in &submittable_statements {
        println!("    |- {statement}");
    }
    println!(
        "\n  ONE ARTIFACT PER FOUNDED STATEMENT, WHOLE -- the complete population, nothing selected:"
    );
    let mut exhibited: BTreeSet<&str> = BTreeSet::new();
    for passage in &submittable {
        if !exhibited.insert(passage.statement.as_str()) {
            continue;
        }
        println!();
        for line in passage.text.lines() {
            println!("    | {line}");
        }
    }
    println!(
        "\n  WHAT IS CLAIMED, precisely: every NAME in these statements resolves against declarations\n  \
         the material itself wrote, so an elaborator's answer would be about the mathematics rather\n  \
         than about an unknown identifier. That is what `(P : Prop) (h : P) : exactCarrier apply` --\n  \
         which the withheld setting founds and this one refuses -- could never reach."
    );
    println!(
        "\n  NAME RESOLUTION IS NOT TYPE CORRECTNESS, and the population itself carries the gap.\n    \
         |- (P : Prop) (h : P) : ExactRelay P   the carried scope makes `ExactRelay P` reducible to\n       \
         `exactCarrier P` to `P`, which `h` inhabits -- a statement an elaborator has something to\n       \
         say about.\n    \
         |- (P : P) (h : P) : exactCarrier P    every name resolves and the elaborator will still\n       \
         refuse it. WHICH refusal is not asserted here, because asserting it would mean running the\n       \
         kernel, and that is the batch pass's job and not this loop's. The population reached a\n       \
         state where a kernel's answer is ABOUT THE MATHEMATICS, which is what a batch grade needs\n       \
         and is not the same as being right."
    );
    println!(
        "\n  WHAT IS NOT CLAIMED: the composed BODY is not a proof. `have founded := ...` names both\n  \
         sides of the contact pair so the licence is visible in the circuit; it closes no goal, so a\n  \
         batch submission returns `unsolved goals` on even the well-typed statements. Composing a\n  \
         proof is a different move and is not this one. Nothing here is asserted to be true, and\n  \
         nothing here bears on any Millennium result."
    );

    // ---------------------------------------------------------------------------------------------
    rule("[8]  THE CIRCUIT  --  does the founded statement have a 0-cell, and does the reading see it?");

    let before = found_conditioned_circuit(body.standing().to_vec(), APERTURE).expect("founds");
    let after = found_conditioned_circuit(
        passages_with_composed(&body, &composed).expect("passages"),
        APERTURE,
    )
    .expect("founds");

    let before_vertices = statement_vertices(&before);
    let after_vertices = statement_vertices(&after);
    let new_vertices: Vec<String> = after_vertices
        .difference(&before_vertices)
        .cloned()
        .collect();
    println!("\n  statement 0-cells of the deposit alone: {}", before_vertices.len());
    for vertex in &before_vertices {
        println!("    {vertex}");
    }
    println!(
        "\n  statement 0-cells the production founded: {}",
        new_vertices.len()
    );
    for vertex in &new_vertices {
        println!("    {vertex}");
    }

    let movement = route_movement(&before.circuit, &after.circuit);
    println!(
        "\n  route_movement().founded_statements() -- the organ built to see a founded statement, \
         which\n  returned the EMPTY population on every query in the record:"
    );
    for statement in movement.founded_statements() {
        println!("    |- {statement}");
    }
    println!(
        "\n  the two populations agree: {}",
        *movement.founded_statements() == statements
    );
    println!(
        "  and every founded statement's 0-cell key resolves in the circuit: {}",
        statements
            .iter()
            .all(|statement| after.circuit.vertices().contains_key(&statement_vertex_key(statement)))
    );
    println!(
        "  provenance is total (every cell named by a passage): {}",
        after.provenance_is_total()
    );

    controls.check(
        "control 2 -- a returned passage reaches a statement absent from standing_statements()",
        !statements.is_empty()
            && statements.is_disjoint(&body.standing_statements())
            && !new_vertices.is_empty()
            && *movement.founded_statements() == statements
            && !morphemic.is_empty(),
        &format!(
            "{} statements founded, {} of them exhibited in full at a morphemic licence, {} new \
             statement 0-cells in the circuit, and route_movement().founded_statements() reports \
             exactly the founded population. That organ returned empty on every query in the \
             record; it fires here.",
            statements.len(),
            morphemic.len(),
            new_vertices.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[9]  THE FOURTH MOVE SPECIES  --  separated from the other three by its substitution");

    let composing = statement_composition_moves(&after, &body.standing_statements());
    let existing = moves_the_production_made(&after);
    let composing_deposit_the_vertex = composing
        .iter()
        .filter(|declared| deposits_its_statement_vertex(&after, declared))
        .count();

    println!(
        "\n  `Deposit`, `RecruitmentExchange` and `LemmaSplit` all preserve `statement` by \
         construction:\n  both sides of each of them already reach it, so the statement 0-cell sits \
         in the move's BOUNDARY.\n  `StatementComposition` deposits that 0-cell. The discriminator \
         is a property of the substitution."
    );
    println!(
        "\n    {:<24} {:>6} moves   {:>6} of them deposit their own statement 0-cell",
        MoveSpecies::StatementComposition.name(),
        composing.len(),
        composing_deposit_the_vertex
    );
    let mut existing_deposit_the_vertex = 0usize;
    for species in [
        MoveSpecies::Deposit,
        MoveSpecies::RecruitmentExchange,
        MoveSpecies::LemmaSplit,
    ] {
        let members: Vec<&DerivationMove> = existing
            .iter()
            .filter(|declared| declared.species == species)
            .collect();
        let depositing = members
            .iter()
            .filter(|declared| deposits_its_statement_vertex(&after, declared))
            .count();
        existing_deposit_the_vertex += depositing;
        println!(
            "    {:<24} {:>6} moves   {:>6} of them deposit their own statement 0-cell",
            species.name(),
            members.len(),
            depositing
        );
    }
    println!(
        "\n    the fourth species is separated from the other three on this material: {}",
        composing_deposit_the_vertex == composing.len()
            && existing_deposit_the_vertex == 0
            && !composing.is_empty()
            && existing.len() > composing.len()
    );

    if let Some(declared) = composing.first() {
        println!("\n  one statement-composition move, whole:");
        println!("    species    {}", declared.species.name());
        println!("    statement  |- {}", declared.statement);
        println!("    stem       {:?}", declared.stem);
        println!("    withdraws  {:?}", declared.withdraws);
        println!("    deposits   {:?}", declared.deposits);
        println!(
            "    boundary   {} cells   before {} cells   after {} cells   added {} cells",
            declared.substitution.boundary.len(),
            declared.substitution.before.len(),
            declared.substitution.after.len(),
            declared.substitution.added().len()
        );
    }

    // ---------------------------------------------------------------------------------------------
    rule("[10]  THE UNCONDITIONED NULL  --  the same species, put to a body exposed to nothing");

    let null_founded =
        found_statements_under(&null, &ecology, PositionGate::Applied).expect("founds");
    println!(
        "\n  candidates composed: {}   admitted: {}   refused: {}",
        null_founded.adjudicated.len(),
        null_founded.admitted().len(),
        null_founded.refused().len()
    );
    println!(
        "  founded statements: {:?}",
        null_founded.founded_statements()
    );
    println!("\n  the refusals, by species:");
    for (species, members) in null_founded.obstructions() {
        println!("    {species:<44} {} candidates", members.len());
    }
    println!(
        "\n  The grammar is the SAME grammar -- it is recovered from the deposit's statements, which \
         the\n  null body also stands on -- so the candidate population is identical. What differs \
         is the\n  licence: a body that has founded no stem covers nothing, holds no pair together, \
         and admits\n  nothing. The conditioning is the last gate and the only one that founds."
    );

    controls.check(
        "control 4 -- the unconditioned null founds nothing through the new species",
        null_founded.admitted().is_empty()
            && null_founded.founded_statements().is_empty()
            && null_founded.adjudicated.len() == founded.adjudicated.len(),
        &format!(
            "the same {} candidates were composed against the same recovered grammar and every one \
             was refused. {} of them by `no-founded-stem-holds-them`, which is the licence law \
             refusing for want of a morphology.",
            null_founded.adjudicated.len(),
            null_founded
                .obstructions()
                .get("no-founded-stem-holds-them")
                .map_or(0, Vec::len)
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[11]  THE ABLATION  --  remove one founded stem and re-found");

    let licensing: BTreeSet<String> = founded
        .admitted()
        .into_iter()
        .flat_map(|entry| {
            entry
                .admission
                .licences()
                .iter()
                .map(|licence| licence.stem.clone())
                .collect::<Vec<String>>()
        })
        .filter(|stem| stem.chars().count() >= MORPHEMIC_LETTERS)
        .collect();
    println!(
        "\n  the founded stems carrying a morphemic licence in this production: {licensing:?}"
    );

    let mut every_ablation_removes = !licensing.is_empty();
    for stem in &licensing {
        let ablation =
            ablate_stem_for_statements_under(&body, stem, Some(&ecology)).expect("ablates");
        every_ablation_removes &= ablation.removes_structure();
        println!(
            "\n    removing the founded stem {:?}, witnessed by the corpus wholes:",
            ablation.stem
        );
        for whole in &ablation.wholes {
            println!("      {whole}");
        }
        println!(
            "      founded statements {} -> {}",
            ablation.statements_before.len(),
            ablation.statements_after.len()
        );
        println!(
            "      the ROUTES its removal made structurally absent ({}):",
            ablation.routes_departed.len()
        );
        for route in &ablation.routes_departed {
            println!("        |- {}   under stem {:?}", route.statement, route.stem);
        }
        println!(
            "      the ROUTES its removal REOPENED -- occurrences it had been suppressing by \
             maximality ({}):",
            ablation.routes_reopened.len()
        );
        for reopened in &ablation.routes_reopened {
            println!(
                "        |- {}   now licensed by {:?}",
                reopened.statement, reopened.stems
            );
        }
        println!(
            "      the STATEMENTS that departed entirely ({}):",
            ablation.statements_departed.len()
        );
        for departed in &ablation.statements_departed {
            println!(
                "        |- {}   had been licensed by {:?} at sites {:?}",
                departed.statement, departed.stems, departed.sites
            );
        }
        println!(
            "      the STATEMENTS its removal reopened ({}):",
            ablation.statements_reopened.len()
        );
        for reopened in &ablation.statements_reopened {
            println!(
                "        |- {}   now licensed by {:?}",
                reopened.statement, reopened.stems
            );
        }
        println!("      unaccounted reopenings: {}", ablation.unaccounted.len());
        if ablation.statements_departed.is_empty() && !ablation.routes_departed.is_empty() {
            println!(
                "      READING: the statement is OVER-DETERMINED and the route is not. Removing \
                 this stem\n      removes the route it licensed; the statement stays founded \
                 because the residual letters\n      the stem had been suppressing license the same \
                 contact pair the moment it is gone. That\n      is retained-fiber reopening, and a \
                 report at statement granularity alone would have called\n      it no change."
            );
        }
    }

    controls.check(
        "control 5 -- an ablation removes later founding by removing structure",
        every_ablation_removes,
        &format!(
            "each of the {} morphemic licensing stems was removed in turn and re-founded. Every one \
             made founded routes structurally absent, and every reopening is accounted for by the \
             maximality the removed stem had been exercising -- unaccounted is empty throughout. \
             The departed and reopened populations are exhibited above by name; nothing here is a \
             count delta.",
            licensing.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("[12]  APERTURE HONESTY  --  what the recovered grammar cannot compose, and why");

    println!(
        "\n  A grammar with no stated aperture has not been graded. These are statements in the \
         deposit's\n  OWN vocabulary, out of identifiers it recruits, that this grammar therefore \
         cannot compose:"
    );

    let residue_refused: Vec<&AdjudicatedCandidate> = founded
        .obstructions()
        .get("slot-lies-in-grammar-residue")
        .cloned()
        .unwrap_or_default();
    let shape_refused: Vec<&AdjudicatedCandidate> = founded
        .obstructions()
        .get("grammar-never-witnessed-the-shape")
        .cloned()
        .unwrap_or_default();
    let length_refused: Vec<&AdjudicatedCandidate> = founded
        .obstructions()
        .get("binder-list-length-is-unfounded")
        .cloned()
        .unwrap_or_default();

    if let Some(entry) = residue_refused.first() {
        println!("\n    (a) |- {}", entry.candidate.statement);
        println!(
            "        The trailing region of |- {} is UNDECOMPOSED. Its reading is",
            entry.candidate.from
        );
        println!(
            "        {}",
            founded
                .grammar
                .render(&entry.candidate.from)
                .unwrap_or_default()
        );
        println!("        and the bracketed part is residue the recovery could not place:");
        println!(
            "          {}",
            entry
                .admission
                .obstruction()
                .map_or_else(String::new, ToString::to_string)
        );
        println!(
            "        {} such compositions were composed and every one refused.",
            residue_refused.len()
        );
    }
    if let Some(entry) = shape_refused.first() {
        println!("\n    (b) |- {}", entry.candidate.statement);
        println!(
            "        This is the record's own example -- `exactCarrier (exactCarrier P)` from \
             `exactCarrier P`."
        );
        println!(
            "        The record said what was needed was knowing that `exactCarrier` is applied to \
             an argument.\n        The grammar DOES recover that: {:?}. And it is NOT ENOUGH, which \
             is a second missing\n        ingredient the record did not name:",
            founded.grammar.heads()
        );
        println!(
            "          {}",
            entry
                .admission
                .obstruction()
                .map_or_else(String::new, ToString::to_string)
        );
        println!(
            "        {} such compositions were composed and every one refused.",
            shape_refused.len()
        );
    }
    if let Some(entry) = length_refused.first() {
        println!("\n    (c) |- {}", entry.candidate.statement);
        println!(
            "        Withdrawing the only bracket group of |- {} would leave a leading region the",
            entry.candidate.from
        );
        println!("        population never witnesses:");
        println!(
            "          {}",
            entry
                .admission
                .obstruction()
                .map_or_else(String::new, ToString::to_string)
        );
        println!(
            "        {} such compositions were composed and every one refused.",
            length_refused.len()
        );
    }

    println!("\n  and the arities the population does not found, which admissions CARRY rather than erase:");
    let carrying: Vec<String> = founded
        .admitted()
        .into_iter()
        .filter_map(|entry| match &entry.admission {
            StatementAdmission::Admitted {
                carried_aperture, ..
            } if !carried_aperture.is_empty() => Some(label(entry, &ordinals)),
            _ => None,
        })
        .collect();
    println!(
        "    {} admitted compositions carry at least one uncertified arity:",
        carrying.len()
    );
    wrapped("      ", &carrying);

    controls.check(
        "control 6 -- the recovered grammar states its aperture and a bounded statement is exhibited",
        !founded.grammar.aperture().is_empty()
            && !residue_refused.is_empty()
            && !shape_refused.is_empty(),
        &format!(
            "the grammar returns {} aperture members, each carrying the material that bounds it. \
             {} compositions were refused as residue and {} as a shape the population never \
             witnessed, with one of each exhibited whole above.",
            founded.grammar.aperture().len(),
            residue_refused.len(),
            shape_refused.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    let mut by_species: BTreeMap<&str, usize> = BTreeMap::new();
    for entry in founded.refused() {
        if let Some(obstruction) = entry.admission.obstruction() {
            *by_species.entry(obstruction.species()).or_default() += 1;
        }
    }
    println!("\n  the retained obstruction population, by species:");
    for (species, count) in &by_species {
        println!("    {species:<44} {count}");
    }

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
