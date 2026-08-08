//! Condition a body on the project's own natural-language mathematics, ask it and an unconditioned
//! twin the same question, and read what each returned as a circuit.
//!
//! ```text
//! cargo run --release --example conditioned_derivation_body -- \
//!     standing/output \
//!     reference/pureholonics-seed/src/pureholonics \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! The three paths are the mathematical deposit and two frames of linguistic material. Both frames
//! are read: `CLAUDE.md` §8 requires a gauge to exhibit a non-trivial orbit on the declared material
//! before agreement between frames may be read as evidence, and two corpora that founded the same
//! morphology would be one frame wearing two names. On this material they do not — one corpus
//! witnessed `carrier` and `witness` in two wholes and the other in at most one, so the same
//! deposited identifier decomposes differently under each, and the run prints both covers side by
//! side.
//!
//! ## What this driver is for
//!
//! It runs one control and everything else is the material that control needs:
//!
//! > **Same query, two bodies, one conditioned and one not. The returns must differ, and the
//! > difference must be caused by founded morphology being on the path: delete the founded stem and
//! > the later production must be structurally absent.**
//!
//! Both halves are here. The unconditioned body returns nothing because a body exposed to nothing
//! holds no stem that can bridge two identifiers — that is construction by omission. Then every
//! stem that licensed a passage is **deleted from the founded population and the query is re-asked**,
//! which is the fourth ablation shape and has no implementation in this repository or in the frozen
//! laboratory.
//!
//! Nothing here is submitted to a kernel. A derived passage is production read as structure, exactly
//! as the deposited artifacts are — the deposit itself carries `theorem carrier_transport ... :=
//! Nat.zero`, which no kernel accepts and which the atlas reads all the same.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    ablate_stem, expose, ConditionedBody, ConditionedCircuit, DerivationQuery, DerivedPassage,
    Exposure, FoundedMorphology, PassageOrigin, StemAblation,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::rebase_invariants::PivotRule;

/// Every file with one of the declared extensions under `root`, in a stable order.
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

fn rule(title: &str) {
    println!("\n{}", "=".repeat(94));
    println!("{title}");
    println!("{}", "=".repeat(94));
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

fn short(statement: &str) -> String {
    if statement.chars().count() <= 46 {
        statement.to_owned()
    } else {
        format!("{}...", statement.chars().take(43).collect::<String>())
    }
}

/// Print one passage as the artifact it is, with its bridge lineage grouped by occurrence pair.
fn exhibit(passage: &DerivedPassage) {
    println!("\n  {}", passage.name);
    println!(
        "      licensed by stem {:?}   brought {}   reaches {}",
        passage.stem, passage.brought, passage.reaches
    );
    for bridge in passage.licensing() {
        let routes = if bridge.routes.len() <= 3 {
            bridge.routes.join(" ")
        } else {
            format!(
                "{} ... {}   [{} routes]",
                bridge.routes[0],
                bridge.routes[bridge.routes.len() - 1],
                bridge.routes.len()
            )
        };
        println!(
            "      bridge   {} @{}  <-{:?}->  {} @{}   licensed by {routes}",
            bridge.held, bridge.held_at, bridge.stem, bridge.brought, bridge.brought_at
        );
    }
    for line in passage.text.lines() {
        println!("      | {line}");
    }
}

fn betti(circuit: &ConditionedCircuit, grade: u32) -> Option<usize> {
    circuit
        .circuit
        .invariants(PivotRule::SmallestMagnitude)
        .ok()
        .and_then(|invariants| {
            invariants
                .grades
                .iter()
                .find(|carried| carried.grade == grade)
                .map(|carried| carried.betti)
        })
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let deposit_root = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );
    let frame_a = PathBuf::from(arguments.get(1).cloned().unwrap_or_else(|| {
        "reference/pureholonics-seed/src/pureholonics".to_owned()
    }));
    let frame_b = PathBuf::from(
        arguments
            .get(2)
            .cloned()
            .unwrap_or_else(|| "reference/holobrochos-a07ff376/src/soma".to_owned()),
    );

    let deposit = read_deposit(&deposit_root);
    let corpus_a = read_corpus(&frame_a);
    let corpus_b = read_corpus(&frame_b);

    if deposit.is_empty() || corpus_a.is_empty() || corpus_b.is_empty() {
        eprintln!(
            "material missing: deposit {} artifacts, frame A {} wholes, frame B {} wholes",
            deposit.len(),
            corpus_a.len(),
            corpus_b.len()
        );
        std::process::exit(2);
    }

    let mut controls = Controls::new();

    let unconditioned = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let mut body_a = unconditioned.clone();
    body_a.condition(&corpus_a);
    let mut body_b = unconditioned.clone();
    body_b.condition(&corpus_b);

    let recruited = unconditioned.recruited_population();
    let statements = unconditioned.standing_statements();

    rule("CONDITIONED DERIVATION -- the conditioning, the production, the circuit");
    println!("\nmaterial");
    println!(
        "  mathematical   {:<52} {} artifacts",
        deposit_root.display(),
        deposit.len()
    );
    println!(
        "  linguistic A   {:<52} {} wholes",
        frame_a.display(),
        corpus_a.len()
    );
    println!(
        "  linguistic B   {:<52} {} wholes",
        frame_b.display(),
        corpus_b.len()
    );
    println!("\nthe deposit recruits {} identifiers:", recruited.len());
    for identifier in &recruited {
        println!("    {identifier}");
    }
    println!("\nand reached {} statements:", statements.len());
    for statement in &statements {
        println!("    {statement}");
    }

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE CONDITIONING -- morphology founded by exposure to linguistic material");

    for (name, body) in [("A", &body_a), ("B", &body_b)] {
        let morphology = body.morphology();
        println!(
            "\n  frame {name}:  founded {}   committed {}   provisional {}",
            morphology.founded().len(),
            morphology.committed().len(),
            morphology.provisional().len()
        );
    }

    println!("\n  the founded cover of every recruited identifier, in both frames");
    println!(
        "  a residue character is bracketed: material the corpus committed no stem for.\n"
    );
    println!("    {:<26} {:<34} {}", "identifier", "frame A", "frame B");
    let mut covers_differ = false;
    let mut residue_a: Vec<String> = Vec::new();
    for identifier in &recruited {
        let cover_a = body_a.morphology().cover(identifier).expect("ascii");
        let cover_b = body_b.morphology().cover(identifier).expect("ascii");
        if cover_a.render() != cover_b.render() {
            covers_differ = true;
        }
        if !cover_a.residue.is_empty() {
            residue_a.push(format!("{identifier} -> {}", cover_a.residue_characters()));
        }
        println!(
            "    {:<26} {:<34} {}",
            identifier,
            cover_a.render(),
            cover_b.render()
        );
    }
    println!("\n  retained obstruction in frame A -- material no committed stem covers:");
    if residue_a.is_empty() {
        println!("    (none)");
    } else {
        for entry in &residue_a {
            println!("    {entry}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE GAUGE -- two receiver families over one item population");

    let orbit_a = body_a.frame_orbit().expect("ascii identifiers");
    println!(
        "\n  item population: the character positions of the recruited identifiers -- {} items",
        orbit_a.conditioned.one_shot.blocks.iter().map(BTreeSet::len).sum::<usize>()
    );
    println!(
        "  unconditioned family: 1 receiver (has this identifier ended)      one-shot blocks {}",
        orbit_a.unconditioned.one_shot.len()
    );
    println!(
        "  conditioned   family: 1 + {} founded stems                        one-shot blocks {}",
        body_a.morphology().committed().len(),
        orbit_a.conditioned.one_shot.len()
    );
    println!(
        "  pairs the unconditioned reading merged and the conditioning separated: {}",
        orbit_a.separated_by_conditioning.len()
    );

    println!("\n  the founded morphology's complete incidence on the mathematical material");
    println!("  (every committed stem that fires, and where -- the generator of those pairs)\n");
    for firing in &orbit_a.firing {
        println!("    {:<14} {}", firing.stem, firing.positions.join("  "));
    }

    println!("\n  four separated pairs, with the word the unconditioned reading needed:");
    for pair in orbit_a.separated_by_conditioning.iter().rev().take(4) {
        println!(
            "    {:<24} {:<24} word {:<8} conditioned sees it by stem {:?}",
            pair.left,
            pair.right,
            format!("{:?}", pair.distinguishing_word),
            pair.witness_stem.clone().unwrap_or_default()
        );
    }

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE PRODUCTION -- the same query, put to two bodies");

    let mut derived_a: BTreeMap<String, Vec<DerivedPassage>> = BTreeMap::new();
    let mut derived_bare: usize = 0;
    for statement in &statements {
        let query = DerivationQuery::reaching(statement);
        let bare = unconditioned.derive(&query).expect("derives");
        derived_bare += bare.len();
        let passages = body_a.derive(&query).expect("derives");
        derived_a.insert(statement.clone(), passages);
    }

    println!("\n  query                                            unconditioned   conditioned");
    for statement in &statements {
        println!(
            "  {:<48} {:>13}   {:>11}",
            short(statement),
            0,
            derived_a[statement].len()
        );
    }

    let query = statements
        .iter()
        .max_by_key(|statement| derived_a[*statement].len())
        .cloned()
        .expect("the deposit reached a statement");
    let the_query = DerivationQuery::reaching(&query);
    let production = derived_a[&query].clone();

    println!("\n  the query carried forward: {query}");
    println!(
        "\n  the unconditioned body returned: (empty -- it holds no stem that can bridge two \
         identifiers)"
    );
    println!(
        "\n  the conditioned body returned {} passages, exhibited whole:",
        production.len()
    );
    for passage in &production {
        exhibit(passage);
    }

    let licensing: BTreeSet<String> = production
        .iter()
        .map(|passage| passage.stem.clone())
        .collect();
    println!("\n  the founded stems that licensed them: {licensing:?}");

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE CIRCUIT -- that production as a GradedCausalComplex, cell by passage");

    let aperture = CircuitAperture::STATEMENT_INCIDENT;
    let before = unconditioned
        .circuit(&the_query, aperture)
        .expect("founds");
    let after = body_a.circuit(&the_query, aperture).expect("founds");

    println!("\n  aperture: {aperture:?}\n");
    println!(
        "    {:<22} {:>14} {:>14}",
        "", "unconditioned", "conditioned"
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "passages",
        before.passages.len(),
        after.passages.len()
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "cells",
        before.cell_names().len(),
        after.cell_names().len()
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "betti 0",
        betti(&before, 0).map_or("-".to_owned(), |b| b.to_string()),
        betti(&after, 0).map_or("-".to_owned(), |b| b.to_string())
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "betti 1",
        betti(&before, 1).map_or("-".to_owned(), |b| b.to_string()),
        betti(&after, 1).map_or("-".to_owned(), |b| b.to_string())
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "routes to one result",
        before.circuit.lineage_route_excess(),
        after.circuit.lineage_route_excess()
    );
    println!(
        "    {:<22} {:>14} {:>14}",
        "vertices reaching it",
        before.circuit.vertices_reaching(&query).len(),
        after.circuit.vertices_reaching(&query).len()
    );

    let opened: BTreeSet<String> = after
        .cell_names()
        .difference(&before.cell_names())
        .cloned()
        .collect();
    println!(
        "\n  cells the conditioning founded ({}), each traced back to the passage that founded it:",
        opened.len()
    );
    for cell in after.circuit.complex().cells().values() {
        if !opened.contains(&cell.name) {
            continue;
        }
        let founding: Vec<String> = after
            .passages_founding(cell.id)
            .into_iter()
            .map(|passage| match &passage.origin {
                PassageOrigin::Derived { stem, brought, .. } => {
                    format!("{} [stem {stem:?} brought {brought}]", passage.derivation.name)
                }
                PassageOrigin::Standing { source } => format!("standing {source}"),
            })
            .collect();
        println!(
            "    grade {}  {:<52} <- {}",
            cell.grade,
            cell.name,
            founding.join(", ")
        );
    }

    let mut provenance_total = true;
    let mut apertures_founded = 0usize;
    for declared in CircuitAperture::DECLARED {
        match body_a.circuit(&the_query, declared) {
            Ok(circuit) => {
                apertures_founded += 1;
                if !circuit.provenance_is_total() {
                    provenance_total = false;
                    println!(
                        "\n  {declared:?} left cells unclaimed: {:?}",
                        circuit.unclaimed
                    );
                }
            }
            Err(refusal) => println!("\n  {declared:?} refused: {refusal}"),
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[5]  THE ABLATION -- delete a founded stem from the morphology and re-ask the query");

    let mut ablations: Vec<StemAblation> = Vec::new();
    for stem in &licensing {
        match ablate_stem(&body_a, stem, &the_query, aperture) {
            Ok(ablation) => ablations.push(ablation),
            Err(refusal) => println!("  {stem:?} refused: {refusal}"),
        }
    }
    println!(
        "\n  a removal both removes and REOPENS: a founded stem suppresses, by maximality, every"
    );
    println!("  founded occurrence it contains, and deleting it returns that suppressed population.");
    println!(
        "\n    {:<12} {:>8} {:>8} {:>8} {:>9} {:>12}   wholes witnessing",
        "stem", "before", "after", "absent", "reopened", "unaccounted"
    );
    for ablation in &ablations {
        println!(
            "    {:<12} {:>8} {:>8} {:>8} {:>9} {:>12}   {}",
            ablation.stem,
            ablation.passages_before.len(),
            ablation.passages_after.len(),
            ablation.passages_absent.len(),
            ablation.reopened.len(),
            ablation.unaccounted.len(),
            ablation.wholes.len()
        );
    }

    let reopening: Vec<&StemAblation> = ablations
        .iter()
        .filter(|ablation| !ablation.reopened.is_empty())
        .collect();
    if reopening.is_empty() {
        println!("\n  no removal reopened anything on this material.");
    } else {
        println!("\n  every reopening, with the stem the removed one had been covering:");
        for ablation in &reopening {
            for entry in &ablation.reopened {
                println!(
                    "    removing {:<10} reopened {:<52} licensed by {:?}",
                    format!("{:?}", ablation.stem),
                    entry.passage,
                    entry.stem
                );
            }
        }
    }

    if let Some(exhibited) = ablations
        .iter()
        .find(|ablation| {
            ablation.stem.chars().count() >= 4 && !ablation.passages_absent.is_empty()
        })
        .or_else(|| ablations.first())
    {
        println!(
            "\n  deleting the founded stem {:?} -- witnessed by {} -- made these structurally \
             absent:",
            exhibited.stem,
            exhibited
                .wholes
                .iter()
                .map(|whole| {
                    Path::new(whole)
                        .file_name()
                        .map_or(whole.clone(), |name| name.to_string_lossy().into_owned())
                })
                .collect::<Vec<String>>()
                .join(" ")
        );
        for passage in &exhibited.passages_absent {
            exhibit(passage);
        }
        println!("\n  and these circuit cells stopped existing:");
        for cell in &exhibited.cells_absent {
            println!("      {cell}");
        }
        println!(
            "\n  circuit cells that appeared, all of them reopenings: {}",
            exhibited.cells_appeared.len()
        );
        for cell in exhibited.cells_appeared.iter().take(6) {
            println!("      {cell}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE DECLARED FOILS -- if any stem population licenses as much, this is decorative");

    let founded_names: BTreeSet<String> = production
        .iter()
        .map(|passage| passage.name.clone())
        .collect();
    let mut foils: Vec<(String, BTreeSet<String>)> = Vec::new();
    for (name, morphology) in [
        (
            "promoted provisional",
            body_a.morphology().promoted_provisional(),
        ),
        ("reversed committed", body_a.morphology().reversed()),
        ("frame B (holobrochos)", body_b.morphology().clone()),
        ("unconditioned", FoundedMorphology::unconditioned()),
    ] {
        let committed = morphology.committed().len();
        let names: BTreeSet<String> = body_a
            .with_morphology(morphology)
            .derive(&the_query)
            .expect("derives")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        println!(
            "\n  {name:<24} committed stems {committed:<6} passages {:<5} same population as the \
             founded morphology? {}",
            names.len(),
            if names == founded_names { "YES" } else { "no" }
        );
        let only_founded: Vec<&String> = founded_names.difference(&names).collect();
        let only_foil: Vec<&String> = names.difference(&founded_names).collect();
        if !only_founded.is_empty() {
            println!("      only the founded morphology licenses: {only_founded:?}");
        }
        if !only_foil.is_empty() {
            println!("      only this foil licenses:              {only_foil:?}");
        }
        foils.push((name.to_owned(), names));
    }

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    controls.check(
        "the two linguistic frames found different morphologies on this material",
        covers_differ,
        "otherwise the corpus is not a frame and the gauge has one member",
    );
    controls.check(
        "the gauge acts non-trivially on the item population",
        orbit_a.acts_nontrivially(),
        "the conditioning separated identifier positions the unconditioned reading merged",
    );
    controls.check(
        "every separated pair names the founded stem that sees it",
        orbit_a
            .separated_by_conditioning
            .iter()
            .all(|pair| pair.witness_stem.is_some()),
        "a separation no stem accounts for would mean the orbit is not the conditioning's",
    );
    controls.check(
        "removing receivers only coarsens",
        orbit_a.coarsening_holds(),
        "the unconditioned one-shot partition is no finer than the conditioned one",
    );
    controls.check(
        "the unconditioned body returned nothing, for every query",
        derived_bare == 0,
        "a body exposed to nothing holds no stem that can bridge two identifiers",
    );
    controls.check(
        "the conditioned body returned a non-empty passage population",
        !production.is_empty(),
        "and every passage carries the bridge that licensed it",
    );
    controls.check(
        "at least one licensing stem is a whole morpheme rather than a residual letter",
        licensing.iter().any(|stem| stem.chars().count() >= 4),
        "a licence carried only by single characters would not be a morphological bridge",
    );
    controls.check(
        "every cell of the circuit traces back to a passage, under every aperture that founds",
        provenance_total && apertures_founded > 0,
        "a cell no passage names makes every later organ's return anonymous",
    );
    controls.check(
        "the conditioned circuit strictly contains the unconditioned one",
        before.cell_names().is_subset(&after.cell_names()) && !opened.is_empty(),
        "the conditioning founded cells and removed none",
    );
    controls.check(
        "the conditioning opened further routes to a standing statement",
        after.circuit.lineage_route_excess() > before.circuit.lineage_route_excess()
            && after.circuit.vertices_reaching(&query).len()
                > before.circuit.vertices_reaching(&query).len(),
        "a second route to a result the deposit already reached is what a derivation circuit calls \
         plurality",
    );
    controls.check(
        "deleting any licensing stem removes passages and the circuit cells they founded",
        !ablations.is_empty() && ablations.iter().all(StemAblation::removes_structure),
        "the fourth ablation shape: a founded fiber deleted, the query re-asked, later production \
         structurally absent",
    );
    controls.check(
        "the absent passages are exactly those the deleted stem licensed",
        ablations.iter().all(|ablation| {
            ablation
                .passages_absent
                .iter()
                .all(|passage| passage.stem == ablation.stem)
        }),
        "removing one stem may not remove a passage another stem licensed",
    );
    controls.check(
        "every passage a removal reopened is licensed by a stem the removed one contained",
        ablations
            .iter()
            .all(|ablation| ablation.unaccounted.is_empty()),
        "maximality is the only thing that can promote an occurrence; anything else is unexplained",
    );
    controls.check(
        "at least one removal reopens, so the suppression a founded stem exercises is measured",
        ablations
            .iter()
            .any(|ablation| !ablation.reopened.is_empty()),
        "a founded stem that suppresses nothing would leave this law present in the code and absent \
         from the evidence",
    );
    for (name, names) in &foils {
        controls.check(
            &format!("the {name} foil licenses a different population"),
            names != &founded_names,
            "if it licensed the same, the founding carries no evidence",
        );
    }

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
