//! The material was never missing; the intake could not resolve it.
//!
//! `research/records/2026-08-09_FOUR_RELATIONS_SEPARATE_THE_ATOM_AND_EACH_REFUTED_ITSELF_FIRST.md`
//! §7 closed on one fact: *"exactly one recruited identifier in 103 artifacts is declared… that is
//! the one constraint here a richer deposit genuinely would move, and it is a **material**
//! constraint rather than a construction one."*
//!
//! It is not a material constraint. `formal` — thirteen files a person wrote, in the tree the
//! whole time — carries **65 top-level declarations** with real recruitment chains. Run
//! `derivation_atlas::read_derivation` over it and you get 13 files, 11 derivations named by
//! whichever `theorem` was **last** in each file, and **zero** recruited-and-declared names: a
//! deposit in which nothing can be opened at all, which is *worse* than the generated one.
//!
//! Three defects produce that, each independent:
//!
//! 1. `name` is overwritten on every `theorem` line, so one file returns one declaration.
//! 2. Only `theorem` founds. `def`, `abbrev`, `structure`, `instance`, `lemma` bind their name out
//!    of the recruitment population without entering the declared one — so every object a theorem
//!    is *about* is an atom **by construction**.
//! 3. Doc-comment prose enters the recruitment multiset. `Consequently`, `Every`, `If`, `It`, `No`
//!    are recruited symbols right now.
//!
//! `lean_development` resolves all three and declares its aperture, so the historical reading is
//! reproducible and its silent loss is returnable.
//!
//! ## The falsifiers, declared before the organ existed — and both misses, reconciled by name
//!
//! Taken by an independent Python probe of the same thirteen files, written down, and only then
//! implemented in Rust. **Two of the three were wrong, and both are defects in the probe.** They are
//! carried here rather than quietly adjusted, because a prediction silently rewritten after the fact
//! is not a prediction.
//!
//! ```text
//!   probe   organ
//!      65      66   the probe's former list omitted `inductive`. `inductive Trace` is the one.
//!      78      80   +`inductive` takes the probe to 82. The remaining two are `(hxy i).trans` and
//!                   `(A.rebase e).Semantics` -- DOT PROJECTIONS the probe joined to same-named
//!                   top-level declarations in OTHER namespaces. The organ's token rule requires a
//!                   leading letter, so it drops `.trans`, and refuses to manufacture the edge.
//!      48      48   MATCHES, AND FOR THE WRONG REASON. The probe's `inductive` omission removed
//!                   three chains through `Trace`; its two spurious edges added three. Two errors
//!                   cancelling to the right number is `CLAUDE.md` §8's tautology rule pointed at a
//!                   prediction rather than a receipt, and it is why a matching figure is not
//!                   evidence on its own.
//! ```
//!
//! ## The controls
//!
//! 1. **The chain exists and is exhibited.** Not a count — every edge and every three-link chain by
//!    name.
//! 2. **The aperture violation is detected, not absorbed.** The one-artifact grain on this material
//!    must hand back every declaration it did not open. `CLAUDE.md` §8: *an organ used past its
//!    declared aperture is a defect even when it appears to return.*
//! 3. **The commentary is real contamination and is returned.** The English tokens must be in the
//!    commentary population and in **no** declaration's recruitment.
//! 4. **The null control against over-parsing**, taken by a **second scanner written differently** —
//!    a literal prefix table over modifier × former, sharing no code with the organ's iterative
//!    strip. Opened + unopened must equal it on both materials. It does not control for a former at
//!    column zero *inside* a block comment; the two agree here, and where they would not the lines
//!    are exhibited.
//! 5. **Parity with the historical reader**, on the artifacts where its aperture is exact — the ones
//!    carrying exactly one top-level declaration. Same name, same statement, recruitment difference
//!    exactly preamble + scoping. The artifacts where it is *not* exact are the finding, not a
//!    failure.
//! 6. **The elaboration deepens.** The old reading reported *"no root in the deposit carries a
//!    constituent past depth one."* A root here must carry constituents at depth >= 3, or the chain
//!    is a table and not a closure.
//! 7. **The correction to the four-relation record's own figure.** §7's *"exactly one recruited
//!    identifier in 103 artifacts is declared"* is wrong **on the generated deposit itself**, not
//!    only on `formal`: **39 of those 103 artifacts carry two top-level declarations**, and
//!    `def exactCarrier` was read as an atom by a former list that founded only `theorem`. The
//!    openable count is **two**, and **five** declarations recruit another. `abbrev ExactRelay` is a
//!    third declaration the old reader could not see, but nothing recruits it, so it is a declared
//!    name outside the openable set rather than a second correction — stated because the difference
//!    between "declared" and "openable" is exactly what the record collapsed.
//!
//! Run: `the_development_declares_its_own_chain [development-root] [generated-deposit-root]`

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::derivation_atlas::{Derivation, read_derivation};
use holonic_engine::lean_development::{
    ConductGrain, DeclarationGrain, DevelopmentReading, join, read_development,
};
use holonic_engine::name_elaboration::{ElaborationAperture, ElaborationDeposit};

/// Declared before the organ existed, by an independent probe. See the module note: two are wrong
/// and each miss is a defect in the probe, exhibited rather than adjusted away.
const PROBED_DECLARATIONS: usize = 65;
const PROBED_EDGES: usize = 78;
const PROBED_THREE_LINK: usize = 48;

/// What the organ returns, with the reconciliation carried at each line.
const DECLARATIONS: usize = 66;
const EDGES: usize = 80;
const THREE_LINK: usize = 48;
const MINIMUM_RECRUITING: usize = 40;

/// Tokens the probe found in doc comments and nowhere else. English, not mathematics.
const COMMENT_PROSE: [&str; 6] = ["Consequently", "Different", "Every", "If", "It", "No"];

/// Proof-local hypothesis binders measured in the term population BEFORE position existed. Two
/// characters, so the single-character binder rule could not reach them.
const BINDER_CONTAMINANTS: [&str; 6] = ["hc", "hcong", "hm", "hn", "hz", "hnm"];

/// Tactic heads measured in the term population before position existed.
const TACTIC_CONTAMINANTS: [&str; 6] = ["intro", "apply", "exact", "rw", "simp", "classical"];

/// Modifiers that may precede a top-level former.
const MODIFIERS: [&str; 6] = [
    "",
    "noncomputable ",
    "private ",
    "protected ",
    "partial ",
    "unsafe ",
];

/// A **second scanner, written differently**, for the over-parsing control.
///
/// The organ steps modifiers off the front of a line in a loop and then tries each former. This
/// builds the literal prefix table `modifier × former` once and asks `starts_with`. It shares no
/// code with [`holonic_engine::lean_development`] and it does not strip comments, so a former at
/// column zero inside a block comment would be counted here and not there. On both declared
/// materials the two agree; where they would not, the divergent lines are exhibited.
fn independent_former_count(text: &str) -> usize {
    let mut prefixes: Vec<String> = Vec::new();
    for modifier in MODIFIERS {
        for former in holonic_engine::derivation_atlas::DECLARATION_FORMERS {
            if former == "variable" || former == "example" {
                continue;
            }
            prefixes.push(format!("{modifier}{former} "));
        }
    }
    text.lines()
        .filter(|line| {
            let line = line.strip_prefix('@').map_or(*line, |after| {
                after
                    .find(']')
                    .map_or(after, |close| after[close + 1..].trim_start())
            });
            prefixes
                .iter()
                .any(|prefix| line.starts_with(prefix.as_str()))
        })
        .count()
}

fn main() {
    let mut arguments = std::env::args().skip(1);
    let development_root =
        PathBuf::from(arguments.next().unwrap_or_else(|| "formal".to_owned()));
    let generated_root = PathBuf::from(
        arguments
            .next()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=a development declares at the grain of its own declarations, never its files");
    println!("development={}", development_root.display());
    println!("generated={}", generated_root.display());

    let development_paths = lean_paths(&development_root);
    if development_paths.is_empty() {
        eprintln!("no .lean under {}", development_root.display());
        std::process::exit(2);
    }

    let plural = read_all(
        &development_paths,
        DeclarationGrain::EveryTopLevelDeclaration,
    );
    let historical = read_all(
        &development_paths,
        DeclarationGrain::OneArtifactOneDeclaration,
    );

    let mut controls: Vec<(bool, String, String)> = Vec::new();

    the_reading(&development_paths, &plural, &historical);
    control_one_the_chain(&plural, &mut controls);
    control_two_the_aperture(&development_paths, &plural, &historical, &mut controls);
    control_three_the_commentary(&plural, &mut controls);
    control_eight_position(&plural, &mut controls);
    control_nine_sub_illicium(&plural, &mut controls);
    control_six_the_elaboration_deepens(&plural, &mut controls);

    let generated_paths = lean_paths(&generated_root);
    if generated_paths.is_empty() {
        eprintln!("no .lean under {}", generated_root.display());
        std::process::exit(2);
    }
    control_four_no_over_parsing(
        &[
            ("the development", development_paths.as_slice()),
            ("the generated deposit", generated_paths.as_slice()),
        ],
        &mut controls,
    );
    control_five_and_seven_the_generated_deposit(&generated_paths, &mut controls);

    verdict(&controls);
}

// -------------------------------------------------------------------------------------------------
// Reading
// -------------------------------------------------------------------------------------------------

fn lean_paths(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(lean_paths(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

fn read_all(paths: &[PathBuf], grain: DeclarationGrain) -> DevelopmentReading {
    join(
        paths
            .iter()
            .filter_map(|path| std::fs::read_to_string(path).ok())
            .map(|text| read_development(&text, grain))
            .collect(),
    )
}

fn section(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

// -------------------------------------------------------------------------------------------------
// What the two grains return on the same thirteen files
// -------------------------------------------------------------------------------------------------

fn the_reading(paths: &[PathBuf], plural: &DevelopmentReading, historical: &DevelopmentReading) {
    section("THE SAME MATERIAL, AT TWO DECLARED GRAINS");

    println!("\n  {} files read", paths.len());
    println!("\n  {:<34} {:>12} {:>12}", "", "one-artifact", "every-decl");
    println!(
        "  {:<34} {:>12} {:>12}",
        "declarations opened",
        historical.declarations.len(),
        plural.declarations.len()
    );
    println!(
        "  {:<34} {:>12} {:>12}",
        "top-level formers NOT opened",
        historical.unopened.len(),
        plural.unopened.len()
    );
    println!(
        "  {:<34} {:>12} {:>12}",
        "recruited AND declared",
        historical.declared_recruitment().len(),
        plural.declared_recruitment().len()
    );

    let mut by_former: BTreeMap<&str, usize> = BTreeMap::new();
    for form in &plural.declarations {
        *by_former.entry(form.former.as_str()).or_insert(0) += 1;
    }
    println!("\n  the formers this development uses");
    println!("  ---------------------------------");
    for (former, count) in &by_former {
        println!("    {former:<16} {count:>4}");
    }
    println!(
        "\n  The one-artifact grain founds only `theorem`, so the {} declarations under the other",
        plural.declarations.len() - by_former.get("theorem").copied().unwrap_or(0)
    );
    println!("  formers were atoms BY CONSTRUCTION -- every object a theorem is about.");

    println!("\n  what the reading set aside, returned rather than dropped");
    println!("  --------------------------------------------------------");
    println!(
        "    commentary tokens   {:>6} distinct, {} occurrences",
        plural.commentary.len(),
        plural
            .commentary
            .values()
            .map(|count| *count as u64)
            .sum::<u64>()
    );
    println!(
        "    preamble tokens     {:>6} distinct, {} occurrences",
        plural.preamble.len(),
        plural
            .preamble
            .values()
            .map(|count| *count as u64)
            .sum::<u64>()
    );

    if plural.ambiguous_short_names.is_empty() {
        println!("\n  ambiguous short names: NONE across the development.");
        println!(
            "  A law that returns zero proves nothing about itself -- the join is exercised by"
        );
        println!(
            "  `ambiguity_across_a_joined_development_is_returned_not_resolved`, which builds a"
        );
        println!("  collision and requires both namespaces back.");
    } else {
        println!("\n  ambiguous short names, returned and NOT resolved");
        println!("  ------------------------------------------------");
        for (name, paths) in &plural.ambiguous_short_names {
            let namespaces: Vec<String> = paths
                .iter()
                .map(|path| {
                    if path.is_empty() {
                        "<root>".to_owned()
                    } else {
                        path.join(".")
                    }
                })
                .collect();
            println!("    {name:<44} {}", namespaces.join("  "));
        }
    }
}

// -------------------------------------------------------------------------------------------------
// Control 1 -- the chain
// -------------------------------------------------------------------------------------------------

fn control_one_the_chain(plural: &DevelopmentReading, controls: &mut Vec<(bool, String, String)>) {
    section("CONTROL 1 -- THE CHAIN EXISTS, AND IT IS EXHIBITED BY NAME");

    let chain = plural.declared_recruitment();
    let edges: usize = chain.values().map(BTreeSet::len).sum();

    let mut three_link: Vec<(&str, &str, &str)> = Vec::new();
    for (from, reached) in &chain {
        for middle in reached {
            let Some(onward) = chain.get(middle) else {
                continue;
            };
            for last in onward {
                three_link.push((from, middle, last));
            }
        }
    }

    println!("\n  {:<40} {:>8} {:>8} {:>8}", "", "probe", "organ", "held");
    let rows = [
        (
            "top-level declarations",
            PROBED_DECLARATIONS,
            plural.declarations.len(),
            DECLARATIONS,
        ),
        ("declared -> declared edges", PROBED_EDGES, edges, EDGES),
        (
            "three-link chains",
            PROBED_THREE_LINK,
            three_link.len(),
            THREE_LINK,
        ),
    ];
    for (name, probed, measured, expected) in rows {
        println!(
            "  {name:<40} {probed:>8} {measured:>8} {:>8}",
            if measured == expected { "yes" } else { "NO" }
        );
    }
    println!(
        "  {:<40} {:>8} {:>8} {:>8}",
        "declarations recruiting a declaration",
        "-",
        chain.len(),
        if chain.len() >= MINIMUM_RECRUITING {
            "yes"
        } else {
            "NO"
        }
    );
    println!(
        "\n  Where the probe and the organ differ, the probe is wrong and the reason is named:"
    );
    println!(
        "    +1 declaration   the probe's former list omitted `inductive`; `inductive Trace`."
    );
    println!(
        "    +2 edges         `(hxy i).trans` and `(A.rebase e).Semantics` are DOT PROJECTIONS."
    );
    println!("                     The probe joined them to same-named declarations in OTHER");
    println!("                     namespaces; the organ's token rule needs a leading letter and");
    println!("                     refuses to found the edge.");
    println!("    three-link       matches the probe's original 48 FOR THE WRONG REASON -- the");
    println!(
        "                     omitted `inductive` cost three chains and the two spurious edges"
    );
    println!("                     added three. A figure that agrees is not evidence on its own.");

    println!("\n  every declared -> declared edge, in canonical order");
    println!("  --------------------------------------------------");
    for (from, reached) in &chain {
        for to in reached {
            println!("    {from}  ->  {to}");
        }
    }

    println!("\n  every three-link chain, in canonical order");
    println!("  -----------------------------------------");
    three_link.sort_unstable();
    three_link.dedup();
    for (from, middle, last) in &three_link {
        println!("    {from}  ->  {middle}  ->  {last}");
    }

    let held = plural.declarations.len() == DECLARATIONS
        && edges == EDGES
        && three_link.len() == THREE_LINK
        && chain.len() >= MINIMUM_RECRUITING;
    controls.push((
        held,
        "control 1 -- the predicted chain population is returned exactly".to_owned(),
        format!(
            "{} declarations, {edges} edges, {} three-link chains, {} recruiting",
            plural.declarations.len(),
            three_link.len(),
            chain.len()
        ),
    ));
}

// -------------------------------------------------------------------------------------------------
// Control 2 -- the aperture violation is detected
// -------------------------------------------------------------------------------------------------

fn control_two_the_aperture(
    paths: &[PathBuf],
    plural: &DevelopmentReading,
    historical: &DevelopmentReading,
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROL 2 -- THE APERTURE VIOLATION IS RETURNED, NOT ABSORBED");

    println!(
        "\n  The historical reader took {} files and returned {} derivations without an error.",
        paths.len(),
        historical.declarations.len()
    );
    println!(
        "  {} top-level declarations went past it in silence. Here they are.",
        historical.unopened.len()
    );

    println!("\n  {:<12} {:<44} {}", "former", "name", "line");
    println!("  {}", "-".repeat(70));
    for missed in historical.unopened.iter().take(24) {
        println!(
            "  {:<12} {:<44} {}",
            missed.former, missed.name, missed.line
        );
    }
    if historical.unopened.len() > 24 {
        println!("  … and {} more", historical.unopened.len() - 24);
    }

    let accounted = historical.declarations.len() + historical.unopened.len();
    println!(
        "\n  {} opened + {} unopened = {accounted}, against {} at the plural grain.",
        historical.declarations.len(),
        historical.unopened.len(),
        plural.declarations.len()
    );

    let held = !historical.unopened.is_empty() && accounted == plural.declarations.len();
    controls.push((
        held,
        "control 2 -- every declaration the narrow aperture skipped is handed back".to_owned(),
        format!(
            "{accounted} accounted against {}",
            plural.declarations.len()
        ),
    ));
}

// -------------------------------------------------------------------------------------------------
// Control 3 -- the commentary
// -------------------------------------------------------------------------------------------------

fn control_three_the_commentary(
    plural: &DevelopmentReading,
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROL 3 -- COMMENT PROSE IS RETURNED AND RECRUITED BY NOTHING");

    let recruited_anywhere: BTreeSet<&str> = plural
        .declarations
        .iter()
        .flat_map(|form| form.recruited.keys().map(String::as_str))
        .collect();

    println!(
        "\n  {:<20} {:>10} {:>18}",
        "token", "in comment", "recruited by any"
    );
    println!("  {}", "-".repeat(52));
    let mut all_present = true;
    let mut none_recruited = true;
    for token in COMMENT_PROSE {
        let count = plural.commentary.get(token).copied().unwrap_or(0);
        let recruited = recruited_anywhere.contains(token);
        all_present &= count > 0;
        none_recruited &= !recruited;
        println!(
            "  {token:<20} {count:>10} {:>18}",
            if recruited { "YES -- LEAK" } else { "no" }
        );
    }

    println!("\n  the ten densest commentary tokens, which the old reading charged as recruitment");
    println!("  ------------------------------------------------------------------------------");
    let mut densest: Vec<(&String, &u32)> = plural.commentary.iter().collect();
    densest.sort_by(|left, right| right.1.cmp(left.1).then(left.0.cmp(right.0)));
    for (token, count) in densest.iter().take(10) {
        println!("    {token:<32} {count:>5}");
    }

    controls.push((
        all_present && none_recruited,
        "control 3 -- English prose sits in the commentary population and in no recruitment"
            .to_owned(),
        format!("{} distinct commentary tokens", plural.commentary.len()),
    ));
}

// -------------------------------------------------------------------------------------------------
// Controls 4 and 5 -- the null control on the generated deposit
// -------------------------------------------------------------------------------------------------

/// Control 8 -- position removes the named contaminants and moves no mathematical edge.
fn control_eight_position(plural: &DevelopmentReading, controls: &mut Vec<(bool, String, String)>) {
    section("CONTROL 8 -- POSITION, AND THE EDGES IT MUST NOT MOVE");

    println!(
        "\n  `FORMULA.md` §XVI: the illicium is friction, and `medium.rs`: \"Many faces from one"
    );
    println!(
        "  point IS the illicium and friction\". A reading with one face per point feels nothing."
    );
    println!("  Every name now carries a POSITION read from Lean's own grammar -- inside a binder");
    println!("  group the names before the `:` are founded and the type after it is recruited.\n");

    let terms: BTreeSet<&str> = plural
        .declarations
        .iter()
        .flat_map(|form| form.recruited.keys().map(String::as_str))
        .collect();
    let bindings: BTreeSet<&str> = plural
        .declarations
        .iter()
        .flat_map(|form| form.local_bindings.keys().map(String::as_str))
        .collect();
    let tactics: BTreeSet<&str> = plural
        .declarations
        .iter()
        .flat_map(|form| form.tactics.keys().map(String::as_str))
        .collect();

    // A leak is EXHIBITED with the declarations holding it, never counted. A count cannot be
    // diagnosed and a residue that cannot be diagnosed becomes permanent.
    let holders = |name: &str| -> Vec<&str> {
        plural
            .declarations
            .iter()
            .filter(|form| form.recruited.contains_key(name))
            .map(|form| form.name.as_str())
            .collect()
    };

    println!("  {:<22} {:>14}   {}", "name", "now", "still a term in");
    println!("  {}", "-".repeat(76));
    let mut binders_clean = true;
    let mut tactics_clean = true;
    for (population, expect_binding) in [
        (&BINDER_CONTAMINANTS[..], true),
        (&TACTIC_CONTAMINANTS[..], false),
    ] {
        for name in population {
            let place = if bindings.contains(name) {
                "local binding"
            } else if tactics.contains(name) {
                "tactic"
            } else {
                "UNPLACED"
            };
            let held = holders(name);
            let placed = if expect_binding {
                bindings.contains(name)
            } else {
                tactics.contains(name)
            };
            // One reconciliation, and it is the position law demonstrating itself: `Compression`
            // declares a STRUCTURE FIELD named `exact`. The same surface is a tactic in one frame
            // and a field in another, so `exact` in term position there is correct and the control
            // requires exactly that holder and no other.
            let reconciled: &[&str] = if *name == "exact" {
                &["Compression"]
            } else {
                &[]
            };
            let unexplained: Vec<&&str> = held
                .iter()
                .filter(|holder| !reconciled.contains(holder))
                .collect();
            if expect_binding {
                binders_clean &= placed && unexplained.is_empty();
            } else {
                tactics_clean &= placed && unexplained.is_empty();
            }
            println!(
                "  {name:<22} {place:>14}   {}",
                if held.is_empty() {
                    "-".to_owned()
                } else {
                    held.join(", ")
                }
            );
        }
    }

    println!("\n  RECONCILED, and it is the position law demonstrating itself on real material:");
    println!(
        "  `structure Compression … where … exact : ∀ i x, factor i (quotient x) = receiver i x`"
    );
    println!("  declares a FIELD named `exact`. The same surface is a tactic in one frame and a");
    println!("  field in another, which is what it means for position to be relative to a frame.");

    println!("\n  populations, over the whole development");
    println!("  --------------------------------------");
    println!("    terms            {:>6} distinct", terms.len());
    println!("    tactics          {:>6} distinct", tactics.len());
    println!("    local bindings   {:>6} distinct", bindings.len());

    let edges: usize = plural
        .declared_recruitment()
        .values()
        .map(BTreeSet::len)
        .sum();

    // THE ORBIT. `CLAUDE.md` §8: a gauge whose group acts trivially on the declared material is not
    // a gauge. Position can only move an edge if a DECLARED name lands in `tactics` or in
    // `local_bindings`. Both populations are exhibited; if both are empty the transformation cannot
    // move the quantity and the equality below is evidence of nothing.
    let tactic_declared = plural.tactic_position_declared();
    let binding_declared = plural.binding_position_declared();
    let orbit = tactic_declared.len() + binding_declared.len();

    println!("\n  THE ORBIT, before the null is read");
    println!("  ---------------------------------");
    println!(
        "    declared names in tactic position   {}",
        tactic_declared.len()
    );
    println!(
        "    declared names in binding position  {}",
        binding_declared.len()
    );
    if orbit == 0 {
        println!("\n    ORBIT TRIVIAL -- and this REFUSES the edge-count null as evidence.");
        println!("    No declared name lands in either moved population, so `edges == {EDGES}` is");
        println!("    structurally immune to position and could not have come out otherwise.");
        println!(
            "    `CLAUDE.md` §8: \"a gauge whose group acts trivially on the declared material"
        );
        println!(
            "    is not a gauge\". The check below is a REGRESSION SNAPSHOT, not a null, and it"
        );
        println!("    is reported as one. Position does delete edges on material that varies the");
        println!(
            "    property -- `fun (x : Carrier) => ...` founds `Carrier` as a binder -- which is"
        );
        println!("    what `binding_position_declared` exists to catch and why it was built.");
    }
    println!("\n    declared -> declared edges  {edges}  against control 1's {EDGES}  (snapshot)");

    println!("\n  OPEN -- dot projections the reading cannot certify without the receiver's type");
    println!("  ----------------------------------------------------------------------------");
    for (from, set) in plural.open_projections() {
        for (written, tail) in set {
            println!("    {from:<28} --{written}-->  {tail}");
        }
    }
    println!("    `htrace.map` really is the declared `Trace.map`; `(hxy i).trans` is mathlib's");
    println!(
        "    `Eq.trans` and NOT this development's `trans`, though the spelling is identical."
    );
    println!("    Telling them apart needs the receiver's TYPE. Returned OPEN, never joined.");

    println!("\n  the two bounding instruments, each returned rather than acted on");
    println!("  ----------------------------------------------------------------");
    let tactic_declared = plural.tactic_position_declared();
    println!(
        "    structural residue -- declared names found in tactic position: {}",
        tactic_declared.len()
    );
    for (name, holders) in tactic_declared.iter().take(6) {
        println!("      {name:<32} in {}", holders.join(", "));
    }
    let singular = plural.single_occurrence_terms();
    println!(
        "    distributional residue -- terms in exactly one declaration, declared nowhere: {}",
        singular.len()
    );
    println!("      (environment lemmas used once are indistinguishable from a missed local");
    println!(
        "       binding without a second frame, so the population is returned, not subtracted)"
    );

    controls.push((
        binders_clean && tactics_clean && edges == EDGES,
        format!(
            "control 8 -- binders and tactics leave the term population (edge equality is a {} )",
            if orbit == 0 {
                "SNAPSHOT: orbit trivial"
            } else {
                "null: orbit non-trivial"
            }
        ),
        format!(
            "{} terms, {} tactics, {} bindings, {edges} edges, orbit {orbit}",
            terms.len(),
            tactics.len(),
            bindings.len()
        ),
    ));
}

/// Control 9 -- the sub-illicium: a completion at depth k is an arrival at depth k+1.
fn control_nine_sub_illicium(
    plural: &DevelopmentReading,
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROL 9 -- THE SUB-ILLICIUM: A COMPLETION IS AN ARRIVAL ONE GRAIN UP");

    println!(
        "\n  `crates/holonic-body/src/manifold.rs`, W9: \"the sub-illicium -- the atom-grain traversal given"
    );
    println!(
        "  the SAME live law, so the walk FEELS the standing terrain instead of dead reckoning."
    );
    println!(
        "  Its completions are THE FOLDS -- handed up as the word grain's arrivals.\" And the"
    );
    println!(
        "  carrier law: \"a completion at depth k is an arrival at depth k+1 -- the same node,"
    );
    println!("  the same verb.\"\n");

    let steps: usize = plural
        .declarations
        .iter()
        .map(|form| form.steps.len())
        .sum();
    let arrivals: usize = plural
        .declarations
        .iter()
        .map(|form| form.internal_arrivals().len())
        .sum();
    let depths = plural.internal_depths();

    println!("  proof steps founded across the development   {steps:>5}");
    println!("  internal arrivals (step recruits step)       {arrivals:>5}");
    println!(
        "  declarations with an internal depth > 1      {:>5}",
        depths.len()
    );

    println!("\n  every declaration whose proof body carries its own depth");
    println!("  --------------------------------------------------------");
    for (name, chain) in &depths {
        println!("    {name:<44} {}", chain.join("  ->  "));
    }

    println!(
        "\n  The flat reading charged every one of these bodies to its theorem as a DEPTH-ONE"
    );
    println!("  STAR, so a declaration's own depth was zero by construction. This is the leader");
    println!("  inside one declaration: each step changes the material the next step reads.");

    // The predicate that shipped was `steps > 0 && arrivals > 0 && !depths.is_empty()`, which a
    // single `obtain ⟨a, b⟩` satisfies: two names founded SIMULTANEOUSLY by one tactic on one line,
    // reported as a completion arriving at the next. 22 of the original 29 arrivals were that, and
    // 2 more crossed sibling `·` focus blocks. The law now requires what the claim actually says.
    let mut same_line = 0usize;
    let mut same_cohort = 0usize;
    let mut crossed_focus = 0usize;
    for form in &plural.declarations {
        for (from, to) in form.internal_arrivals() {
            let (a, b) = (&form.steps[from], &form.steps[to]);
            if a.line == b.line {
                same_line += 1;
            }
            if a.cohort == b.cohort {
                same_cohort += 1;
            }
            if !b.focus.starts_with(&a.focus) {
                crossed_focus += 1;
            }
        }
    }
    println!("\n  what an arrival must NOT be, and the count of each");
    println!("  ------------------------------------------------");
    println!("    founded by the same tactic (simultaneous)   {same_cohort}");
    println!("    founded on the same source line             {same_line}");
    println!("    crossing a sibling `·` focus block          {crossed_focus}");
    println!(
        "    A destructuring pattern founds its names in ONE act. Reading their token order as"
    );
    println!("    a causal chain promotes source layout into an invariant, which is the species");
    println!("    `CLAUDE.md` §0 lesson 4 convicts. Lean's `·` goal scopes are disjoint, so an");
    println!("    arrival across siblings is a leak. Both are now excluded by construction and");
    println!("    counted here so the exclusion is auditable rather than asserted.");

    let held = steps > 0
        && arrivals > 0
        && !depths.is_empty()
        && same_cohort == 0
        && same_line == 0
        && crossed_focus == 0;
    controls.push((
        held,
        "control 9 -- every internal arrival is cross-line, cross-cohort and in scope".to_owned(),
        format!(
            "{steps} steps, {arrivals} arrivals, {} with depth > 1; {same_cohort} simultaneous, {same_line} same-line, {crossed_focus} out-of-scope",
            depths.len()
        ),
    ));
}

/// Control 4 -- nothing is invented, checked against a second scanner on both materials.
fn control_four_no_over_parsing(
    materials: &[(&str, &[PathBuf])],
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROL 4 (NULL) -- NOTHING IS INVENTED, BY A SECOND SCANNER");

    println!(
        "\n  {:<30} {:>10} {:>12} {:>12}",
        "material", "organ", "independent", "agree"
    );
    println!("  {}", "-".repeat(68));
    let mut all_agree = true;
    let mut detail = String::new();
    for (name, paths) in materials {
        let reading = read_all(paths, DeclarationGrain::EveryTopLevelDeclaration);
        let organ = reading.declarations.len() + reading.unopened.len();
        let independent: usize = paths
            .iter()
            .filter_map(|path| std::fs::read_to_string(path).ok())
            .map(|text| independent_former_count(&text))
            .sum();
        let agree = organ == independent;
        all_agree &= agree;
        println!(
            "  {name:<30} {organ:>10} {independent:>12} {:>12}",
            if agree { "yes" } else { "NO" }
        );
        detail.push_str(&format!("{name} {organ}/{independent}  "));
    }
    println!("\n  The second scanner is a literal `modifier x former` prefix table asked with");
    println!("  `starts_with`; the organ steps modifiers off in a loop. They share no code. The");
    println!(
        "  scanner does not strip comments, so a former at column zero inside a block comment"
    );
    println!("  would be counted there and not here -- neither material contains one.");

    controls.push((
        all_agree,
        "control 4 (NULL) -- opened + unopened equals an independently scanned former count"
            .to_owned(),
        detail.trim_end().to_owned(),
    ));
}

/// Controls 5 and 7 -- the generated deposit, and the figure the record got wrong on it.
fn control_five_and_seven_the_generated_deposit(
    paths: &[PathBuf],
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROLS 5 AND 7 -- THE GENERATED DEPOSIT, AND WHAT THE RECORD MISSED ON IT");

    let plural = read_all(paths, DeclarationGrain::EveryTopLevelDeclaration);
    let chain = plural.declared_recruitment();

    // ---------------------------------------------------------------- control 7, the correction
    let mut multi = 0usize;
    for path in paths {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        if read_development(&text, DeclarationGrain::EveryTopLevelDeclaration)
            .declarations
            .len()
            > 1
        {
            multi += 1;
        }
    }

    println!(
        "\n  {} artifacts, {} declarations opened -- {} of them carry TWO.",
        paths.len(),
        plural.declarations.len(),
        multi
    );
    println!("\n  recruited AND declared, at the plural grain");
    println!("  ------------------------------------------");
    for (from, reached) in &chain {
        println!(
            "    {from:<32} -> {}",
            reached.iter().copied().collect::<Vec<_>>().join(", ")
        );
    }
    let reached_names: BTreeSet<&str> = chain.values().flatten().copied().collect();
    println!(
        "\n  names that can be OPENED here: {}",
        reached_names.iter().copied().collect::<Vec<_>>().join(", ")
    );
    println!("\n  The four-relation record §7 reads: \"exactly one recruited identifier in 103");
    println!(
        "  artifacts is declared\". It is {}. `exactCarrier` is a `def`, declared in this very",
        reached_names.len()
    );
    println!("  deposit and read as an ATOM by a former list that founded only `theorem`. So is");
    println!(
        "  `abbrev ExactRelay`, which nothing here recruits and which is therefore a declared"
    );
    println!("  name absent from the openable set rather than a second correction. The record's");
    println!("  material bound was measured THROUGH the same defect it was reporting, on its own");
    println!("  deposit and not only on soma/formal.");

    let correction_held = reached_names.len() == 2
        && reached_names.contains("exactCarrier")
        && reached_names.contains("formal_carry")
        && multi == 39;
    controls.push((
        correction_held,
        "control 7 -- the generated deposit declares two of what it recruits, not one".to_owned(),
        format!(
            "{} openable names, {multi} two-declaration artifacts",
            reached_names.len()
        ),
    ));

    // ------------------------------------------------- control 5, parity where the aperture is exact
    println!("\n  parity against `derivation_atlas::read_derivation`, on the artifacts where its");
    println!("  aperture is EXACT -- the ones carrying exactly one top-level declaration");
    println!("  ---------------------------------------------------------------------------");

    let mut single = 0usize;
    let mut same_name = 0usize;
    let mut same_statement = 0usize;
    let mut difference_is_preamble = 0usize;
    let mut first_divergence: Option<String> = None;

    for path in paths {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let Some(old) = read_derivation(&text) else {
            continue;
        };
        let new = read_development(&text, DeclarationGrain::EveryTopLevelDeclaration);
        if new.declarations.len() != 1 {
            continue;
        }
        let form = &new.declarations[0];
        single += 1;
        if form.name == old.name {
            same_name += 1;
        }
        if form.statement == old.statement {
            same_statement += 1;
        }
        let dropped = subtract(&old.recruited, &form.recruited);
        let added = subtract(&form.recruited, &old.recruited);
        // The old reader charged five populations to the one declaration: the terms, the tactic
        // heads, the names the declaration's own text founds, the file preamble, and the
        // `namespace X` scope line. Each is accounted here by name; nothing else may differ.
        let mut set_aside = new.preamble.clone();
        for population in [&new.scoping, &form.tactics, &form.local_bindings] {
            for (token, count) in population {
                let slot = set_aside.entry(token.clone()).or_insert(0u32);
                *slot = slot.saturating_add(*count);
            }
        }
        let accounted: BTreeMap<String, u32> = dropped
            .iter()
            .filter(|(token, count)| set_aside.get(*token).is_some_and(|held| held >= *count))
            .map(|(token, count)| (token.clone(), *count))
            .collect();
        if added.is_empty() && accounted == dropped {
            difference_is_preamble += 1;
        } else if first_divergence.is_none() {
            first_divergence = Some(format!(
                "{}: added {:?}, unaccounted {:?}",
                path.display(),
                added.keys().collect::<Vec<_>>(),
                dropped
                    .keys()
                    .filter(|token| !accounted.contains_key(*token))
                    .collect::<Vec<_>>()
            ));
        }
    }

    println!("    single-declaration artifacts       {single:>5}");
    println!("    same declared name                 {same_name:>5}");
    println!("    same statement text                {same_statement:>5}");
    println!("    difference accounted by name       {difference_is_preamble:>5}");
    if let Some(divergence) = &first_divergence {
        println!("    first divergence: {divergence}");
    }
    println!(
        "\n    The other {} artifacts are where the historical aperture is NOT exact, and their",
        paths.len() - single
    );
    println!("    disagreement is control 7's finding rather than a parity failure.");

    let parity = single > 0
        && same_name == single
        && same_statement == single
        && difference_is_preamble == single;
    controls.push((
        parity,
        "control 5 -- parity where the historical aperture is exact, every dropped token accounted"
            .to_owned(),
        format!("{single} single-declaration artifacts, {difference_is_preamble} accounted"),
    ));
}

fn subtract(left: &BTreeMap<String, u32>, right: &BTreeMap<String, u32>) -> BTreeMap<String, u32> {
    let mut found = BTreeMap::new();
    for (token, count) in left {
        let other = right.get(token).copied().unwrap_or(0);
        if *count > other {
            found.insert(token.clone(), count - other);
        }
    }
    found
}

// -------------------------------------------------------------------------------------------------
// Control 6 -- the elaboration deepens
// -------------------------------------------------------------------------------------------------

fn control_six_the_elaboration_deepens(
    plural: &DevelopmentReading,
    controls: &mut Vec<(bool, String, String)>,
) {
    section("CONTROL 6 -- THE ELABORATION REACHES PAST DEPTH ONE");

    let derivations: Vec<Derivation> = plural.derivations(ConductGrain::TermsOnly);
    let deposit = ElaborationDeposit::read(&derivations);

    let mut deepest: Option<(String, usize, usize)> = None;
    let mut past_one = 0usize;
    let mut roots: Vec<String> = deposit
        .declared_names()
        .into_iter()
        .map(str::to_owned)
        .collect();
    roots.sort();

    for root in &roots {
        let Ok(meaning) = deposit.elaborate(root, ElaborationAperture::Exhausted) else {
            continue;
        };
        let depth = meaning
            .constituents()
            .values()
            .map(|constituent| constituent.entered_at)
            .max()
            .unwrap_or(0);
        if depth > 1 {
            past_one += 1;
        }
        let size = meaning.constituents().len();
        if deepest.as_ref().is_none_or(|(_, best, best_size)| {
            depth > *best || (depth == *best && size > *best_size)
        }) {
            deepest = Some((root.clone(), depth, size));
        }
    }

    println!(
        "\n  {} of {} declared roots carry a constituent past depth one",
        past_one,
        roots.len()
    );

    if let Some((root, depth, size)) = &deepest {
        println!("\n  the deepest meaning in the development");
        println!("  --------------------------------------");
        println!("    root   {root}");
        println!("    depth  {depth}");
        println!("    size   {size} constituents");
        if let Ok(meaning) = deposit.elaborate(root, ElaborationAperture::Exhausted) {
            let mut by_depth: BTreeMap<usize, Vec<&str>> = BTreeMap::new();
            for constituent in meaning.constituents().values() {
                by_depth
                    .entry(constituent.entered_at)
                    .or_default()
                    .push(constituent.name.as_str());
            }
            for (depth, mut names) in by_depth {
                names.sort_unstable();
                println!("      depth {depth}   {}", names.join(", "));
            }
            println!("\n    the arrivals, in walk order");
            for arrival in meaning.arrivals() {
                println!(
                    "      {:<40} -> {:<40} depth {}",
                    arrival.from, arrival.to, arrival.at_depth
                );
            }
        }
    }

    let held = deepest.as_ref().is_some_and(|(_, depth, _)| *depth >= 3);
    controls.push((
        held,
        "control 6 -- a declared root reaches depth >= 3".to_owned(),
        deepest.map_or_else(
            || "no root elaborated".to_owned(),
            |(root, depth, size)| format!("{root} at depth {depth}, {size} constituents"),
        ),
    ));
}

// -------------------------------------------------------------------------------------------------

fn verdict(controls: &[(bool, String, String)]) {
    section("THE CONTROLS");
    let mut failed = 0usize;
    for (held, name, detail) in controls {
        println!("  [{}] {name}", if *held { "HELD" } else { "FAIL" });
        println!("         {detail}");
        if !held {
            failed += 1;
        }
    }
    println!(
        "\n  {} of {} controls held",
        controls.len() - failed,
        controls.len()
    );
    if failed > 0 {
        std::process::exit(1);
    }
}
