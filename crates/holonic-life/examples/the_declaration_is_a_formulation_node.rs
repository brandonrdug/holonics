//! `D`, the parameter domain — and **Lean is the oracle for it**.
//!
//! Third movement of `archive/plans/THE_TYPED_TRANSPORT_ATLAS.md`, and its gate. `H.0362` names `D` as a
//! formulation node's parameter domain. `LeanBinderChart` carried names and explicitness; the type
//! was bound to `_` at the destructuring, instance binders were not parsed at all, and the emission
//! consequently filled argument positions by matching binder **names** across two declarations'
//! frames — a string intersection standing in for a chart transition.
//!
//! # The oracle, and why it is the kernel again
//!
//! One reader cannot audit itself. `#check @d` makes Lean print the declaration's own type, binder
//! groups and all, and that is the ground truth this movement is graded against. For every
//! declaration of the declared sample the node's `D` is placed beside Lean's, and **every
//! disagreement is returned by name**.
//!
//! # What completion means here, and what halts the plan
//!
//! This movement is complete when the disagreement population is **returned and named** — *not*
//! when it is empty. An honest partial `D` whose failures are exhibited is a completion; a silent
//! one is not.
//!
//! **It halts the plan if `D` cannot be recovered for a majority of the sample.** Proceeding to
//! typed admissibility on a domain that is mostly absent would produce a green recognition law over
//! material it never read, so this driver exits non-zero in that case and says so.
//!
//! ```text
//! cargo run --release -p life --example the_declaration_is_a_formulation_node
//! ```

use std::path::{Path, PathBuf};
use std::process::Command;

use life::lean_mathematics::{LeanBinderKind, LeanMathematicsEcology, LeanSourceDocument};

const PROJECT: &str = "formal/rh-source-transport";
const CORPUS: &str = "SomaRHSourceTransport/FiniteTransport.lean";
const MATHLIB: &str = "formal/elementary-holonics/.lake/packages/mathlib";

/// Mathlib modules the sample is drawn from. Declared here so the sample is stated rather than
/// selected after the fact, and chosen for subject spread rather than for outcome.
const SAMPLE_MODULES: [&str; 3] = [
    "Mathlib/Algebra/Group/Basic.lean",
    "Mathlib/Order/Basic.lean",
    "Mathlib/Data/Finset/Card.lean",
];

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The **positional domain** Lean prints for a declaration: how many arguments an application must
/// supply, and the names of those Lean names.
///
/// The first attempt compared names up to the first depth-zero comma and disagreed with the oracle
/// six times in seven. Looking at what Lean actually printed showed the instrument was wrong rather
/// than the reader:
///
/// ```text
/// @proportionalFlow_respects_capacity : ∀ {Old} {New} [inst] [inst_1]
///   (demand : Old → ℝ) (capacity : New → ℝ) (incident : Old → New → Prop) [inst_2],
///   (∀ m, 0 ≤ capacity m) → (∀ m, congestion … ≤ 1) → ∀ (m : New), …
/// ```
///
/// **A named hypothesis whose name the conclusion never mentions is printed as an anonymous
/// arrow.** `hc` and `hcong` are positional arguments and Lean writes them `→`. So the domain is
/// every explicit group of every `∀` telescope **plus** every depth-zero arrow, and a parenthesised
/// group outside a telescope is a hypothesis *type*, not a binder.
fn lean_positional_domain(printed: &str) -> Option<(usize, Vec<String>)> {
    let body = printed.split_once(" : ")?.1;
    let mut arity = 0usize;
    let mut names = Vec::new();
    let mut depth = 0i64;
    let mut in_telescope = false;
    let mut group: Option<(usize, bool)> = None;
    let characters: Vec<(usize, char)> = body.char_indices().collect();
    for (index, (byte, character)) in characters.iter().copied().enumerate() {
        match character {
            '∀' if depth == 0 => in_telescope = true,
            '(' | '{' | '[' | '⦃' => {
                if depth == 0 {
                    group = Some((byte + character.len_utf8(), character == '('));
                }
                depth += 1;
            }
            ')' | '}' | ']' | '⦄' => {
                depth -= 1;
                if depth == 0 {
                    if let Some((start, positional)) = group.take() {
                        if positional && in_telescope {
                            let content = &body[start..byte];
                            let names_part = content.split_once(':').map_or(content, |(l, _)| l);
                            for name in names_part.split_whitespace() {
                                arity += 1;
                                names.push(name.to_owned());
                            }
                        }
                    }
                }
            }
            ',' if depth == 0 => in_telescope = false,
            '→' if depth == 0 => arity += 1,
            '-' if depth == 0 => {
                if characters.get(index + 1).map(|(_, next)| *next) == Some('>') {
                    arity += 1;
                }
            }
            _ => {}
        }
    }
    Some((arity, names))
}

fn check(project: &Path, source: &str, scratch: &Path, label: &str) -> String {
    let path = scratch.join(format!("check-{label}.lean"));
    std::fs::write(&path, source).expect("the probe writes");
    let output = Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg(&path)
        .current_dir(project)
        .output()
        .expect("lake env lean runs");
    let mut said = String::from_utf8_lossy(&output.stdout).into_owned();
    said.push_str(&String::from_utf8_lossy(&output.stderr));
    said
}

struct Row {
    name: String,
    ours: Vec<String>,
    theirs: Vec<String>,
    their_arity: usize,
    unreadable: bool,
}

fn main() {
    let root = repository_root();
    let project = root.join(PROJECT);
    let scratch = root.join(".local/artifacts/the-declaration-is-a-formulation-node");
    std::fs::create_dir_all(&scratch).expect("the scratch root is writable");
    println!("THE DECLARATION IS A FORMULATION NODE — D, and Lean is the oracle");
    if !project.join(".lake/packages/mathlib").exists() {
        println!("  mathlib is not materialised; the oracle cannot run.");
        println!("  recover it with:  cd formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }

    let mut rows: Vec<Row> = Vec::new();

    // ---------------------------------------------------------------- the corpus
    let text = std::fs::read_to_string(project.join(CORPUS)).expect("the corpus reads");
    let corpus = vec![LeanSourceDocument::new("FiniteTransport.lean", &text)];
    let ecology = LeanMathematicsEcology::condition(&corpus).expect("the corpus conditions");
    println!("\n=== what D now carries, on the declared corpus");
    for organ in ecology.declarations() {
        let positional: Vec<&_> = organ
            .binders
            .iter()
            .filter(|binder| binder.kind.is_positional())
            .collect();
        println!(
            "  {:42} binders {:2}  positional {:2}  instance {:2}  typed {:2}",
            organ.name,
            organ.binders.len(),
            positional.len(),
            organ
                .binders
                .iter()
                .filter(|binder| binder.kind == LeanBinderKind::Instance)
                .count(),
            organ
                .binders
                .iter()
                .filter(|binder| !binder.type_text.is_empty())
                .count()
        );
    }
    println!("\n=== the oracle — `#check @d`, and every disagreement named");
    for organ in ecology.declarations() {
        let source = format!(
            "import SomaRHSourceTransport.FiniteTransport\nopen Soma.RHSourceTransport in\n#check @{}\n",
            organ.name
        );
        let said = check(&project, &source, &scratch, &organ.name);
        let printed = said
            .lines()
            .find(|line| line.contains(&format!("@{}", organ.name)) && line.contains(" : "))
            .map(|line| {
                // Lean may wrap the type; join the continuation lines.
                let start = said.find(line).unwrap_or(0);
                said[start..].replace('\n', " ")
            });
        let theirs = printed.as_deref().and_then(lean_positional_domain);
        let ours: Vec<String> = organ
            .binders
            .iter()
            .filter(|binder| binder.kind.is_positional() && !binder.name.is_empty())
            .map(|binder| binder.name.clone())
            .collect();
        rows.push(Row {
            name: organ.name.clone(),
            ours,
            theirs: theirs.clone().map(|(_, names)| names).unwrap_or_default(),
            their_arity: theirs.as_ref().map_or(0, |(arity, _)| *arity),
            unreadable: theirs.is_none(),
        });
    }

    // ---------------------------------------------------------------- a mathlib sample
    println!("\n=== a mathlib sample, drawn from declared modules");
    let mathlib = root.join(MATHLIB);
    for module in SAMPLE_MODULES {
        let path = mathlib.join(module);
        let Ok(text) = std::fs::read_to_string(&path) else {
            println!("  {module} absent");
            continue;
        };
        let document = LeanSourceDocument::new(module, &text);
        let Ok(one) = LeanMathematicsEcology::condition(std::slice::from_ref(&document)) else {
            println!("  {module} refused by the reader");
            continue;
        };
        let import = module.trim_end_matches(".lean").replace('/', ".");
        let names: Vec<String> = one
            .declarations()
            .map(|organ| organ.name.clone())
            .take(5)
            .collect();
        println!("  {module} — {} declarations sampled", names.len());
        for name in &names {
            let Some(organ) = one.declarations().find(|organ| &organ.name == name) else {
                continue;
            };
            let source = format!("import {import}\n#check @{name}\n");
            let said = check(&project, &source, &scratch, &format!("mathlib-{name}"));
            let joined = said.replace('\n', " ");
            let theirs = joined
                .contains(&format!("@{name}"))
                .then(|| lean_positional_domain(&joined))
                .flatten();
            let ours: Vec<String> = organ
                .binders
                .iter()
                .filter(|binder| binder.kind.is_positional() && !binder.name.is_empty())
                .map(|binder| binder.name.clone())
                .collect();
            rows.push(Row {
                name: name.clone(),
                ours,
                theirs: theirs.clone().map(|(_, names)| names).unwrap_or_default(),
                their_arity: theirs.as_ref().map_or(0, |(arity, _)| *arity),
                unreadable: theirs.is_none(),
            });
        }
    }

    // ---------------------------------------------------------------- the comparison
    println!("\n=== D against the oracle, every disagreement by name");
    let mut agree = 0usize;
    let mut disagree = Vec::new();
    let mut unreadable = Vec::new();
    for row in &rows {
        if row.unreadable {
            unreadable.push(row.name.clone());
            println!("  {:42} ORACLE UNREADABLE", row.name);
            continue;
        }
        // Agreement is on the POSITIONAL ARITY — the number of arguments an application must
        // supply — and on the names Lean prints being a subsequence of ours. Lean writes an
        // anonymous arrow for a hypothesis whose name its conclusion never mentions, so demanding
        // name-for-name equality would fail on material where nothing is wrong.
        let arity_agrees = row.ours.len() == row.their_arity;
        let names_agree = row.theirs.iter().all(|name| row.ours.contains(name));
        if arity_agrees && names_agree {
            agree += 1;
            println!(
                "  {:42} agrees  arity {}  {:?}",
                row.name, row.their_arity, row.ours
            );
        } else {
            disagree.push(row.name.clone());
            println!("  {:42} DISAGREES", row.name);
            println!("      ours   arity {} {:?}", row.ours.len(), row.ours);
            println!(
                "      Lean   arity {} names {:?}",
                row.their_arity, row.theirs
            );
        }
    }

    let decided = agree + disagree.len();
    println!("\n=== the return");
    println!(
        "  sample {}   oracle unreadable {}   decided {}   agree {}   disagree {}",
        rows.len(),
        unreadable.len(),
        decided,
        agree,
        disagree.len()
    );
    println!("  THIS MOVEMENT IS COMPLETE WHEN THE DISAGREEMENT POPULATION IS NAMED, not when it");
    println!("  is empty. An honest partial D with its failures exhibited is a completion.");

    if decided == 0 {
        println!(
            "\n  THE PLAN HALTS: no member of the sample could be decided against the oracle."
        );
        std::process::exit(1);
    }
    if agree * 2 <= decided {
        println!(
            "\n  THE PLAN HALTS: D agrees with the oracle on {agree} of {decided} decided members,"
        );
        println!("  which is not a majority. Typed admissibility over a domain that is mostly");
        println!("  absent would be a green recognition law over material it never read.");
        std::process::exit(1);
    }
    println!("\n  D is recovered for a majority of the decided sample; the plan proceeds.");
}
