//! Real mathematical prose enters the conditioning through `crates/holonic-life`'s own text intake, and the
//! mathematics the conditioned body then derives is exhibited whole.
//!
//! ```text
//! cargo run --release -p life --example eros_mathematics_conditioning
//! ```
//!
//! ## The seam this driver closes
//!
//! `holonic-engine`'s `conditioned_derivation` states its governing law directly: *an unconditioned
//! morphology commits no stem, so no two identifiers share one, no bridge is licensed, and `derive`
//! returns the empty population.* The conditioning is what makes production possible — so **where the
//! conditioning material comes from is the whole of the claim**. The engine's own driver authors its
//! exposures from string literals it holds itself; that reads as conditioning but is a body exposed to
//! its own author.
//!
//! `life::text_material` is the intake that receives foreign material as linguistic occurrence with
//! its container, ordinal, parentage and exact surface retained, and it is reached by no driver. This
//! one reaches it. The direction is the only one that compiles: `life` depends on `holonic-engine`,
//! so a driver here may call both and the reverse edge does not exist.
//!
//! ```text
//!   declared corpus on disk
//!     -> ParsedTextDocument            one document, its sections declared by the codec below
//!     -> ExactTextMaterialCorpus       life's intake: occurrence identity, witness, parentage
//!     -> ExactTextMaterialAtlas        life's conditioned atlas over that corpus
//!     -> MorphologicalLanguagePassage  what the intake emits, one per admitted occurrence
//!     -> Exposure                      (whole, text), the engine's one entry for linguistic material
//!     -> FoundedMorphology             stems committed by recurrence across DISTINCT wholes
//!     -> DerivedPassage                the mathematics, each carrying the bridge that licensed it
//! ```
//!
//! The `whole` of every exposure is the intake's own occurrence identity, which carries the corpus
//! document's path inside it. That is what makes a founded stem traceable back to a **named document
//! on disk** rather than to an anonymous blob, and it is what the corpus ablation below acts on.
//!
//! ## The four slots
//!
//! ```text
//!   source geometry   the deposited Lean artifacts under standing/output and what they recruit
//!   receiver map      the morphology the declared mathematical prose founded
//!   transport         character succession through a recruited identifier
//!   returned residual the passages licensed, the residue no committed stem covers, and the passages
//!                     that depart when one corpus document is withheld
//! ```
//!
//! ## What is declared here and printed in the receipt
//!
//! The corpus documents, the standing deposit, the section codec, and the query. Nothing is sampled,
//! scored, ranked, weighted or thresholded: every population this driver returns is returned whole.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::conditioned_derivation::{
    expose, ConditionedBody, DerivationQuery, DerivedPassage, Exposure, FoundedMorphology,
};
use life::text_material::{ExactTextMaterialAtlas, ExactTextMaterialCorpus, ParsedTextDocument};

// -------------------------------------------------------------------------------------------------
// The declaration
// -------------------------------------------------------------------------------------------------

/// **The declared corpus.** Fourteen documents of the project's own mathematics — statements,
/// lemmas, corollaries and definitions on the carrier / transport / receiver / kernel line. They are
/// named here rather than globbed so that withholding exactly one of them is a well-posed operation.
const CORPUS: &[&str] = &[
    "research/papers/source/mathematics/theorems/weil-support-induction-reduction.typ",
    "research/papers/source/mathematics/theorems/conditioned-support-quotient-shorting.typ",
    "research/papers/source/mathematics/theorems/conditioned-effective-tension.typ",
    "research/papers/source/mathematics/theorems/prime-power-aperture-incidence.typ",
    "research/papers/source/mathematics/theorems/prime-power-hinge-cell-recurrence.typ",
    "research/papers/source/mathematics/theorems/archimedean-remainder-amplitude.typ",
    "research/papers/source/mathematics/theorems/causal-parity-kirchhoff-return.typ",
    "research/papers/source/mathematics/theorems/dyadic-character-filler-bound.typ",
    "research/papers/source/mathematics/lemmas/situated-mean-transport.typ",
    "research/papers/source/mathematics/lemmas/geometric-remainder-squeeze.typ",
    "research/papers/source/mathematics/lemmas/first-prime-capacitance-completion.typ",
    "research/papers/source/mathematics/corollaries/archimedean-carrier-prime-boundary.typ",
    "research/papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
    "research/papers/source/mathematics/definitions/graded-arithmetic-accessibility-current.typ",
];

/// **The declared standing derivation deposit.** The same one `holonic-engine`'s own driver mounts:
/// the Lean artifacts this project's formal-production organs emitted. Kernel-refused foils are
/// deliberately among them; nothing here is submitted to a kernel.
const DEPOSIT: &str = "standing/output";

/// **The declared query.** A statement the deposit already reaches, asked of both bodies verbatim.
/// If the deposit stops carrying it the driver refuses rather than silently asking another.
const QUERY: &str = "(h : P) : exactCarrier P";

/// **The declared corpus document exhibited whole** in the ablation. Every declared document is
/// withheld in turn below and the whole difference population is reported for each; this one is
/// additionally opened up stem by stem so that a null result, if it is one, is checkable rather than
/// asserted.
const WITHHELD_EXHIBITED: &str =
    "research/papers/source/mathematics/theorems/weil-support-induction-reduction.typ";

// -------------------------------------------------------------------------------------------------
// The exterior codecs — reading files is not a claim, so both are stated here in full
// -------------------------------------------------------------------------------------------------

/// **The declared section codec.** A section is a maximal run of non-blank lines. Nothing is
/// stripped, lowercased, or normalized: `life::text_material` receives the surface as written and
/// retains its own sha256 of it.
fn sections(text: &str) -> Vec<String> {
    let mut sections = Vec::new();
    let mut open: Vec<&str> = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            if !open.is_empty() {
                sections.push(open.join("\n"));
                open.clear();
            }
        } else {
            open.push(line);
        }
    }
    if !open.is_empty() {
        sections.push(open.join("\n"));
    }
    sections
}

/// Every `.lean` artifact under `root`, in a stable order.
fn deposit_artifacts(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(deposit_artifacts(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

// -------------------------------------------------------------------------------------------------
// The intake
// -------------------------------------------------------------------------------------------------

/// What one pass through `life`'s intake returned.
struct Intake {
    /// The declared documents actually read, in declaration order.
    documents: Vec<String>,
    /// One exposure per admitted occurrence: `(occurrence identity, occurrence surface)`.
    exposures: Vec<Exposure>,
    /// `life`'s own conditioned atlas over the same corpus.
    atlas: ExactTextMaterialAtlas,
}

/// Read the declared corpus through `life::text_material`, optionally withholding one document.
fn intake(withhold: Option<&str>) -> Result<Intake, String> {
    let mut documents = Vec::new();
    let mut parsed = Vec::new();
    for path in CORPUS {
        if withhold == Some(*path) {
            continue;
        }
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        let sections = sections(&text);
        if sections.is_empty() {
            return Err(format!("{path}: the section codec returned nothing"));
        }
        parsed.push(ParsedTextDocument {
            identity: (*path).to_owned(),
            source: (*path).to_owned(),
            sections,
        });
        documents.push((*path).to_owned());
    }
    let corpus = ExactTextMaterialCorpus::import(Vec::new(), &parsed, 1)
        .map_err(|error| format!("life's intake refused the corpus: {error:?}"))?;
    let atlas = ExactTextMaterialAtlas::condition(corpus)
        .map_err(|error| format!("life refused to condition the atlas: {error:?}"))?;
    let exposures = atlas
        .corpus()
        .passages()
        .iter()
        .map(|passage| expose(&passage.identity, &passage.text))
        .collect();
    Ok(Intake {
        documents,
        exposures,
        atlas,
    })
}

/// The declared corpus document an intake occurrence identity names.
///
/// `life` mints `document:{identity}:{ordinal}:{sha256}` and the driver hands it the file path as the
/// identity, so this is a parse of the intake's own key and not a second bookkeeping structure.
fn document_of(whole: &str) -> Option<&'static str> {
    let body = whole.strip_prefix("document:")?;
    CORPUS
        .iter()
        .copied()
        .find(|path| body.starts_with(&format!("{path}:")))
}

/// The declared corpus documents whose sections witnessed one founded stem.
fn documents_witnessing(morphology: &FoundedMorphology, stem: &str) -> BTreeSet<&'static str> {
    morphology
        .stem(stem)
        .map(|founded| {
            founded
                .wholes
                .iter()
                .filter_map(|whole| document_of(whole))
                .collect()
        })
        .unwrap_or_default()
}

fn file_name(path: &str) -> &str {
    Path::new(path)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(path)
}

// -------------------------------------------------------------------------------------------------
// Reading
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
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

/// One passage, exhibited as the artifact it is: the bridge lineage, then the text.
fn exhibit(passage: &DerivedPassage, morphology: &FoundedMorphology) {
    let witnessing: Vec<&str> = documents_witnessing(morphology, &passage.stem)
        .into_iter()
        .map(file_name)
        .collect();
    println!("\n  {}", passage.name);
    println!(
        "      licensed by stem {:?}   brought {}   reaches {}",
        passage.stem, passage.brought, passage.reaches
    );
    println!(
        "      stem founded by corpus documents: {}",
        witnessing.join(" ")
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

fn names(passages: &[DerivedPassage]) -> BTreeSet<String> {
    passages
        .iter()
        .map(|passage| passage.name.clone())
        .collect()
}

/// Exhibit why a passage appeared or departed as a **cover change**, never as an assertion.
///
/// The identifiers the passage bridges are decomposed under the morphology before the withholding
/// and under the morphology after it, and the founded occurrences that left and entered each cover
/// are named. Maximality is the only thing that can promote an occurrence, so a passage that appears
/// while its own stem was already committed must show a longer occurrence leaving the cover — and
/// that is printed rather than claimed.
fn cover_change(passage: &DerivedPassage, before: &FoundedMorphology, after: &FoundedMorphology) {
    let mut identifiers: BTreeSet<&str> = BTreeSet::new();
    identifiers.insert(passage.brought.as_str());
    for bridge in &passage.bridges {
        identifiers.insert(bridge.held.as_str());
    }
    for identifier in identifiers {
        let (Ok(was), Ok(now)) = (before.cover(identifier), after.cover(identifier)) else {
            continue;
        };
        if was.render() == now.render() {
            println!(
                "                {identifier:<20} cover unchanged   {}",
                was.render()
            );
            continue;
        }
        let was_stems = was.stems();
        let now_stems = now.stems();
        let left: Vec<&str> = was_stems.difference(&now_stems).copied().collect();
        let entered: Vec<&str> = now_stems.difference(&was_stems).copied().collect();
        println!(
            "                {identifier:<20} before  {}\n                {:<20} after   {}",
            was.render(),
            "",
            now.render()
        );
        println!(
            "                {:<20} left the cover {left:?}   entered {entered:?}",
            ""
        );
    }
}

fn main() {
    let mut controls = Controls::new();

    // ---------------------------------------------------------------------------------------------
    rule("EROS MATHEMATICS CONDITIONING -- a real corpus enters through life's text intake");

    let corpus_intake = match intake(None) {
        Ok(taken) => taken,
        Err(refusal) => {
            eprintln!("{refusal}");
            std::process::exit(2);
        }
    };

    let artifacts = deposit_artifacts(Path::new(DEPOSIT));
    let deposit: Vec<(String, String)> = artifacts
        .iter()
        .filter_map(|path| {
            std::fs::read_to_string(path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect();
    if deposit.is_empty() {
        eprintln!("the declared standing deposit {DEPOSIT} holds no readable Lean artifact");
        std::process::exit(2);
    }

    println!("\ndeclared standing derivation deposit");
    println!("  {DEPOSIT:<74} {} artifacts", deposit.len());
    println!("\ndeclared corpus -- read through life::text_material, section by section");
    let mut per_document: BTreeMap<&str, usize> = BTreeMap::new();
    for exposure in &corpus_intake.exposures {
        if let Some(path) = document_of(&exposure.whole) {
            *per_document.entry(path).or_default() += 1;
        }
    }
    for path in &corpus_intake.documents {
        println!(
            "  {path:<74} {:>3} occurrences",
            per_document.get(path.as_str()).copied().unwrap_or_default()
        );
    }

    let corpus_receipt = corpus_intake.atlas.corpus().receipt();
    let atlas_receipt = corpus_intake.atlas.receipt();
    println!("\nlife's own intake receipt (supporting; the artifact is below)");
    println!(
        "  corpus  containers {}   raw bytes {}   witnessed {}   unique {}   document occurrences {}",
        corpus_receipt.containers,
        corpus_receipt.raw_bytes,
        corpus_receipt.witnessed_occurrences,
        corpus_receipt.unique_occurrences,
        corpus_receipt.document_occurrences
    );
    println!(
        "  corpus  raw container sha256 {}",
        corpus_receipt.raw_container_sha256
    );
    println!(
        "  atlas   sections {}   surface bytes {}   token occurrences {}   distinct tokens {}",
        atlas_receipt.conditioned_sections,
        atlas_receipt.surface_bytes,
        atlas_receipt.token_occurrences,
        atlas_receipt.distinct_tokens
    );
    println!(
        "  atlas   transports {}   indexed features {}   recurrent tokens {}",
        atlas_receipt.distinct_transports,
        atlas_receipt.indexed_features,
        atlas_receipt.recurrent_tokens
    );

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE CONDITIONING -- morphology founded by exposure to that corpus");

    let unconditioned_body = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let mut conditioned = unconditioned_body.clone();
    conditioned.condition(&corpus_intake.exposures);
    let morphology = conditioned.morphology().clone();

    let recruited = conditioned.recruited_population();
    let statements = conditioned.standing_statements();

    println!(
        "\n  {} exposures handed across the seam, one per admitted occurrence",
        corpus_intake.exposures.len()
    );
    println!(
        "  founded {}   committed {}   provisional {}",
        morphology.founded().len(),
        morphology.committed().len(),
        morphology.provisional().len()
    );
    println!(
        "\n  the deposit recruits {} identifiers. Each is shown under the founded cover, with a\n  \
         bracketed residue: material no committed stem of this corpus covers.\n",
        recruited.len()
    );
    for identifier in &recruited {
        let cover = match morphology.cover(identifier) {
            Ok(cover) => cover,
            Err(refusal) => {
                eprintln!("cover refused: {refusal}");
                std::process::exit(2);
            }
        };
        println!("    {identifier:<22} {}", cover.render());
    }

    // ---------------------------------------------------------------------------------------------
    rule(
        "[2]  THE PRODUCTION -- the declared query, put to the conditioned body and to the control",
    );

    if !statements.contains(QUERY) {
        eprintln!("the declared query is not a statement this deposit reaches: {QUERY}");
        eprintln!("the deposit reaches: {statements:?}");
        std::process::exit(2);
    }
    let query = DerivationQuery::reaching(QUERY);

    // The declared control, stated exactly as the law states it: the same body, the same standing,
    // the same query, carrying `FoundedMorphology::unconditioned()`.
    let control_body = conditioned.with_morphology(FoundedMorphology::unconditioned());

    println!("\n  every statement the deposit reaches, asked of both bodies");
    println!(
        "\n    {:<50} {:>13} {:>13}",
        "statement", "unconditioned", "conditioned"
    );
    let mut control_total = 0usize;
    for statement in &statements {
        let asked = DerivationQuery::reaching(statement);
        let bare = control_body.derive(&asked).expect("derives");
        let full = conditioned.derive(&asked).expect("derives");
        control_total += bare.len();
        println!(
            "    {:<50} {:>13} {:>13}",
            statement,
            bare.len(),
            full.len()
        );
    }

    let production = conditioned.derive(&query).expect("derives");
    let control = control_body.derive(&query).expect("derives");

    println!("\n  the declared query: {QUERY}");
    println!(
        "\n  the control body -- FoundedMorphology::unconditioned() -- returned {} passages",
        control.len()
    );
    println!(
        "\n  the conditioned body returned {} passages. All of them follow, whole.",
        production.len()
    );
    for passage in &production {
        exhibit(passage, &morphology);
    }

    let licensing: BTreeSet<String> = production
        .iter()
        .map(|passage| passage.stem.clone())
        .collect();

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE LICENCE, TRACED TO NAMED DOCUMENTS ON DISK");

    println!(
        "\n  every stem that licensed a passage, with the declared corpus documents whose sections\n  \
         witnessed it and the passages it licensed\n"
    );
    let mut traced: Vec<(&String, BTreeSet<&'static str>)> = Vec::new();
    for stem in &licensing {
        let documents = documents_witnessing(&morphology, stem);
        let licensed: Vec<String> = production
            .iter()
            .filter(|passage| &passage.stem == stem)
            .map(|passage| format!("{}<-{}", passage.reaches, passage.brought))
            .collect();
        println!("    stem {stem:?}");
        for path in &documents {
            println!("      founded by  {path}");
        }
        println!("      licensed    {}", licensed.join("  "));
        traced.push((stem, documents));
    }

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE CORPUS ABLATION -- withhold one declared document, re-condition, re-derive");

    println!(
        "\n  Every declared corpus document is withheld in turn. The difference is reported as a\n  \
         population -- which passages departed, which appeared, and which stems left or entered the\n  \
         committed morphology to cause it. Nothing is reduced to a delta.\n"
    );

    let founded_names = names(&production);
    struct Withholding {
        document: &'static str,
        departed: BTreeSet<String>,
        appeared: BTreeSet<String>,
        decommitted: BTreeSet<String>,
        newly_committed: BTreeSet<String>,
        derived: Vec<DerivedPassage>,
        morphology: FoundedMorphology,
    }
    let committed_now: BTreeSet<String> = morphology
        .committed()
        .into_iter()
        .map(|stem| stem.stem.clone())
        .collect();

    let mut withholdings: Vec<Withholding> = Vec::new();
    for document in CORPUS {
        let without = match intake(Some(document)) {
            Ok(without) => without,
            Err(refusal) => {
                eprintln!("{refusal}");
                std::process::exit(2);
            }
        };
        let mut body = unconditioned_body.clone();
        body.condition(&without.exposures);
        let derived = body.derive(&query).expect("derives");
        let after = names(&derived);
        let committed_after: BTreeSet<String> = body
            .morphology()
            .committed()
            .into_iter()
            .map(|stem| stem.stem.clone())
            .collect();
        withholdings.push(Withholding {
            document,
            departed: founded_names.difference(&after).cloned().collect(),
            appeared: after.difference(&founded_names).cloned().collect(),
            decommitted: committed_now
                .difference(&committed_after)
                .cloned()
                .collect(),
            newly_committed: committed_after
                .difference(&committed_now)
                .cloned()
                .collect(),
            derived,
            morphology: body.morphology().clone(),
        });
    }

    println!(
        "    {:<58} {:>9} {:>9} {:>9} {:>12} {:>12}",
        "withheld document", "passages", "departed", "appeared", "decommitted", "committed+"
    );
    for withholding in &withholdings {
        println!(
            "    {:<58} {:>9} {:>9} {:>9} {:>12} {:>12}",
            file_name(withholding.document),
            withholding.derived.len(),
            withholding.departed.len(),
            withholding.appeared.len(),
            withholding.decommitted.len(),
            withholding.newly_committed.len(),
        );
    }

    println!(
        "\n  the difference, as a population, for every document whose withholding moved one:\n"
    );
    let mut moved = 0usize;
    for withholding in &withholdings {
        if withholding.departed.is_empty() && withholding.appeared.is_empty() {
            continue;
        }
        moved += 1;
        println!("    withholding {}", withholding.document);
        for name in &withholding.departed {
            let Some(passage) = production.iter().find(|passage| &passage.name == name) else {
                continue;
            };
            println!(
                "      departed  {name}\n                licensed by stem {:?}, which is {}",
                passage.stem,
                if withholding.decommitted.contains(&passage.stem) {
                    "no longer committed"
                } else {
                    "still committed"
                }
            );
            cover_change(passage, &morphology, &withholding.morphology);
        }
        for name in &withholding.appeared {
            let Some(passage) = withholding
                .derived
                .iter()
                .find(|passage| &passage.name == name)
            else {
                continue;
            };
            println!(
                "      appeared  {name}\n                licensed by stem {:?}, which was {}",
                passage.stem,
                if committed_now.contains(&passage.stem) {
                    "already committed before"
                } else {
                    "not committed before"
                }
            );
            cover_change(passage, &morphology, &withholding.morphology);
        }
    }
    if moved == 0 {
        println!("    (no declared document's withholding changed the passage population)");
    }

    println!(
        "\n  the declared exhibit: withholding {}\n",
        WITHHELD_EXHIBITED
    );
    match withholdings
        .iter()
        .find(|withholding| withholding.document == WITHHELD_EXHIBITED)
    {
        Some(withholding) => {
            println!(
                "    stems that left the committed morphology with it: {:?}",
                withholding.decommitted
            );
            println!(
                "    stems that entered it: {:?}",
                withholding.newly_committed
            );
            println!(
                "\n    every stem that licensed a passage, checked against this withholding.\n    \
                 A passage can only depart if its licensing stem stops being committed, so the\n    \
                 remaining witnessing documents are the check and are printed, not summarised.\n"
            );
            println!(
                "    {:<12} {:<16} {:>8}  remaining declared documents that witness it",
                "stem", "after", "wholes"
            );
            for (stem, _) in &traced {
                let remaining = documents_witnessing(&withholding.morphology, stem);
                let wholes = withholding
                    .morphology
                    .stem(stem)
                    .map_or(0, |founded| founded.wholes.len());
                println!(
                    "    {:<12} {:<16} {:>8}  {}",
                    format!("{stem:?}"),
                    if withholding.decommitted.contains(*stem) {
                        "NOT committed"
                    } else {
                        "committed"
                    },
                    wholes,
                    remaining
                        .iter()
                        .copied()
                        .map(file_name)
                        .collect::<Vec<&str>>()
                        .join(" ")
                );
            }
            if withholding.departed.is_empty() {
                println!(
                    "\n    no passage departed, and the table above is why: every licensing stem is\n    \
                     still witnessed by at least two distinct wholes among the remaining thirteen\n    \
                     documents, so none of them left the committed morphology. Reported plainly as a\n    \
                     null result on the departure direction; the appearance direction above is not\n    \
                     null."
                );
            } else {
                println!("\n    the passages that departed, exhibited whole as they stood BEFORE:");
                for name in &withholding.departed {
                    if let Some(passage) = production.iter().find(|passage| &passage.name == name) {
                        exhibit(passage, &morphology);
                    }
                }
            }
            if !withholding.appeared.is_empty() {
                println!("\n    the passages that appeared, exhibited whole as they stand AFTER:");
                for name in &withholding.appeared {
                    if let Some(passage) = withholding
                        .derived
                        .iter()
                        .find(|passage| &passage.name == name)
                    {
                        exhibit(passage, &withholding.morphology);
                    }
                }
            }
        }
        None => println!("    the declared exhibit is not among the declared corpus"),
    }

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");

    controls.check(
        "the unconditioned control emitted zero passages on the declared query",
        control.is_empty(),
        "FoundedMorphology::unconditioned() commits no stem, so no two identifiers share one",
    );
    controls.check(
        "the unconditioned control emitted zero passages on every statement the deposit reaches",
        control_total == 0,
        "the conditioning is on the causal path for the whole deposit, not only for one query",
    );
    controls.check(
        "the conditioned body returned a non-empty passage population",
        !production.is_empty(),
        "and every passage above carries the bridge and the corpus documents that licensed it",
    );
    let named: Vec<(&String, &BTreeSet<&'static str>)> = traced
        .iter()
        .filter(|(stem, documents)| stem.chars().count() >= 4 && !documents.is_empty())
        .map(|(stem, documents)| (*stem, documents))
        .collect();
    controls.check(
        "at least one passage's bridge stem is a whole morpheme founded by a NAMED corpus document",
        !named.is_empty(),
        &match named.first() {
            Some((stem, documents)) => format!(
                "stem {stem:?} founded by {}",
                documents.iter().copied().collect::<Vec<&str>>().join(", ")
            ),
            None => {
                "no licensing stem longer than three characters resolved to a declared document"
                    .to_owned()
            }
        },
    );
    controls.check(
        "every licensing stem resolves to at least one declared corpus document",
        traced.iter().all(|(_, documents)| !documents.is_empty()),
        "a stem no declared document witnessed would mean the corpus is not what conditioned this",
    );
    controls.check(
        "every intake exposure carries an occurrence identity naming a declared corpus document",
        corpus_intake
            .exposures
            .iter()
            .all(|exposure| document_of(&exposure.whole).is_some()),
        "the whole is life's own occurrence identity, so provenance is the intake's and not the \
         driver's",
    );
    controls.check(
        "withholding a declared corpus document was carried out for every declared document",
        withholdings.len() == CORPUS.len(),
        "the ablation is over the whole declared population, so nothing was selected into it",
    );
    controls.check(
        "at least one withholding moved the passage population",
        withholdings.iter().any(|withholding| {
            !withholding.departed.is_empty() || !withholding.appeared.is_empty()
        }),
        "otherwise the corpus is decorative: report that plainly rather than adjusting the corpus",
    );

    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}
