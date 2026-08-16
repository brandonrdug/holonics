//! EROS LABORATORY INTERLOCUTOR — repository-scale recurrent research deliberation.
//!
//! Recovered from the frozen laboratory at
//! `ba8716b5:src/soma/life/examples/eros_laboratory_interlocutor.rs` (124 lines). Deleted at
//! `a07ff376`; never imported by `06518c3` ("Transition to Rust").
//!
//! ## THE DIVERGENCE THAT REWROTE THIS DRIVER
//!
//! The laboratory driver was four calls:
//!
//! ```text
//!   let atlas    = LaboratorySourceAtlas::mount_repository_excluding(&root, &grading)?;
//!   let mut eco  = LaboratoryResearchEcology::new(LaboratoryResearchSpec { leader_aperture: 16 });
//!   let first    = eco.ask(&atlas, "How does agentic language ecology carry relational parse fiber?")?;
//!   println!("eros> {}", first.text);
//! ```
//!
//! **Neither `ask` nor `LaboratoryResearchAnswer` exists in this body.** `LaboratoryResearchAnswer`
//! occurs nowhere under `soma/life/src/` — it is not renamed, it is gone — and
//! `LaboratoryResearchEcology` no longer forms answer *text* at all. Its outward method is
//! `deliberate_until_return_with_world_front`, returning a `LaboratoryResearchDeliberation`:
//! leaders, world returns, thought steps, a relational thought fiber, and the conditioned-passage
//! and relational-clause counts before and after.
//!
//! **The answer-forming half moved to `agentic_language` / `agentic_research`.** The laboratory's
//! one organ split into a deliberation organ (here) and a language organ (there), and
//! `AgenticResearchSession` is what re-joins them — which is why
//! `eros_agentic_research_conversation` is the driver that emits text and this one is not.
//!
//! So this is a **port of the deliberation**, not of `ask`. It emits no `eros>` line, because the
//! organ it drives emits none. What it returns is the world's own returned sections — real bytes
//! of real files, selected by a leader the question caused — plus the standing the deliberation
//! changed. Claiming an answer here would be authoring one.
//!
//! ## Two apertures, both declared
//!
//! - **The world.** `mount_repository_excluding` walks `src/soma/RESEARCH`, `src/soma/PAPERS`,
//!   `src/soma` and `crates`, which is the laboratory's layout, not this repository's. A symlink
//!   fixture maps live material into it. `--world repository` mounts everything (796 files,
//!   74,117 sections); the default `--world declared` mounts a named handful, because —
//! - **The leader aperture.** MEASURED 2026-08-09 against the whole-repository mount: **every
//!   finite aperture refuses**, at exactly `aperture + 1` (16 → 17, 512 → 513), and
//!   `complete_local_star()` does not close inside 40 minutes. `LaboratoryResearchSpec` refuses
//!   rather than truncating, which is correct; it also means a world this size has no admissible
//!   aperture on this law.
//!
//! ## AND THE DELIBERATION REQUIRES TWO INFORMANT PORTS, HARDCODED
//!
//! MEASURED 2026-08-09. The laboratory driver handed `ask` a repository atlas and nothing else.
//! The live organ cannot be driven that way: `open_world_contact_front`
//! (`laboratory_language.rs:1300`) emits, **for every leader**, one request on
//! `RepositorySource` and one on `ResidentTextCard` — the port list is a literal array in the
//! function, not a spec field — and `join_wave_returns` then looks for a return on **both**. A
//! repository-only world answers the first and obstructs the second, and the front stays open:
//!
//! ```text
//!   World("repository-search-0/world-front/0 remains open: repository atlas cannot enact ResidentTextCard")
//! ```
//!
//! So this driver mounts the same two-port world the agentic conversation does — repository atlas
//! plus a CUDA-resident exact text atlas, composed by `MountedResearchInformantWorld`. **A
//! repository-only interlocutor is not a thing this body can express**, and that is a structural
//! fact about the port, not a limitation of the port's author.
//!
//! Run:
//! ```text
//!   cargo run -p life --example eros_laboratory_interlocutor
//! ```

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::{
    agentic_research::MountedResearchInformantWorld,
    laboratory_language::{
        LaboratoryResearchDeliberation, LaboratoryResearchEcology, LaboratoryResearchSpec,
        LaboratorySourceAtlas,
    },
    text_material::{ExactTextMaterialAtlas, ExactTextMaterialCorpus, ParsedTextDocument},
};

/// The laboratory's own two questions, unchanged.
const FIRST_QUESTION: &str = "How does agentic language ecology carry relational parse fiber?";
const SECOND_QUESTION: &str =
    "What carries a continuity obstruction for relational morphology, and what cultivates contemporary morphology?";

/// The laboratory excluded its own grading record so a rerun could not inherit its transcript.
/// Same exclusion, same purpose, this repository's path shape.
const GRADING_RECORD: &str =
    "src/soma/RESEARCH/2026-07-31_THE_OPEN_LEADERS_RETURN_TO_ONE_BODY_THE_REPOSITORY_EMITS_ITS_OWN_DIAGNOSIS.md";

/// `--world declared` — the named world. Theory that speaks about parse fiber and morphology, and
/// the live Rust owners of the organs the questions name.
const DECLARED_THEORY: &[&str] = &[
    "research/records/2026-07-31_THE_OPERATOR_ENTERS_THE_CONTINUING_BODY_THE_TRACE_SEPARATES_THE_SURFACE_FROM_ITS_LINEAGE.md",
    "research/records/2026-07-31_THE_DIALOGUE_RETURNS_AS_VERSION_THE_ANSWER_RESTS_ONLY_AFTER_ITS_LOCAL_REGIONS_RETURN.md",
    "research/records/2026-07-31_THE_RETURN_RECURS_AS_THE_CODEC_THE_UNSEEN_FACE_DEPARTS_THE_DEVELOPMENTAL_SOURCE.md",
    "research/records/2026-08-01_THE_AGENT_EMITS_THE_DEED_THE_LOCAL_CLOSURE_SPEAKS_BESIDE_THE_OPEN_FIBER.md",
];

const DECLARED_RUST: &[&str] = &[
    "soma/life/src/relational_language/types.rs",
    "soma/life/src/relational_language/transport.rs",
    "soma/life/src/agentic_research/open_completion.rs",
];

/// `--world repository` — the whole tree, in the layout the organ walks.
const REPOSITORY_DIRECTORIES: &[(&str, &str)] = &[
    ("research/records", "src/soma/RESEARCH"),
    ("canon", "src/soma/PAPERS/canon"),
    ("soma", "src/soma/live"),
    ("crates", "crates"),
];

fn main() {
    if let Err(error) = run() {
        eprintln!("eros laboratory interlocutor: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut whole_repository = false;
    let mut leader_horizon = 0u64;
    let mut fixture = std::env::temp_dir().join("holonics-laboratory-interlocutor-fixture");
    let mut input = std::env::args().skip(1);
    while let Some(argument) = input.next() {
        match argument.as_str() {
            "--world" => match input.next().as_deref() {
                Some("declared") => whole_repository = false,
                Some("repository") => whole_repository = true,
                other => return Err(format!("--world takes declared|repository, not {other:?}")),
            },
            "--leader-aperture" => {
                leader_horizon = input
                    .next()
                    .ok_or("--leader-aperture needs a value")?
                    .parse()
                    .map_err(|e| format!("{e}"))?
            }
            "--fixture" => fixture = input.next().ok_or("--fixture needs a value")?.into(),
            other => return Err(format!("unknown argument {other:?}")),
        }
    }

    let root = repository_root();
    let started = Instant::now();
    let mapped = if whole_repository {
        repository_fixture(&root, &fixture)?
    } else {
        declared_fixture(&root, &fixture)?
    };
    let atlas = LaboratorySourceAtlas::mount_repository_excluding(
        &fixture,
        &BTreeSet::from([GRADING_RECORD.to_owned()]),
    )
    .map_err(|error| format!("mount laboratory atlas: {error:?}"))?;
    let mount_millis = started.elapsed().as_millis();

    println!("STATION 1 — THE MOUNTED WORLD");
    println!(
        "  world                {}",
        if whole_repository {
            "repository"
        } else {
            "declared (DEFAULT)"
        }
    );
    for (live, at) in &mapped {
        println!("    {at}  <-  {live}");
    }
    println!("  source_files         {}", atlas.receipt().source_files);
    println!("  theory_sections      {}", atlas.receipt().theory_sections);
    println!(
        "  rust_source_sections {}",
        atlas.receipt().rust_source_sections
    );
    println!(
        "  indexed_features     {}",
        atlas.receipt().indexed_features
    );
    println!("  mount                {mount_millis} ms");
    println!("  excluded             {GRADING_RECORD}");

    let mut spec = if leader_horizon == 0 {
        LaboratoryResearchSpec::default()
    } else {
        LaboratoryResearchSpec::at_horizon(leader_horizon)
    };
    spec.worker_threads = 2;
    let mut ecology = LaboratoryResearchEcology::new(spec);

    // The second informant port. Its material is the same declared theory, conditioned through
    // `ExactTextMaterialCorpus::import`; every section is a paragraph of a tracked file.
    let documents = DECLARED_THEORY
        .iter()
        .enumerate()
        .map(|(at, named)| {
            let text = fs::read_to_string(root.join(named))
                .map_err(|e| format!("read declared theory {named}: {e}"))?;
            Ok(ParsedTextDocument {
                identity: format!("interlocutor-theory-{at}"),
                source: (*named).to_owned(),
                sections: text
                    .split("\n\n")
                    .map(|p| p.split_whitespace().collect::<Vec<_>>().join(" "))
                    .filter(|p| !p.is_empty())
                    .collect(),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let corpus = ExactTextMaterialCorpus::import(Vec::new(), &documents, 2)
        .map_err(|e| format!("import declared text corpus: {e:?}"))?;
    let text = ExactTextMaterialAtlas::condition(corpus)
        .map_err(|e| format!("condition text ecology: {e:?}"))?;
    let text_sections = text.receipt().conditioned_sections;
    let resident = text
        .mount_cuda(0)
        .map_err(|refusal| format!("mount resident CUDA text: {:?}", refusal.error()))?;
    let device = resident.device_name().to_owned();
    let mut world = MountedResearchInformantWorld::new(atlas, resident, 2)
        .map_err(|e| format!("compose two-port informant world: {e:?}"))?;
    println!("\n  second informant     resident text card on {device}, {text_sections} sections");

    for (label, deed, question) in [
        ("FIRST", "repository-search-0", FIRST_QUESTION),
        ("SECOND", "repository-search-1", SECOND_QUESTION),
    ] {
        println!("\nSTATION 2 — {label} QUESTION");
        println!("  you> {question}");
        let started = Instant::now();
        match ecology.deliberate_until_return_with_world_front(deed, question, |requests| {
            world.enact_contact_front(requests)
        }) {
            Ok(deliberation) => {
                print_deliberation(&deliberation, started.elapsed().as_millis());
            }
            Err(error) => {
                println!("  OBSTRUCTED  {error:?}");
                println!(
                    "  (a `ReceiverAperture` obstruction is the organ refusing an authored count \
rather than truncating a return; it is a lawful refusal, not a failure)"
                );
                return Ok(());
            }
        }
    }

    println!("\nSTATION 3 — THE CONTINUING BODY");
    println!("  conditioned_passages {}", ecology.conditioned_passages());
    println!("  relational_clauses   {}", ecology.relational_clauses());
    Ok(())
}

/// The ARTIFACT of a deliberation is the world's returned sections. Print them before any count.
fn print_deliberation(deliberation: &LaboratoryResearchDeliberation, millis: u128) {
    println!("\n  ── THE ARTIFACT — WHAT THE WORLD RETURNED ──");
    let mut shown = 0usize;
    for returned in &deliberation.returns {
        for section in returned.sections.iter().take(3) {
            let text = section.text.replace('\n', " ");
            let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
            println!("  [{}:{}] {text}", section.source, section.line);
            if !section.matched_features.is_empty() {
                let features = section
                    .matched_features
                    .iter()
                    .take(6)
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ");
                println!("      matched: {features}");
            }
            shown += 1;
            if shown >= 12 {
                break;
            }
        }
        if shown >= 12 {
            break;
        }
    }
    if shown == 0 {
        println!("  (the world returned no section — the leader's caused region met nothing)");
    }

    println!("\n  motion");
    println!("    deed               {}", deliberation.deed);
    println!("    question identity  {}", deliberation.question_identity);
    println!("    leaders            {}", deliberation.leaders.len());
    for leader in deliberation.leaders.iter().take(6) {
        println!(
            "      {} generation {} horizon {} region {:?}",
            leader.identity, leader.generation, leader.horizon, leader.region
        );
    }
    println!("    world returns      {}", deliberation.returns.len());
    let complete: usize = deliberation
        .returns
        .iter()
        .map(|r| r.complete_population)
        .sum();
    let omitted: usize = deliberation
        .returns
        .iter()
        .map(|r| r.omitted_population)
        .sum();
    println!("    complete / omitted {complete} / {omitted}");
    println!(
        "    thought steps      {}",
        deliberation.thought_steps.len()
    );
    for step in deliberation.thought_steps.iter().take(4) {
        println!(
            "      wave {} generation {} sections {} newly_conditioned {} clauses {} -> {}",
            step.arrival_chronology,
            step.generation,
            step.returned_sections,
            step.newly_conditioned_passages,
            step.relational_clauses_before,
            step.relational_clauses_after
        );
    }
    println!(
        "    conditioned        {} -> {}",
        deliberation.conditioned_passages_before, deliberation.conditioned_passages_after
    );
    println!(
        "    relational clauses {} -> {}",
        deliberation.relational_clauses_before, deliberation.relational_clauses_after
    );
    println!(
        "    thought fiber      {}",
        if deliberation.fiber.is_some() {
            "present"
        } else {
            "none"
        }
    );
    println!("    elapsed            {millis} ms");
}

fn declared_fixture(root: &Path, fixture: &Path) -> Result<Vec<(String, String)>, String> {
    let _ = fs::remove_dir_all(fixture);
    let mut mapped = Vec::new();
    for (named, at) in DECLARED_THEORY
        .iter()
        .map(|n| (*n, "src/soma/RESEARCH"))
        .chain(DECLARED_RUST.iter().map(|n| (*n, "src/soma/live")))
    {
        let from = root.join(named);
        if !from.is_file() {
            return Err(format!("declared world file is absent: {named}"));
        }
        let directory = fixture.join(at);
        fs::create_dir_all(&directory)
            .map_err(|e| format!("create {}: {e}", directory.display()))?;
        let leaf = Path::new(named).file_name().expect("a file name");
        let into = directory.join(leaf);
        std::os::unix::fs::symlink(&from, &into)
            .map_err(|e| format!("link {}: {e}", into.display()))?;
        mapped.push((named.to_owned(), format!("{at}/{}", leaf.to_string_lossy())));
    }
    Ok(mapped)
}

fn repository_fixture(root: &Path, fixture: &Path) -> Result<Vec<(String, String)>, String> {
    let _ = fs::remove_dir_all(fixture);
    let mut mapped = Vec::new();
    for (live, at) in REPOSITORY_DIRECTORIES {
        let from = root.join(live);
        if !from.is_dir() {
            continue;
        }
        let into = fixture.join(at);
        if let Some(parent) = into.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("create {}: {e}", parent.display()))?;
        }
        std::os::unix::fs::symlink(&from, &into)
            .map_err(|e| format!("link {}: {e}", into.display()))?;
        mapped.push(((*live).to_owned(), (*at).to_owned()));
    }
    Ok(mapped)
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root resolves")
}
