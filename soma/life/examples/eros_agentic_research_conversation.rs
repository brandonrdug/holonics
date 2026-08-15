//! EROS AGENTIC RESEARCH CONVERSATION — the agentic loop, end to end, on real material.
//!
//! Recovered from the frozen laboratory at `ba8716b5:src/soma/life/examples/eros_agentic_research_conversation.rs`
//! (1,327 lines). The file does **not** exist at `a07ff376`: that commit deleted it along with
//! `eros_causal_language_generation`, `eros_symbolic_language_agent` and four siblings, and
//! `06518c3` ("Transition to Rust") imported the library without any of the drivers. The organs it
//! calls — `agentic_language` (6,473 lines), `agentic_research` (1,525), `laboratory_language`,
//! `relational_language` (4,801), `morphological_language` — had **no caller** in this tree.
//!
//! ## What this driver conducts
//!
//! ```text
//!   question  ->  typed deed  ->  world contact front  ->  world return
//!             ->  answer      ->  feedback (correction) ->  codec cultivation
//!             ->  second question, which may conduct through the cultivated codec
//! ```
//!
//! Every input is a byte of a file tracked in this repository. No measurement is authored, no
//! model is executed, no answer text is supplied by this driver.
//!
//! ## Four API divergences from the laboratory source, each named
//!
//! 1. **`AgenticResearchSession::converse_with_world` → `converse_with_world_front`.** The
//!    laboratory closure received one `&LaboratoryResearchLeader` and returned one
//!    `LaboratoryWorldReturn`. The live closure receives `&[LaboratoryWorldContactRequest]` and
//!    returns a `LaboratoryWorldContactAttempt` — a *front*, not a single leader.
//! 2. **The join is now a library organ.** The laboratory driver hand-rolled `joined_return()` to
//!    glue the card return to the repository return. `MountedResearchInformantWorld` owns that
//!    composition and its apparatus testimony; the hand-rolled join is deleted, not ported.
//! 3. **`LaboratorySourceAtlas::enact(leader) -> (history, receipt)` → `enact_contact_front`.**
//!    The per-leader restriction receipt (`TextMaterialCudaRestrictionReceipt`) was replaced by
//!    `TextMaterialCudaContactReceipt`, carried on the world rather than returned to the caller.
//!    The laboratory's ~600 lines of restriction telemetry have no live fields to fill and are
//!    **not reconstructed**; what the live receipts carry is what is printed.
//! 4. **The atlas mounts a laboratory layout.** `mount_repository_excluding` walks
//!    `src/soma/RESEARCH`, `src/soma/PAPERS`, `src/soma`, `crates`. This repository is
//!    `research/records`, `papers/source`, `soma`, `crates`. A symlink fixture maps live material
//!    into the layout the organ declares; nothing is copied and nothing is edited under `src/`.
//!
//! ## The input the laboratory had and this repository does not
//!
//! The laboratory read `runs/symbolic-language-agent/TEXT_REST.json`, written by
//! `eros_symbolic_language_agent`. `runs/` was never tracked — zero files exist under it at any
//! laboratory commit — and that driver's owner, `life::symbolic_reasoning`, was deleted at
//! `a07ff376`. So the rest is unrecoverable and its producer is gone. Instead the text body is
//! conditioned here from **declared live research records** through the same
//! `ExactTextMaterialCorpus::import` → `ExactTextMaterialAtlas::condition` path, and `--text-rest`
//! still accepts a native rest when one exists. This is a declared substitution, not a recovery.
//!
//! Run:
//! ```text
//!   cargo run -p life --example eros_agentic_research_conversation --release
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use holonic_structure::CausalMembrane;
use life::{
    agentic_language::{
        AgenticLanguageCapability, AgenticLanguageEcology, AgenticLanguageFeedback,
        AgenticLanguageFeedbackKind, AgenticLanguageOccurrence, AgenticLanguageSpec,
    },
    agentic_research::{
        answer_causes, AgenticResearchAnswer, AgenticResearchSession, MountedResearchInformantWorld,
    },
    laboratory_language::{LaboratoryResearchSpec, LaboratorySourceAtlas, LaboratorySourceRoots},
    morphological_language::{MorphologicalGenerationSpec, MorphologicalLanguagePassage},
    text_material::{ExactTextMaterialAtlas, ExactTextMaterialCorpus, ParsedTextDocument},
};
use soma_abi::active::ActionCurrent;

/// The exterior organ the language body must emit a deed against before it may answer.
const RESEARCH_CAPABILITY: &str = "conditioned-laboratory-history";

/// The laboratory's own default question, unchanged.
const DEFAULT_QUESTION: &str = "What carries a continuity obstruction for relational morphology?";

/// A second question, asked after a correction, so the cultivated codec has something to conduct
/// through. Nothing here asserts the second answer must differ; the run reports whether it did.
const SECOND_QUESTION: &str = "What cultivates contemporary relational morphology?";

/// APERTURE — declared, and small on purpose. This is the **only** aperture this driver applies to
/// generation, and it is a bound on OBSERVATION DEPTH: `morphological_language/ecology.rs:839` rests
/// a branch with `ObservationApertureExhausted` once its `returned_event_count` reaches this value.
/// `MorphologicalGenerationSpec` (`soma/life/src/morphological_language.rs:173-176`) has exactly one
/// field and this is it.
///
/// Cost, measured at `a91a84f` on a 23-passage corpus, release build: 1 token 57 ms · 2 tokens
/// 403 ms · 4 tokens 55,098 ms · 8 tokens no return in 200,000 ms. The laboratory declared 128 here
/// and that does not return on this implementation. A receiver parameter, not a law, and it is
/// printed in the receipt.
///
/// **NOTHING BOUNDS THE NUMBER OF RETURNED BRANCHES.** Until 2026-08-10 this driver also carried a
/// `MORPHOLOGICAL_OUTPUT_APERTURE = 3`, stored it, parsed `--output-aperture` into it, and printed
/// it as `output aperture 3 (DECLARED)`. It was passed to nothing: there is no field to receive it,
/// so the receipt advertised a bound of three while the organ returned every branch it produced —
/// `research/records/2026-08-10_THE_MACHINE_RETURNS_EVERY_BRANCH_BECAUSE_NOTHING_ATTACHES.md`
/// measures 14,018 response branches for one obligation at two tokens. The constant, the field and
/// the flag are removed rather than annotated; bounding generation is a separate question and this
/// driver does not decide it.
const MORPHOLOGICAL_OBSERVATION_APERTURE: usize = 24;

/// APERTURE — how many sections one leader may encounter before `LaboratoryResearchSpec` refuses.
///
/// MEASURED 2026-08-09 against this repository's own 793-file source atlas: **every finite value
/// refuses**, and refuses at exactly `aperture + 1` — 16 gave `encountered_population: 17`, 512
/// gave `513`. The leader's caused region reaches more of a repository this size than any authored
/// count admits, so a finite aperture here is not a bound, it is a guaranteed refusal.
///
/// `LaboratoryResearchSpec::complete_local_star()` is the library's own answer and its doc comment
/// says why: *"This removes an authored answer/recruitment count. It does not mean an absolute
/// corpus scan: each world still restricts through the leader's caused receiver region before this
/// outer boundary is applied."* That is the default here. `--leader-aperture N` still forces a
/// finite one, so the refusal above can be reproduced.
const DEFAULT_LEADER_APERTURE: usize = 0;

/// The inherited language body. Six records, named by the laboratory driver verbatim, each of
/// which is present in this repository under `research/records/` with the same basename.
const INHERITED_LANGUAGE_RECORDS: &[&str] = &[
    "research/records/2026-07-31_THE_RETURN_RECURS_AS_THE_CODEC_THE_UNSEEN_FACE_DEPARTS_THE_DEVELOPMENTAL_SOURCE.md",
    "research/records/2026-07-31_THE_MATERIAL_DEPARTS_THE_RETURNED_PATH_REMAINS_THE_BODY_ASKS_WHAT_ITS_DIFFERENCES_CAN_DO.md",
    "research/records/2026-07-31_THE_PREFIX_GROWS_THE_DEED_RETAINS_ITS_WITNESSES_THE_LEXICAL_STAR_REMAINS_TOO_BROAD.md",
    "research/records/2026-07-31_THE_DIALOGUE_CONDITIONS_THE_DEED_THE_EXACT_RETURN_CAUSES_FURTHER_THOUGHT.md",
    "research/records/2026-07-31_THE_OPERATOR_ENTERS_THE_CONTINUING_BODY_THE_TRACE_SEPARATES_THE_SURFACE_FROM_ITS_LINEAGE.md",
    "research/records/2026-07-31_THE_DIALOGUE_RETURNS_AS_VERSION_THE_ANSWER_RESTS_ONLY_AFTER_ITS_LOCAL_REGIONS_RETURN.md",
];

/// The grading record is excluded from the world so this driver's own transcript cannot become
/// inherited testimony on a later run. Laboratory lineage: the same exclusion, same purpose.
const GRADING_RECORD: &str =
    "src/soma/RESEARCH/2026-08-01_THE_AGENT_EMITS_THE_DEED_THE_LOCAL_CLOSURE_SPEAKS_BESIDE_THE_OPEN_FIBER.md";

/// `--world repository` — the whole tree mapped into the layout the organ walks.
///
/// MEASURED 2026-08-09: this mounts **796 source files, 47,440 theory sections, 26,677 Rust
/// sections, 53,195 indexed features**, and one question at `complete_local_star` does not close
/// inside 40 minutes. It is kept because it is the laboratory's own framing and because the mount
/// figures are themselves evidence, but it is not the default.
const FIXTURE_REPOSITORY_DIRECTORIES: &[(&str, &str)] = &[
    ("research/records", "src/soma/RESEARCH"),
    ("canon", "src/soma/PAPERS/canon"),
    ("soma", "src/soma/live"),
    ("crates", "crates"),
];

/// `--world declared` — THE DEFAULT, and the aperture is on the MATERIAL, stated here.
///
/// The world is the six inherited research records plus the five live owners of the organs the
/// loop conducts through. This is a declared receiver family, not a sample: every file is named,
/// and the question below is one the material can actually answer. The laboratory's own world was
/// of this order; the whole-repository mount is a later framing that its leader law cannot close.
const DECLARED_WORLD_THEORY: &[&str] = &[
    "research/records/2026-07-31_THE_RETURN_RECURS_AS_THE_CODEC_THE_UNSEEN_FACE_DEPARTS_THE_DEVELOPMENTAL_SOURCE.md",
    "research/records/2026-07-31_THE_MATERIAL_DEPARTS_THE_RETURNED_PATH_REMAINS_THE_BODY_ASKS_WHAT_ITS_DIFFERENCES_CAN_DO.md",
    "research/records/2026-07-31_THE_PREFIX_GROWS_THE_DEED_RETAINS_ITS_WITNESSES_THE_LEXICAL_STAR_REMAINS_TOO_BROAD.md",
    "research/records/2026-07-31_THE_DIALOGUE_CONDITIONS_THE_DEED_THE_EXACT_RETURN_CAUSES_FURTHER_THOUGHT.md",
    "research/records/2026-07-31_THE_OPERATOR_ENTERS_THE_CONTINUING_BODY_THE_TRACE_SEPARATES_THE_SURFACE_FROM_ITS_LINEAGE.md",
    "research/records/2026-07-31_THE_DIALOGUE_RETURNS_AS_VERSION_THE_ANSWER_RESTS_ONLY_AFTER_ITS_LOCAL_REGIONS_RETURN.md",
];

/// Added 2026-08-09 after a MEASURED refusal, and the refusal is worth carrying.
///
/// With only the six inherited records the first question returned `NoClosedCurrent` — *"the typed
/// research deed rested without a locally closed current; no answer was projected"*. The reason is
/// not a defect: the one document that carries the question verbatim is
/// `2026-08-01_THE_AGENT_EMITS_THE_DEED_...`, which is this driver's **grading record** and is
/// therefore excluded from the world by design, exactly as the laboratory excluded its own. A
/// question can only close on material that is not the transcript of it being asked.
///
/// These five carry `continuity`, `obstruction`, `relational`, `morphology` and `contemporary` in
/// their own prose, none is a grading record, and each was found by grepping the live tree for the
/// question's own regions rather than chosen for its result.
const DECLARED_WORLD_SUPPORT: &[&str] = &[
    "research/records/2026-07-31_THE_OPEN_LEADERS_RETURN_TO_ONE_BODY_THE_REPOSITORY_EMITS_ITS_OWN_DIAGNOSIS.md",
    "research/records/2026-07-31_THE_CHARACTERISTIC_CARRIES_THE_CURRENT_THE_EXPONENTIAL_RETURNS_AS_RECEIVER_PHASE.md",
    "research/records/2026-07-31_THE_RETURN_CHANGES_THE_CONTINUATION_FIBER_THE_INTERMEDIATE_BODY_IS_THE_LOCAL_INFORMATION_LAW.md",
    "research/records/2026-07-31_THE_REFERENCE_OPENS_AN_APERTURE_THE_RETURN_CONDITIONS_THE_CONTINUING_BODY.md",
    "research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md",
];

const DECLARED_WORLD_RUST: &[&str] = &[
    "soma/life/src/relational_language/types.rs",
    "soma/life/src/relational_language/transport.rs",
    "soma/life/src/agentic_research/open_completion.rs",
    "soma/life/src/dialogue_lineage.rs",
    "soma/life/src/research_intelligence.rs",
];

struct Arguments {
    text_rest: Option<PathBuf>,
    fixture: Option<PathBuf>,
    whole_repository: bool,
    /// How many of `DECLARED_WORLD_SUPPORT` enter the world. A DECLARED APERTURE ON THE MATERIAL:
    /// deliberation cost grows steeply in world size (7 files 14 s; 16 files did not close in 40
    /// minutes), so the smallest world that still closes the question is the honest default.
    support_records: usize,
    question: Option<String>,
    leader_aperture: usize,
    threads: usize,
    observation_aperture: usize,
    thought_receiver_horizon: u64,
}

impl Default for Arguments {
    fn default() -> Self {
        Self {
            text_rest: None,
            fixture: None,
            whole_repository: false,
            support_records: 5,
            question: None,
            leader_aperture: DEFAULT_LEADER_APERTURE,
            threads: 2,
            observation_aperture: MORPHOLOGICAL_OBSERVATION_APERTURE,
            thought_receiver_horizon: 90,
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros agentic research conversation: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = arguments()?;
    let root = repository_root();

    // ── STATION 1 — the inherited language body ─────────────────────────────────────────────
    let inherited = inherited_language_body(&root)?;
    println!("STATION 1 — THE INHERITED LANGUAGE BODY");
    println!(
        "  records              {}",
        INHERITED_LANGUAGE_RECORDS.len()
    );
    println!(
        "  passages             {} ({} octets)",
        inherited.len(),
        inherited.iter().map(|p| p.text.len()).sum::<usize>()
    );
    for record in INHERITED_LANGUAGE_RECORDS {
        println!("    {record}");
    }

    // ── STATION 2 — the exact text world ────────────────────────────────────────────────────
    let mount_started = Instant::now();
    let (atlas, text_provenance) = match arguments.text_rest.as_ref() {
        Some(path) => {
            let bytes = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
            let atlas = ExactTextMaterialAtlas::from_native_bytes(&bytes)
                .map_err(|e| format!("remount text rest {}: {e:?}", path.display()))?;
            (atlas, format!("native rest {}", path.display()))
        }
        None => {
            let documents = declared_text_documents(&root)?;
            let corpus = ExactTextMaterialCorpus::import(Vec::new(), &documents, arguments.threads)
                .map_err(|e| format!("import declared text corpus: {e:?}"))?;
            let atlas = ExactTextMaterialAtlas::condition(corpus)
                .map_err(|e| format!("condition text ecology: {e:?}"))?;
            (
                atlas,
                format!("{} declared live records", INHERITED_LANGUAGE_RECORDS.len()),
            )
        }
    };
    let mount_millis = mount_started.elapsed().as_millis();
    let occurrences_before = atlas.corpus().occurrences().len();
    println!("\nSTATION 2 — THE EXACT TEXT WORLD");
    println!("  source               {text_provenance}");
    println!("  occurrences          {occurrences_before}");
    println!(
        "  conditioned          {} occurrences / {} sections",
        atlas.receipt().conditioned_occurrences,
        atlas.receipt().conditioned_sections
    );
    println!("  mount                {mount_millis} ms");

    // ── STATION 3 — the repository world, through a declared layout fixture ─────────────────
    let fixture = arguments
        .fixture
        .clone()
        .unwrap_or_else(|| std::env::temp_dir().join("holonics-agentic-research-fixture"));
    let fixture_map = if arguments.whole_repository {
        build_repository_fixture(&root, &fixture)?
    } else {
        build_declared_fixture(&root, &fixture, arguments.support_records)?
    };
    // **The world declares the roots it built.** The default roots are this repository's own
    // (`research/records`, `papers`, `crates`, `soma`); the fixture is a declared subset and carries
    // two of them. Mounting the fixture at the defaults asked for `papers` and `crates`, found
    // neither, and — before `DeclaredRootIsAbsent` existed — indexed **zero** sections in silence,
    // so the first question failed with `NoClosedCurrent`: a diagnosis about the question for a
    // defect in the mount.
    let repository = LaboratorySourceAtlas::mount_repository_roots(
        &fixture,
        &LaboratorySourceRoots {
            theory: vec![PathBuf::from("research/records")],
            code: vec![PathBuf::from("soma")],
        },
        &BTreeSet::from([GRADING_RECORD.to_owned()]),
    )
    .map_err(|e| format!("mount repository research world: {e:?}"))?;
    println!("\nSTATION 3 — THE REPOSITORY WORLD");
    println!(
        "  world                {}",
        if arguments.whole_repository {
            "repository — every tracked record, canon document, soma and crates source"
        } else {
            "declared — 6 research records + 5 live organ owners, each named below (DEFAULT)"
        }
    );
    println!("  fixture root         {}", fixture.display());
    for (live, mapped) in &fixture_map {
        println!("    {mapped:<28} -> {live}");
    }
    println!(
        "  source_files         {}",
        repository.receipt().source_files
    );
    println!(
        "  theory_sections      {}",
        repository.receipt().theory_sections
    );
    println!(
        "  rust_source_sections {}",
        repository.receipt().rust_source_sections
    );
    println!(
        "  indexed_features     {}",
        repository.receipt().indexed_features
    );
    println!("  excluded             {GRADING_RECORD}");

    // ── STATION 4 — the conditioned agentic body ────────────────────────────────────────────
    let action = ActionCurrent::new(Cog::lit(1))
        .ok_or_else(|| "the agentic action current must be positive".to_owned())?;
    let conditioning_started = Instant::now();
    let agent = AgenticLanguageEcology::condition(
        &inherited,
        &[AgenticLanguageCapability::new(RESEARCH_CAPABILITY, 80).with_open_boundary()],
        &[],
        AgenticLanguageSpec {
            generation: MorphologicalGenerationSpec {
                maximum_observed_tokens: arguments.observation_aperture,
            },
            thought_receiver_horizon: arguments.thought_receiver_horizon,
        },
        action,
        arguments.threads,
    )
    .map_err(|e| format!("condition continuing agentic body: {e:?}"))?;
    let conditioning_millis = conditioning_started.elapsed().as_millis();
    println!("\nSTATION 4 — THE CONDITIONED AGENTIC BODY");
    println!(
        "  conditioning         {conditioning_millis} ms, {} workers",
        arguments.threads
    );
    println!(
        "  observation aperture {}   (DECLARED — the only bound applied to generation: a branch\n\
         \x20                        rests at this many returned events. Cost at `a91a84f`:\n\
         \x20                        1 token 57 ms · 2 · 403 ms · 4 · 55,098 ms · 8 · no return.)",
        arguments.observation_aperture
    );
    println!(
        "  returned branches    UNBOUNDED — no output aperture is applied anywhere on this path.\n\
         \x20                    `MorphologicalGenerationSpec` carries `maximum_observed_tokens`\n\
         \x20                    and nothing else, so every branch the ecology produces is returned."
    );
    println!(
        "  relational clauses   {}",
        agent.relational_body().clauses().len()
    );
    println!(
        "  parse fibers         {}",
        agent.relational_body().parse_fibers().len()
    );
    println!("  capability           {RESEARCH_CAPABILITY} (open boundary)");
    println!(
        "  leader aperture      {}",
        if arguments.leader_aperture == 0 {
            "complete_local_star (usize::MAX) — the library's own removal of the authored count"
                .to_owned()
        } else {
            format!("{} (forced finite)", arguments.leader_aperture)
        }
    );

    // ── STATION 5 — the resident card and the composed world ────────────────────────────────
    let cuda_started = Instant::now();
    let resident = atlas.mount_cuda(0).map_err(|refusal| {
        format!(
            "mount resident exact CUDA text ecology: {:?}",
            refusal.error()
        )
    })?;
    let cuda_millis = cuda_started.elapsed().as_millis();
    let device = resident.device_name().to_owned();
    let mut world = MountedResearchInformantWorld::new(repository, resident, arguments.threads)
        .map_err(|e| format!("compose typed informant world: {e:?}"))?;
    println!("\nSTATION 5 — THE COMPOSED INFORMANT WORLD");
    println!("  device               {device}");
    println!("  cuda mount           {cuda_millis} ms");
    println!("  ports                RepositorySource + ResidentTextCard, one contact front");

    let mut session =
        AgenticResearchSession::new(agent, RESEARCH_CAPABILITY, research_spec(&arguments));

    // ── STATION 6 — the first question, and the artifact ────────────────────────────────────
    let question = arguments
        .question
        .clone()
        .unwrap_or_else(|| DEFAULT_QUESTION.to_owned());
    println!("\nSTATION 6 — THE FIRST QUESTION");
    println!("  you> {question}");
    let started = Instant::now();
    let first = session
        .converse_with_world_front(90, &question, |requests| {
            world.enact_contact_front(requests)
        })
        .map_err(|e| format!("first agentic research passage: {e:?}"))?;
    let first_millis = started.elapsed().as_millis();
    print_answer("FIRST", &first, first_millis);

    // ── STATION 7 — the correction, and the codec it cultivates ─────────────────────────────
    println!("\nSTATION 7 — THE RETURNED CORRECTION");
    let correction_text = first.answer.text.clone();
    let correction = AgenticLanguageFeedback::new(
        "agentic-research-correction-0",
        90,
        first.answer.answer_episode_identity.clone(),
        AgenticLanguageFeedbackKind::Correction,
        correction_text.clone(),
    );
    println!(
        "  you> [correction on {}]",
        first.answer.answer_episode_identity
    );
    println!("       {correction_text}");
    let standing_before = session.agent().standing().reflective_codec_training_events;
    let feedback_receipt = match session
        .agent_mut()
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&correction))
    {
        Ok(life::agentic_language::AgenticLanguageConsequence::Feedback(receipt)) => Some(receipt),
        Ok(other) => {
            println!("  correction returned  {other:?}");
            None
        }
        Err(error) => {
            println!("  correction OBSTRUCTED {error:?}");
            None
        }
    };
    match feedback_receipt
        .as_ref()
        .and_then(|r| r.committed_codec_version.as_ref())
    {
        Some(version) => {
            println!("  committed codec      {}", version.identity);
            println!(
                "  cultivation          receiver_views={} active_transductions {} -> {}",
                version.cultivation.receiver_views,
                version.cultivation.active_transductions_before,
                version.cultivation.active_transductions_after
            );
        }
        None => println!("  committed codec      NONE — the correction changed no conduct"),
    }
    println!(
        "  training events      {} -> {}",
        standing_before,
        session.agent().standing().reflective_codec_training_events
    );

    // ── STATION 8 — the second question, after the correction ───────────────────────────────
    println!("\nSTATION 8 — THE SECOND QUESTION, AFTER THE CORRECTION");
    println!("  you> {SECOND_QUESTION}");
    let started = Instant::now();
    match session.converse_with_world_front(90, SECOND_QUESTION, |requests| {
        world.enact_contact_front(requests)
    }) {
        Ok(second) => {
            let millis = started.elapsed().as_millis();
            print_answer("SECOND", &second, millis);
            println!("\n  DIFFERENCE FROM THE FIRST ANSWER");
            println!(
                "    same text          {}",
                second.answer.text == first.answer.text
            );
            println!(
                "    operative codecs   first={:?} second={:?}",
                first.answer.operative_codec_versions, second.answer.operative_codec_versions
            );
        }
        Err(error) => println!("  second question OBSTRUCTED: {error:?}"),
    }

    // ── STATION 9 — the source-detached rest ────────────────────────────────────────────────
    println!("\nSTATION 9 — THE SOURCE-DETACHED REST");
    match session.into_native_rest() {
        Ok(rest) => match rest.remount() {
            Ok((_, receipt)) => {
                println!(
                    "  agent_native_rest_exact     {}",
                    receipt.agent_native_rest_exact
                );
                println!(
                    "  research_native_rest_exact  {}",
                    receipt.research_native_rest_exact
                );
                println!(
                    "  source_replay_performed     {}",
                    receipt.source_replay_performed
                );
                println!("  remount                     EXACT");
            }
            Err(refusal) => println!("  remount REFUSED {:?}", refusal.error),
        },
        Err(refusal) => println!("  rest REFUSED {:?}", refusal.error),
    }

    println!(
        "\n  card apparatus receipts     {}",
        world.card_apparatus().len()
    );
    Ok(())
}

/// Print the ARTIFACT — the emitted text — before any count.
fn print_answer(label: &str, answer: &AgenticResearchAnswer, millis: u128) {
    println!("\n  ── {label} ANSWER — THE ARTIFACT ──");
    println!("  eros> {}", answer.answer.text);
    println!("\n  causes and lineage");
    println!(
        "    episode            {}",
        answer.answer.answer_episode_identity
    );
    println!("    world deed         {:?}", answer.answer.world_deed);
    println!(
        "    novel contiguous   {}",
        answer.answer.novel_contiguous_surface
    );
    let causes = answer_causes(&answer.answer);
    println!("    causes             {}", causes.len());
    for cause in causes.iter().take(12) {
        println!("      {cause}");
    }
    println!(
        "    evidence sources   {}",
        answer.answer.evidence_sources.len()
    );
    for source in answer.answer.evidence_sources.iter().take(8) {
        println!("      {source}");
    }
    println!(
        "    supporting eps     {}",
        answer.answer.supporting_episode_identities.len()
    );
    println!(
        "    retained alts      {}",
        answer.answer.retained_alternatives.len()
    );
    for alternative in answer.answer.retained_alternatives.iter().take(4) {
        println!("      {alternative:?}");
    }
    println!(
        "    operative codecs   {:?}",
        answer.answer.operative_codec_versions
    );
    println!(
        "    generated tokens   {}   phases {}",
        answer.answer.generated.tokens.len(),
        answer.answer.generated.phases.len()
    );
    match answer.thought.as_ref() {
        Some(thought) => {
            println!("\n  thought");
            println!("    deed               {}", thought.deed);
            println!("    leaders            {}", thought.leaders.len());
            println!("    world returns      {}", thought.returns.len());
            println!("    waves              {}", thought.waves.len());
            println!(
                "    conditioned        {} -> {}",
                thought.conditioned_passages_before, thought.conditioned_passages_after
            );
            for leader in thought.leaders.iter().take(6) {
                println!(
                    "      leader {} generation {} region {:?}",
                    leader.identity, leader.generation, leader.region
                );
            }
            for returned in thought.returns.iter().take(4) {
                println!(
                    "      return from leader {} sections {}",
                    returned.leader,
                    returned.sections.len()
                );
                for section in returned.sections.iter().take(2) {
                    let text = section.text.replace('\n', " ");
                    let text = text.trim();
                    let shown = text.chars().take(160).collect::<String>();
                    println!("        [{}] {shown}", section.source);
                }
            }
        }
        None => println!("\n  thought            NONE — the answer conducted with no world deed"),
    }
    println!("\n    elapsed            {millis} ms");
}

fn inherited_language_body(root: &Path) -> Result<Vec<MorphologicalLanguagePassage>, String> {
    INHERITED_LANGUAGE_RECORDS
        .iter()
        .enumerate()
        .map(|(at, relative)| {
            let path = root.join(relative);
            let text = fs::read_to_string(&path)
                .map_err(|e| format!("read inherited language {}: {e}", path.display()))?;
            Ok(MorphologicalLanguagePassage::new(
                format!("inherited-language-record-{at}"),
                (*relative).to_owned(),
                u64::try_from(at)
                    .ok()
                    .and_then(|at| at.checked_add(10))
                    .ok_or_else(|| "inherited receiver extent overflowed".to_owned())?,
                text,
            ))
        })
        .collect()
}

/// The declared text world, built from the same six live records. Every section is a paragraph of
/// a tracked file; nothing is authored.
fn declared_text_documents(root: &Path) -> Result<Vec<ParsedTextDocument>, String> {
    INHERITED_LANGUAGE_RECORDS
        .iter()
        .enumerate()
        .map(|(at, relative)| {
            let path = root.join(relative);
            let text = fs::read_to_string(&path)
                .map_err(|e| format!("read declared text {}: {e}", path.display()))?;
            let sections = text
                .split("\n\n")
                .map(|paragraph| paragraph.split_whitespace().collect::<Vec<_>>().join(" "))
                .filter(|paragraph| !paragraph.is_empty())
                .collect::<Vec<_>>();
            Ok(ParsedTextDocument {
                identity: format!("declared-research-record-{at}"),
                source: (*relative).to_owned(),
                sections,
            })
        })
        .collect()
}

/// Map this repository's live layout into the layout `mount_repository_excluding` walks. Symlinks
/// only — no bytes are copied and no live file is touched. `path.is_dir()` follows symlinks, which
/// is what makes a directory-level link sufficient.
/// The declared world: named files only, symlinked one at a time.
fn build_declared_fixture(
    root: &Path,
    fixture: &Path,
    support_records: usize,
) -> Result<Vec<(String, String)>, String> {
    let _ = fs::remove_dir_all(fixture);
    let mut mapped = Vec::new();
    for (named, at) in DECLARED_WORLD_THEORY
        .iter()
        .chain(DECLARED_WORLD_SUPPORT.iter().take(support_records))
        .map(|named| (*named, "research/records"))
        .chain(
            DECLARED_WORLD_RUST
                .iter()
                .map(|named| (*named, "soma/life/src")),
        )
    {
        let from = root.join(named);
        if !from.is_file() {
            return Err(format!("declared world file is absent: {named}"));
        }
        let directory = fixture.join(at);
        fs::create_dir_all(&directory)
            .map_err(|e| format!("create fixture {}: {e}", directory.display()))?;
        let into = directory.join(Path::new(named).file_name().expect("a file name"));
        std::os::unix::fs::symlink(&from, &into)
            .map_err(|e| format!("link {} -> {}: {e}", into.display(), from.display()))?;
        mapped.push((
            named.to_owned(),
            format!(
                "{at}/{}",
                Path::new(named).file_name().unwrap().to_string_lossy()
            ),
        ));
    }
    Ok(mapped)
}

fn build_repository_fixture(root: &Path, fixture: &Path) -> Result<Vec<(String, String)>, String> {
    let _ = fs::remove_dir_all(fixture);
    let mut mapped = Vec::new();
    for (live, at) in FIXTURE_REPOSITORY_DIRECTORIES.iter() {
        let from = root.join(live);
        if !from.is_dir() {
            continue;
        }
        let into = fixture.join(at);
        if let Some(parent) = into.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("create fixture {}: {e}", parent.display()))?;
        }
        std::os::unix::fs::symlink(&from, &into)
            .map_err(|e| format!("link {} -> {}: {e}", into.display(), from.display()))?;
        mapped.push(((*live).to_owned(), (*at).to_owned()));
    }
    Ok(mapped)
}

/// The complete local star unless the caller forces a finite aperture.
fn research_spec(arguments: &Arguments) -> LaboratoryResearchSpec {
    let mut spec = if arguments.leader_aperture == 0 {
        LaboratoryResearchSpec::complete_local_star()
    } else {
        LaboratoryResearchSpec {
            leader_aperture: arguments.leader_aperture,
            ..LaboratoryResearchSpec::default()
        }
    };
    spec.worker_threads = arguments.threads;
    spec.thought_receiver_horizon = arguments.thought_receiver_horizon;
    spec
}

fn repository_root() -> PathBuf {
    // `soma/life` -> the repository root is two levels up, not three: the laboratory kept its life
    // crate at `src/soma/life`.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root resolves")
}

fn arguments() -> Result<Arguments, String> {
    let mut arguments = Arguments::default();
    let mut input = std::env::args().skip(1);
    while let Some(argument) = input.next() {
        let mut value = || {
            input
                .next()
                .ok_or_else(|| format!("{argument} needs a value"))
        };
        match argument.as_str() {
            "--text-rest" => arguments.text_rest = Some(value()?.into()),
            "--fixture" => arguments.fixture = Some(value()?.into()),
            "--question" => arguments.question = Some(value()?),
            "--support-records" => {
                arguments.support_records = value()?.parse().map_err(|e| format!("{e}"))?
            }
            "--world" => {
                let named = value()?;
                arguments.whole_repository = match named.as_str() {
                    "declared" => false,
                    "repository" => true,
                    other => {
                        return Err(format!("--world takes declared|repository, not {other:?}"))
                    }
                };
            }
            "--leader-aperture" => {
                arguments.leader_aperture = value()?.parse().map_err(|e| format!("{e}"))?
            }
            "--threads" => arguments.threads = value()?.parse().map_err(|e| format!("{e}"))?,
            // `--output-aperture` is REMOVED, not deprecated. It parsed into a field that was
            // passed to nothing, so it advertised a bound the organ never applied. An unknown-
            // argument refusal is honest; silently accepting a number that governs nothing is not.
            "--observation-aperture" => {
                arguments.observation_aperture = value()?.parse().map_err(|e| format!("{e}"))?
            }
            "--thought-horizon" => {
                arguments.thought_receiver_horizon = value()?.parse().map_err(|e| format!("{e}"))?
            }
            other => return Err(format!("unknown argument {other:?}")),
        }
    }
    arguments.threads = arguments.threads.max(1);
    Ok(arguments)
}

/// Kept so the unused-import lint does not hide a genuine divergence later.
#[allow(dead_code)]
fn unused_marker() -> BTreeMap<String, usize> {
    BTreeMap::new()
}
