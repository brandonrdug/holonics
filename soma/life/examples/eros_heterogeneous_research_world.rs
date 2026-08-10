//! THE HETEROGENEOUS WORLD CONDUCTS — four materials, one leader, one transport.
//!
//! ```text
//! cargo run --release -p life --example eros_heterogeneous_research_world -- \
//!     [--with-code-deeds] [--rollout <path>] [--rollout-cap <octets>]
//! ```
//!
//! ## What this closes
//!
//! `soma/life/src/research_intelligence.rs` (784 lines) and `soma/life/src/dialogue_lineage.rs`
//! (499 lines) had **in-degree zero from everything**. `blueprint/THE_ROADMAP.md` recorded
//! `research_intelligence` as *"fully constructed and one call site short of reachable"* and set
//! the falsifier itself: for each dead organ, **either a driver that conducts through it and
//! returns an artifact, or removal** (`CLAUDE.md` §13 rule 3). This is that driver, and it reaches
//! both organs at once, because `ExactResearchWorld::new` requires an `ExactDialogueLineage` — the
//! two modules were dead *together*.
//!
//! ## Why it could not have run before today, which is the real finding
//!
//! `execute_rust` invoked cargo with `current_dir(root.join("src/soma"))`. That is the **archived
//! laboratory's** directory layout, folded into the one organ whose entire purpose is executing in
//! a foreign chart. No such path exists in this body, so the code section of this world could not
//! return here at any commit. `CLAUDE.md` §0's second lesson is *no absolute frame in a lineage*;
//! a module that is dead is also a module nobody could have noticed carried one. Repaired
//! 2026-08-10 to use the declared workspace root verbatim.
//!
//! ## The receiver question
//!
//! **Does one leader's region reach several materials at once, and do the exterior materials stay
//! absent until a leader's own region causes their deed?**
//!
//! `ExactResearchWorld` composes four receiver sections — repository inscriptions, visible Codex
//! dialogue, exact arithmetic monodromy, and real `cargo test` execution. Its own opening states
//! the law under test: *"Mathematical and code results do not exist as conditioning passages until
//! the corresponding leader causes their deeds and the exterior world returns."* That is a
//! falsifiable claim about **causation**, not a count, so it is measured with a control leader
//! whose region anchors nothing and which must therefore cause no deed at all.
//!
//! ## The apertures, declared
//!
//! ```text
//!   dialogue          ONE Codex rollout: `--rollout` when the caller names one, else the
//!                     largest on disk at most `--rollout-cap` octets
//!                     (default 32 MiB), named in the artifact with its raw extent and prefix
//!                     hash, and the population above the cap is printed rather than dropped
//!                     silently. `include_commentary` is true, so assistant commentary is
//!                     admitted and counted separately from final answers.
//!   repository        research/records + papers + Rust sources under the production roots,
//!                     minus this driver's own grading exclusions.
//!   mathematics       one quintic, one Euler receiver, integers through 41.
//!   code              off by default. `cargo test` inside a driver launched by cargo is real
//!                     exterior execution and costs a full build; `--with-code-deeds` declares it.
//! ```

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{EulerReceiverId, QuinticProblemId};
use life::{
    dialogue_lineage::{CodexDialogueImportSpec, ExactDialogueLineage},
    laboratory_language::{
        LaboratoryLanguageError, LaboratoryResearchLeader, LaboratorySourceAtlas,
        LaboratoryWorldReturn,
    },
    research_intelligence::{ExactQuinticResearchSpec, ExactResearchWorld, RustVerificationSpec},
};
use num_bigint::BigInt;

/// The aperture ladder's first rung. It is 1 because the ladder DOUBLES off the material from
/// here; no rung above it is authored. See `admitting_aperture`.
const FIRST_APERTURE: usize = 1;

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

/// Every Codex rollout on disk, largest first, so the aperture is read off the material.
fn codex_rollouts(root: &Path) -> Vec<(u64, PathBuf)> {
    let mut found = Vec::new();
    let mut frontier = vec![root.to_path_buf()];
    while let Some(at) = frontier.pop() {
        let Ok(entries) = std::fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                frontier.push(path);
            } else if path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("rollout-") && name.ends_with(".jsonl"))
            {
                let octets = entry.metadata().map(|meta| meta.len()).unwrap_or(0);
                found.push((octets, path));
            }
        }
    }
    found.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));
    found
}

fn leader(
    identity: &str,
    question: &str,
    region: &[&str],
    generation: usize,
) -> LaboratoryResearchLeader {
    LaboratoryResearchLeader {
        identity: identity.to_owned(),
        question: question.to_owned(),
        region: region.iter().map(|word| (*word).to_owned()).collect(),
        aperture: FIRST_APERTURE,
        generation,
        caused_by_clauses: BTreeSet::new(),
    }
}

/// The smallest aperture on a doubling ladder at which the repository atlas admits this leader,
/// together with every rung that refused.
///
/// The atlas **refuses** rather than truncating when a leader encounters more sections than its
/// declared aperture, and its refusal names only `aperture + 1` — not the total — so no single
/// probe can report the bound. The ladder is therefore how the caller reads its own aperture off
/// the material instead of authoring one and raising it until the error stops, which is the level
/// pinning `CLAUDE.md` §8 convicts.
///
/// The probe runs against the atlas, which enacts through `&self`. Nothing in the world moves.
fn admitting_aperture(
    repository: &LaboratorySourceAtlas,
    leader: &LaboratoryResearchLeader,
) -> Result<(usize, Vec<usize>), String> {
    let mut probe = leader.clone();
    let mut refused = Vec::new();
    let mut aperture = FIRST_APERTURE;
    loop {
        probe.aperture = aperture;
        match repository.enact(&probe) {
            Ok(_) => return Ok((aperture, refused)),
            Err(LaboratoryLanguageError::ReceiverAperture { .. }) => {
                refused.push(aperture);
                aperture = aperture
                    .checked_mul(2)
                    .ok_or_else(|| "aperture ladder extent".to_owned())?;
            }
            Err(other) => return Err(format!("aperture probe: {other:?}")),
        }
    }
}

/// One leader's return, split by which material carried each section.
struct MaterialSplit<'a> {
    repository: Vec<&'a life::laboratory_language::LaboratoryReturnedSection>,
    dialogue: Vec<&'a life::laboratory_language::LaboratoryReturnedSection>,
    mathematics: Vec<&'a life::laboratory_language::LaboratoryReturnedSection>,
    code: Vec<&'a life::laboratory_language::LaboratoryReturnedSection>,
}

impl MaterialSplit<'_> {
    fn report(&self, leader: &str) {
        println!(
            "\n  {leader} — repository {}, dialogue {}, mathematics {}, code {}",
            self.repository.len(),
            self.dialogue.len(),
            self.mathematics.len(),
            self.code.len()
        );
        for (material, sections) in [
            ("repository", &self.repository),
            ("dialogue", &self.dialogue),
            ("mathematics", &self.mathematics),
            ("code", &self.code),
        ] {
            if sections.is_empty() {
                println!("    --- {material}: nothing returned ---");
                continue;
            }
            println!("    --- {material} ---");
            for section in sections.iter().take(3) {
                let text: String = section.text.chars().take(140).collect();
                println!("      [{}] {}", section.source, text.replace('\n', " "));
            }
            if sections.len() > 3 {
                println!("      ... and {} more", sections.len() - 3);
            }
        }
    }
}

fn split_by_material(returned: &LaboratoryWorldReturn) -> MaterialSplit<'_> {
    let mut split = MaterialSplit {
        repository: Vec::new(),
        dialogue: Vec::new(),
        mathematics: Vec::new(),
        code: Vec::new(),
    };
    for section in &returned.sections {
        if section.source.starts_with("codex-dialogue/") {
            split.dialogue.push(section);
        } else if section.source.starts_with("mathematics-return/") {
            split.mathematics.push(section);
        } else if section.source.starts_with("code-return/") {
            split.code.push(section);
        } else {
            split.repository.push(section);
        }
    }
    split
}

/// Enact one leader at the aperture the material admits, reporting the ladder that found it.
fn enact_at_admitting_aperture(
    world: &mut ExactResearchWorld<'_>,
    repository: &LaboratorySourceAtlas,
    leader: &LaboratoryResearchLeader,
) -> Result<(LaboratoryWorldReturn, usize, Vec<usize>), String> {
    let (aperture, refused) = admitting_aperture(repository, leader)?;
    let mut admitted = leader.clone();
    admitted.aperture = aperture;
    let returned = world
        .enact(&admitted)
        .map_err(|error| format!("{} at aperture {aperture}: {error:?}", leader.identity))?;
    Ok((returned, aperture, refused))
}

fn main() -> Result<(), String> {
    let with_code_deeds = std::env::args().any(|argument| argument == "--with-code-deeds");
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| "resolve the workspace root".to_owned())?
        .to_path_buf();
    let home = PathBuf::from(std::env::var("HOME").unwrap_or_else(|_| "/home/b".to_owned()));

    rule("THE DIALOGUE MEMBRANE — dialogue_lineage, reached for the first time");

    let rollouts = codex_rollouts(&home.join(".codex/sessions"));
    if rollouts.is_empty() {
        return Err("no Codex rollout at the declared root".to_owned());
    }
    // The container is the caller's declaration when the caller makes one.
    let named_rollout = std::env::args()
        .skip_while(|argument| argument != "--rollout")
        .nth(1)
        .map(PathBuf::from);
    let rollout_cap: u64 = std::env::args()
        .skip_while(|argument| argument != "--rollout-cap")
        .nth(1)
        .and_then(|read| read.parse().ok())
        .unwrap_or(32 * 1024 * 1024);
    let above_cap = rollouts.iter().filter(|(octets, _)| *octets > rollout_cap).count();
    let (octets, rollout) = match named_rollout {
        Some(named) => {
            let octets = std::fs::metadata(&named)
                .map(|meta| meta.len())
                .map_err(|error| format!("inspect {}: {error}", named.display()))?;
            (octets, named)
        }
        None => rollouts
            .iter()
            .find(|(octets, _)| *octets <= rollout_cap)
            .cloned()
            .ok_or_else(|| format!("every rollout on disk exceeds the declared cap {rollout_cap}"))?,
    };
    println!("  rollouts on disk      {:>5}", rollouts.len());
    println!(
        "  above the cap         {above_cap:>5}   (cap {rollout_cap} octets, largest {})",
        rollouts[0].0
    );
    println!("  the one taken         {} ({octets} octets)", rollout.display());

    let began = Instant::now();
    let dialogue = ExactDialogueLineage::import_codex_rollout(
        &rollout,
        &CodexDialogueImportSpec::default(),
    )?;
    let receipt = dialogue.receipt();
    println!("\n  raw extent            {:>9}", receipt.raw_extent);
    println!("  raw prefix sha256     {}", receipt.raw_prefix_sha256);
    println!("  complete records      {:>9}", receipt.complete_records);
    println!("  visible occurrences   {:>9}", receipt.visible_occurrences);
    println!("    user                {:>9}", receipt.user_occurrences);
    println!(
        "    assistant final     {:>9}",
        receipt.assistant_final_occurrences
    );
    println!(
        "    assistant commentary{:>9}",
        receipt.assistant_commentary_occurrences
    );
    println!(
        "    assistant other     {:>9}",
        receipt.assistant_other_occurrences
    );
    println!(
        "  excluded control      {:>9}   (tool calls, reasoning, scheduling — never linguistic)",
        receipt.excluded_control_occurrences
    );
    println!(
        "  founded identities    {:>9}   (container supplied no `id`; the record address founds one)",
        receipt.founded_identity_occurrences
    );
    if receipt.founded_identity_occurrences > 0 {
        println!(
            "                                  BEFORE 2026-08-10 THIS CONTAINER WAS REFUSED WHOLE."
        );
    }
    println!("  imported in           {:.2}s", began.elapsed().as_secs_f64());

    rule("THE REPOSITORY ATLAS — the second material");

    let began = Instant::now();
    let repository = LaboratorySourceAtlas::mount_repository_excluding(&root, &BTreeSet::new())
        .map_err(|error| format!("mount the repository atlas: {error:?}"))?;
    println!(
        "  mounted in {:.2}s: {:?}",
        began.elapsed().as_secs_f64(),
        repository.receipt()
    );

    rule("THE WORLD — four receiver sections composed on one root");

    let quintic = ExactQuinticResearchSpec::new(
        "quintic/monodromy",
        QuinticProblemId(1),
        vec![
            BigInt::from(-1),
            BigInt::from(1),
            BigInt::from(0),
            BigInt::from(0),
            BigInt::from(0),
            BigInt::from(1),
        ],
        EulerReceiverId(1),
        // sigma: the engine refuses any sigma <= 1 (`Euler sigma must be an integer greater than
        // one`), because the Euler product does not converge on or left of the abscissa. 2 is the
        // first admitted receiver.
        2,
        41,
        8,
    )?;
    let rust_specs = vec![
        RustVerificationSpec::new(
            "rust/fork",
            "life",
            "agentic_language::tests::the_two_arms_of_a_fork_diverge_only_by_what_each_received",
            "A non-consuming fork yields two causally independent arms.",
        )?,
        RustVerificationSpec::new(
            "rust/remount",
            "life",
            "agentic_language::tests::remount_refuses_a_body_its_declared_causes_do_not_reproduce",
            "A body its declared causes do not reproduce refuses to remount.",
        )?,
    ];

    let mut world = ExactResearchWorld::new(
        &root,
        &repository,
        &dialogue,
        quintic,
        rust_specs,
    )?;
    println!(
        "  dialogue conditioned occurrences  {:>6}",
        world.dialogue_conditioned_occurrences()
    );
    println!(
        "  dialogue indexed features         {:>6}",
        world.dialogue_indexed_features()
    );
    println!(
        "  dialogue local sections           {:>6}",
        world.dialogue_local_sections()
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE CONTROL — a leader whose region anchors NO exterior deed");

    // This runs FIRST and on purpose. If the mathematics or code receipt were already populated
    // before any leader anchored on them, the causation claim would be decoration. The control is
    // the falsifier for the whole law under test.
    let inert = leader(
        "control/inert",
        "What does the returned section retain?",
        &["retained", "section", "returned"],
        0,
    );
    let (inert_return, inert_aperture, inert_refused) =
        enact_at_admitting_aperture(&mut world, &repository, &inert)?;
    println!(
        "  region                {:?}",
        inert.region.iter().collect::<Vec<_>>()
    );
    println!(
        "  aperture ladder       refused at {inert_refused:?}, admitted at {inert_aperture}"
    );
    println!("  sections returned     {:>6}", inert_return.sections.len());
    split_by_material(&inert_return).report("control/inert");
    println!(
        "  complete population   {:>6}   omitted {}",
        inert_return.complete_population, inert_return.omitted_population
    );
    println!(
        "  mathematics receipt   {}",
        if world.quintic_receipt().is_some() {
            "PRESENT  <-- the law under test is FALSE"
        } else {
            "absent   <-- no leader anchored on it, so it does not exist"
        }
    );
    println!(
        "  code receipts         {}",
        world.rust_receipts().len()
    );
    if world.quintic_receipt().is_some() || !world.rust_receipts().is_empty() {
        return Err(
            "an exterior deed was enacted for a leader whose region anchored nothing".to_owned(),
        );
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE MATHEMATICS SECTION — caused by a region that anchors on it");

    let arithmetic = leader(
        "leader/monodromy",
        "What does the Euler receiver return for the quintic monodromy?",
        &["quintic", "monodromy", "euler", "galois", "receiver"],
        1,
    );
    let began = Instant::now();
    let (arithmetic_return, arithmetic_aperture, arithmetic_refused) =
        enact_at_admitting_aperture(&mut world, &repository, &arithmetic)?;
    println!(
        "  aperture ladder       refused at {arithmetic_refused:?}, admitted at {arithmetic_aperture}"
    );
    println!(
        "  enacted in {:.2}s; sections {}",
        began.elapsed().as_secs_f64(),
        arithmetic_return.sections.len()
    );
    let mathematics_receipt = world
        .quintic_receipt()
        .ok_or_else(|| "an anchored arithmetic region caused no mathematics deed".to_owned())?;
    println!("\n  THE ARTIFACT — the exact returned receipt, not a count:");
    println!("    schema                {}", mathematics_receipt.schema);
    println!("    deed                  {}", mathematics_receipt.deed);
    println!(
        "    euler product         {} / {}",
        mathematics_receipt.euler_product_numerator, mathematics_receipt.euler_product_denominator
    );
    println!(
        "    cross-prime gluing    {}",
        mathematics_receipt.cross_prime_root_sheet_gluing
    );
    println!(
        "    lineage reused exact  {}",
        mathematics_receipt.lineage_reused_exactly
    );

    let arithmetic_split = split_by_material(&arithmetic_return);
    arithmetic_split.report("leader/monodromy");
    if arithmetic_split.mathematics.is_empty() {
        return Err("the anchored arithmetic leader received no mathematics section".to_owned());
    }
    if arithmetic_split.repository.is_empty() {
        return Err("the repository material returned nothing".to_owned());
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE DIALOGUE SECTION — a leader whose region is READ OFF the dialogue itself");

    // The arithmetic leader's region is mathematical vocabulary, and this rollout's twelve visible
    // occurrences do not carry it, so that leader receives zero dialogue sections. That is the
    // correct return and not a defect — but it does not establish that the dialogue material
    // conducts. This leader's region is taken from an actual user occurrence in the container, so
    // the material is reached by its own words rather than by words chosen to make it reach.
    let user_occurrence = dialogue
        .occurrences()
        .iter()
        .find(|occurrence| {
            occurrence.speaker == life::dialogue_lineage::DialogueSpeaker::User
                && occurrence.text.split_whitespace().count() > 12
        })
        .ok_or_else(|| "the container carried no user occurrence to read a region off".to_owned())?;
    let region_words: Vec<String> = user_occurrence
        .text
        .split_whitespace()
        .filter(|word| word.chars().all(char::is_alphabetic) && word.len() > 5)
        .map(str::to_lowercase)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let region: Vec<&str> = region_words.iter().map(String::as_str).collect();
    println!("  the occurrence        {} ({:?})", user_occurrence.identity, user_occurrence.identity_species);
    println!("  its region, verbatim  {region:?}");
    let dialogue_leader = leader(
        "leader/dialogue",
        &user_occurrence.text,
        &region,
        3,
    );
    let (dialogue_return, dialogue_aperture, dialogue_refused) =
        enact_at_admitting_aperture(&mut world, &repository, &dialogue_leader)?;
    println!(
        "  aperture ladder       refused at {dialogue_refused:?}, admitted at {dialogue_aperture}"
    );
    let dialogue_split = split_by_material(&dialogue_return);
    dialogue_split.report("leader/dialogue");
    if dialogue_split.dialogue.is_empty() {
        return Err("the dialogue material returned nothing to a leader read off it".to_owned());
    }
    if dialogue_split.repository.is_empty() {
        return Err(
            "the dialogue-derived region reached no repository section, so nothing was joined"
                .to_owned(),
        );
    }
    println!(
        "\n  THE JOIN: one region, read off a Codex message, reached {} dialogue sections AND\n  \
         {} repository sections in the same return. Neither material was told about the other,\n  \
         and no fusion module exists.",
        dialogue_split.dialogue.len(),
        dialogue_split.repository.len()
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE CODE SECTION — real exterior execution");

    if with_code_deeds {
        let code = leader(
            "leader/code",
            "Does the fork test return, and does the remount refuse?",
            &["rust", "code", "test", "fork", "remount"],
            2,
        );
        let began = Instant::now();
        let (code_return, code_aperture, code_refused) =
            enact_at_admitting_aperture(&mut world, &repository, &code)?;
        println!(
            "  aperture ladder       refused at {code_refused:?}, admitted at {code_aperture}"
        );
        println!(
            "  enacted in {:.1}s; sections {}",
            began.elapsed().as_secs_f64(),
            code_return.sections.len()
        );
        if world.rust_receipts().is_empty() {
            return Err("an anchored code region caused no code deed".to_owned());
        }
        split_by_material(&code_return).report("leader/code");
        println!("\n  THE ARTIFACT — what the exterior compiler actually returned:");
        for (identity, receipt) in world.rust_receipts() {
            println!(
                "    {identity:<16} success={} exit={:?} {}ms",
                receipt.success, receipt.exit_code, receipt.elapsed_millis
            );
            println!("      claim   {}", receipt.claim);
            println!("      stdout  sha256 {}", receipt.stdout_sha256);
        }
    } else {
        println!(
            "  NOT RUN. `cargo test` from inside a cargo-launched driver is real exterior\n  \
             execution and costs a full build. Declare it: `-- --with-code-deeds`.\n  \
             This is a declared aperture, not a silent omission (`CLAUDE.md` §8)."
        );
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE ACTIVITY — what the transport cost, in work rather than in time");

    let activity = world.activity_receipt();
    println!("  {activity:#?}");

    rule("BOUNDS");
    println!("  - One rollout, not the corpus. The membrane admits one container per import; a");
    println!("    population reading needs a driver that states its own ladder.");
    println!("  - `execute_rust` ran against a laboratory-layout path until today. Any earlier");
    println!("    claim that the code section returned here would have been false.");
    println!("  - Timings carry one frame and are therefore not falsifiable (`CLAUDE.md` §8).");
    Ok(())
}
