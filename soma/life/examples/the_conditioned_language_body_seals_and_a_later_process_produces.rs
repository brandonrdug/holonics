//! **★ THE MODEL AND THE PRODUCTION MEET.**
//!
//! Measured 2026-08-18, before this driver existed: `grep -rln ErosRest` and
//! `grep -rln CausalLanguageEcology` over `crates` and `soma` returned two file sets whose
//! **intersection was empty**. The organ that holds a whole body and the organ that produces
//! language had never appeared in one file. So a conditioned language body could be described
//! across a seam and never *resumed* across one, and every generation started from an origin
//! instead of continuing from where the last one stood.
//!
//! This driver closes that edge, and it is the shape Brandon specified on 2026-08-15:
//!
//! > *"we can instantiate models of Eros that are 'pretrained' in the sense that they are
//! > **conditioned ecological neural networks stored and able to be recycled into active
//! > processes**."*
//!
//! ## What runs
//!
//! ```text
//!   SEAL     condition on real repository material -> generate -> seal the WHOLE ecology
//!            into an ErosRest organ -> write octets to disk
//!   RESUME   a SECOND OS PROCESS with no corpus argument mounts those octets alone,
//!            reconstructs the ecology, and generates
//!   CONTROL  the same second process with the sealed octets DELETED must refuse
//! ```
//!
//! **The detachment is real.** The resume process is `std::process::Command`, not a `drop()`, and it
//! is given the rest path and nothing else — no corpus path, no passage text. If it produces, it
//! produced from the sealed body.
//!
//! **The falsifier, quoted from the roadmap that owes it:** *"the second conditioning must fail if
//! the sealed form is deleted between the two turns. A return that survives the deletion of the
//! world's record never went through it."* That arm runs here as `CONTROL`.
//!
//! **Nothing here selects.** The generation returns its whole population; this driver prints all of
//! it and takes no maximum.
//!
//! Run:
//! ```text
//!   cargo run --release -p life --example the_conditioned_language_body_seals_and_a_later_process_produces
//! ```

use std::collections::BTreeSet;
use life::causal_language::lexical_tokens;
use std::path::PathBuf;

use body::channel::LineageChannel;
use body::num::Cog;
use life::causal_language::{
    BranchingLaw, CausalLanguageEcology, CausalLanguageGenerationSpec, CausalLanguagePassage,
    ContinuationReceiver,
};
use life::eros_rest::{ErosRest, OrganRest};
use life::presentation_quotient::{
    divide_junction, JunctionDivision, PresentationMaterial, PresentationReceiver,
    PresentedCandidate,
};
use soma_abi::active::ActionCurrent;

/// The organ name the language body is sealed under inside the whole-body rest.
const LANGUAGE_ORGAN: &str = "causal-language-ecology";

/// **Declared aperture, and its reason is measured rather than chosen.** Generation branches
/// super-exponentially in this parameter — 1 token 57 ms, 2 tokens 403 ms, 4 tokens 55,098 ms,
/// 8 tokens no return in 200 s, measured at `a91a84f` and carried by
/// `eros_causal_language_generation`. This is a **receiver parameter and never the law**, and the
/// front cost is reported below as an open finding rather than hidden by the bound.
const GENERATED_TOKENS: usize = 2;

/// The conditioning material: real repository documents, entering as bits like any other material.
/// Each is one passage under its own receiver, so the receiver axis is genuinely plural.
const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

/// The prompts. The first two are drawn from the material's own vocabulary; the third is a control
/// built from words the material does not carry, which must emit nothing rather than fabricate.
const PROMPTS: &[&str] = &["the receiver", "a compression is"];
const CONTROL_PROMPT: &str = "zzqx wubblefrump gorptangle";
/// The prompt the two riding processes are both asked. Declared once so the only difference between
/// them is the body they mounted.
const RIDE_PROMPT: &str = "the receiver";

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let outcome = match arguments.get(1).map(String::as_str) {
        Some("--resume") => resume(arguments.get(2).map(PathBuf::from)),
        Some("--ride") => ride(arguments.get(2).map(PathBuf::from)),
        _ => seal_and_dispatch(),
    };
    if let Err(reason) = outcome {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

/// The action current every conduct in this driver runs under. **A zero construction is the
/// absence of an event action, not a second spelling of one**, so this refuses rather than
/// defaulting.
fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

fn passages() -> Result<Vec<CausalLanguagePassage>, String> {
    let mut carried = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        carried.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    Ok(carried)
}

/// The inherited surfaces the span receiver reads against — the same material the body was
/// conditioned on, tokenized by the same law the emission uses.
fn presentation_material() -> Result<PresentationMaterial, String> {
    let mut inherited_surfaces = Vec::new();
    for (path, _) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        inherited_surfaces.push(lexical_tokens(&text));
    }
    Ok(PresentationMaterial { inherited_surfaces })
}

fn spec() -> CausalLanguageGenerationSpec {
    CausalLanguageGenerationSpec {
        maximum_generated_tokens: GENERATED_TOKENS,
        stop_at_sentence_boundary: true,
        // The complete junction: the whole population branches and NOTHING is filtered. The
        // horizon gate is retained in the organ as a negative control and is not used here.
        branching_law: BranchingLaw::CompleteJunction,
        continuation_receiver: ContinuationReceiver::MostSpecificAttestation,
    }
}

/// Present the conducted population to the division, carrying each emission's own horizons and
/// attesting sources. **Nothing is selected here** — every output becomes a candidate.
fn presented(
    generation: &life::causal_language::CausalLanguageGeneration,
) -> Vec<PresentedCandidate> {
    generation
        .outputs
        .iter()
        .enumerate()
        .map(|(at, text)| PresentedCandidate {
            identity: format!("c{at}"),
            tokens: text.tokens.iter().map(|t| t.token.clone()).collect(),
            matched_horizons: text.tokens.iter().map(|t| t.matched_horizon).collect(),
            sources: text
                .tokens
                .iter()
                .map(|t| t.sources.iter().cloned().collect())
                .collect(),
        })
        .collect()
}

/// **★ THE RESPONSE.** The whole junction goes in; the quotient's blocks come out.
fn respond(division: &JunctionDivision) {
    let (candidates, blocks) = division.compression();
    println!("    ---- THE DIVISION ----");
    println!("    receiver family    {:?}", division.family);
    println!("    candidates in      {candidates}");
    println!("    one-shot blocks    {}", division.one_shot_blocks);
    println!("    conduct blocks     {blocks}   <- THE RESPONSE POPULATION");
    println!("    refinement rounds  {}", division.rounds);
    println!("    collapsed pairs    {}   (the division's exact loss, exhibited)", division.collapsed_population);
    println!("    memory order       {:?}", division.memory_order);
    if division.is_determinate() {
        println!("    DETERMINATE: one block. The junction determined the continuation for this");
        println!("    receiver family, and the response is that block.");
    } else {
        println!("    PLURAL: {blocks} blocks. The prompt did not determine the continuation for");
        println!("    this receiver family. That is not a failure -- it is where a clarifying");
        println!("    question comes from, and the questions below are the words that would");
        println!("    collapse it.");
    }
    for (at, block) in division.blocks.iter().enumerate() {
        println!(
            "      block {at}: {} member(s), {} surface(s){}",
            block.members.len(),
            block.surfaces.len(),
            match block.wholly_inherited {
                Some(true) => ", wholly inherited",
                Some(false) => ", composed",
                None => ", span unreadable (this receiver is blind to the material)",
            }
        );
        for surface in block.surfaces.iter().take(4) {
            println!("        {surface:?}");
        }
        if block.surfaces.len() > 4 {
            println!("        ... {} more surfaces in this block", block.surfaces.len() - 4);
        }
    }
    println!("    ---- THE QUESTIONS the machine would ask ----");
    if division.questions.is_empty() {
        println!("      none: no pair of blocks was separated by a word, so nothing to ask.");
    }
    println!("    separating readings returned: {}", division.questions.len());
    for question in division.questions.iter().take(6) {
        println!(
            "      blocks {} / {} separate on word {:?}{}",
            question.left_block,
            question.right_block,
            question.word,
            if question.separated_by_terminus { "  (one continues, one ends)" } else { "" }
        );
        if let Some((receiver, left, right)) = &question.witness {
            println!("        seen by {receiver:?}: {left} against {right}");
        }
    }
    if division.questions.len() > 6 {
        println!("      ... {} more separating words retained", division.questions.len() - 6);
    }
}

/// Print a generation's WHOLE population, decoded. No maximum, no ranking, no truncation.
fn report(label: &str, generation: &life::causal_language::CausalLanguageGeneration) {
    println!("  {label}");
    println!("    prompt tokens      {:?}", generation.prompt_tokens);
    println!("    recruited sources  {}", generation.initial_hexis.len());
    for source in &generation.initial_hexis {
        println!(
            "      {} (receiver {}) supported by {} features",
            source.identity,
            source.receiver,
            source.supporting_features.len()
        );
    }
    println!("    peak front extent  {}", generation.peak_front_extent);
    println!("    emitted population {}   <- THE FIBER, not the answer", generation.outputs.len());
    if generation.peak_front_extent == generation.outputs.len() && generation.outputs.len() > 1 {
        println!("    ** THE FRONT NEVER CLOSED: peak extent EQUALS emitted population, so every");
        println!("       branch tip survived to be emitted and no junction terminated a branch.");
        println!("       The emission is the whole front. This is the missing termination law --");
        println!("       a branch must continue while something reflects and stop when nothing");
        println!("       does -- and it is an open finding, not a tuning parameter.");
    }
    for text in generation.outputs.iter().take(6) {
        println!("      -> {:?}", text.text);
    }
    if generation.outputs.len() > 6 {
        println!("      ... {} more, all retained", generation.outputs.len() - 6);
    }
    if generation.outputs.is_empty() {
        println!("      (nothing was emitted; the population is empty, not withheld)");
    }
    let _ = label;
}

/// Every emitted surface, as a set, so two runs can be compared without ordering entering the
/// comparison.
fn surfaces(generation: &life::causal_language::CausalLanguageGeneration) -> BTreeSet<String> {
    generation
        .outputs
        .iter()
        .map(|text| text.text.clone())
        .collect()
}

fn seal_and_dispatch() -> Result<(), String> {
    println!("SEAL — this process conditions, produces, and seals\n");
    let material = passages()?;
    let total: usize = material.iter().map(|p| p.text.len()).sum();
    println!(
        "  material           {} passages, {total} octets, {} declared receivers",
        material.len(),
        material.iter().map(|p| p.receiver).collect::<BTreeSet<_>>().len()
    );

    let ecology = CausalLanguageEcology::condition(&material, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    println!(
        "  conditioned        {} passages, {} lexical occurrences, {} route receptors",
        ecology.passage_population(),
        ecology.lexical_occurrence_population(),
        ecology.route_receptor_population()
    );

    println!("\n  PRODUCTION, BEFORE THE SEAM");
    let material_faces = presentation_material()?;
    let mut before = Vec::new();
    for prompt in PROMPTS {
        let generation = ecology
            .generate(prompt, spec(), current()?, 8)
            .map_err(|error| format!("generation refused for {prompt:?}: {error:?}"))?;
        report(prompt, &generation);
        let candidates = presented(&generation);
        // **Two frames.** The full family carries `TerminalToken`, which is the candidate's own
        // identity, so its quotient is the identity map and its block count restates the input.
        // The collapsing family withholds exactly that axis. The DIFFERENCE is what the identity
        // face was carrying, and withholding a receiver axis is the ablation shape this corpus
        // names as the one to imitate.
        let full = divide_junction(&candidates, &material_faces, &PresentationReceiver::ALL)
            .map_err(|error| format!("the junction would not divide: {error:?}"))?;
        respond(&full);
        let collapsing =
            divide_junction(&candidates, &material_faces, &PresentationReceiver::COLLAPSING)
                .map_err(|error| format!("the junction would not divide: {error:?}"))?;
        respond(&collapsing);
        println!(
            "    ---- THE AXIS ABLATION ----\n    withholding TerminalToken moves the response \
             population {} -> {}",
            full.conduct_blocks, collapsing.conduct_blocks
        );
        if full.conduct_blocks == collapsing.conduct_blocks {
            println!("    THE AXIS CARRIED NOTHING: the identity face changed no block. Reported");
            println!("    rather than presented as agreement.");
        }
        before.push((prompt.to_string(), surfaces(&generation)));
    }

    // ---- the seal ----
    let language_bytes = ecology
        .encode_native_bytes()
        .map_err(|error| format!("the language body would not seal: {error:?}"))?;
    let rest = ErosRest::seal(
        LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1))),
        Vec::new(),
        vec![OrganRest {
            organ: LANGUAGE_ORGAN.to_owned(),
            bytes: language_bytes.clone(),
        }],
    )
    .map_err(|error| format!("the whole-body seal refused: {error:?}"))?;
    let octets = rest
        .encode_native_bytes()
        .map_err(|error| format!("the rest would not encode: {error:?}"))?;

    let out = PathBuf::from("output/eros-language-rest");
    std::fs::create_dir_all(&out).map_err(|error| format!("{}: {error}", out.display()))?;
    let path = out.join("conditioned-language.erosrest");
    std::fs::write(&path, &octets).map_err(|error| format!("{}: {error}", path.display()))?;
    println!("\n  THE SEAL");
    println!("    language organ   {} octets", language_bytes.len());
    println!("    whole-body rest  {} octets", octets.len());
    println!("    written to       {}", path.display());

    // The round trip inside this process, before any seam: a body that cannot reproduce itself
    // in memory will not reproduce itself across a process, and failing here says which.
    let remounted = CausalLanguageEcology::from_native_bytes(&language_bytes)
        .map_err(|error| format!("the language body would not remount in-process: {error:?}"))?;
    println!(
        "    in-process remount  {} passages, {} route receptors — {}",
        remounted.passage_population(),
        remounted.route_receptor_population(),
        if remounted.passage_population() == ecology.passage_population()
            && remounted.route_receptor_population() == ecology.route_receptor_population()
        {
            "the populations agree"
        } else {
            "THE POPULATIONS DISAGREE"
        }
    );

    // ---- the second process ----
    println!("\nRESUME — a SECOND OS PROCESS, given the rest path and no corpus\n");
    let self_path = std::env::current_exe().map_err(|error| format!("current_exe: {error}"))?;
    let status = std::process::Command::new(&self_path)
        .arg("--resume")
        .arg(&path)
        .status()
        .map_err(|error| format!("could not launch the resuming process: {error}"))?;
    if !status.success() {
        return Err("the resuming process refused; see its output above".to_owned());
    }

    // ---- the control: delete the world's record ----
    println!("\nCONTROL — delete the sealed octets and resume again\n");
    std::fs::remove_file(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    let refused = std::process::Command::new(&self_path)
        .arg("--resume")
        .arg(&path)
        .status()
        .map_err(|error| format!("could not launch the control process: {error}"))?;
    if refused.success() {
        return Err(
            "THE CONTROL FAILED: the resume succeeded with the sealed form deleted, so the return \
             never went through the world's record"
                .to_owned(),
        );
    }
    println!("  the resume REFUSED with the sealed form deleted, as it must.");
    println!("  A return that survives the deletion of the world's record never went through it.");

    println!("\nWHAT THIS ESTABLISHES");
    println!("  A conditioned language body seals whole, crosses a process boundary as octets, and");
    println!("  produces on the far side with no corpus present. That is an INSTANCE rather than a");
    println!("  run: the next process continues from where this one stood instead of starting at an");
    println!("  origin.");
    println!("\nWHAT IT DOES NOT ESTABLISH");
    println!("  The resumed body was not CHANGED by anything on the far side and did not re-seal, so");
    println!("  this is resume-and-produce, not yet condition-again-and-deposit. The declared");
    println!("  aperture is {GENERATED_TOKENS} tokens because the front branches super-exponentially;");
    println!("  that cost is a real open finding and the bound is a receiver parameter, never a law.");
    Ok(())
}

/// Mount one rest and produce. **This process is given a path and nothing else** — no corpus, no
/// prompt list beyond the declared one, no knowledge of which of the two bodies it holds.
fn ride(path: Option<PathBuf>) -> Result<(), String> {
    let path = path.ok_or("the riding process was given no rest path")?;
    let octets = std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    let rest = ErosRest::from_native_bytes(&octets)
        .map_err(|error| format!("the rest would not mount: {error:?}"))?;
    let organ = rest
        .organs()
        .iter()
        .find(|organ| organ.organ == LANGUAGE_ORGAN)
        .ok_or_else(|| format!("the rest carries no organ named {LANGUAGE_ORGAN:?}"))?;
    let ecology = CausalLanguageEcology::from_native_bytes(&organ.bytes)
        .map_err(|error| format!("the language body would not mount: {error:?}"))?;
    println!(
        "    mounted   {} passages, {} occurrences, {} receptors",
        ecology.passage_population(),
        ecology.lexical_occurrence_population(),
        ecology.route_receptor_population()
    );
    let generation = ecology
        .generate(RIDE_PROMPT, spec(), current()?, 8)
        .map_err(|error| format!("generation refused: {error:?}"))?;
    let blind = PresentationMaterial::default();
    let division = divide_junction(
        &presented(&generation),
        &blind,
        &PresentationReceiver::COLLAPSING,
    )
    .map_err(|error| format!("the junction would not divide: {error:?}"))?;
    let surfaces = surfaces(&generation);
    // The horizon profile is what an absorbed occurrence moves even when no new surface appears:
    // the same continuation attested at a deeper nested receiver is a different reading.
    let mut horizons: BTreeSet<(String, u32)> = BTreeSet::new();
    for text in &generation.outputs {
        for token in &text.tokens {
            horizons.insert((token.token.clone(), token.matched_horizon));
        }
    }
    println!("    produced  {} emissions, {} distinct surfaces", generation.outputs.len(), surfaces.len());
    println!("    divided   {} response blocks", division.conduct_blocks);
    println!("    collapsed {} pairs", division.collapsed_population);
    println!("    horizons  {} distinct (token, matched horizon) readings", horizons.len());
    println!(
        "    ATTEST    surfaces={} blocks={} collapsed={} horizons={}",
        surfaces.len(),
        division.conduct_blocks,
        division.collapsed_population,
        horizons.len()
    );
    Ok(())
}

fn resume(path: Option<PathBuf>) -> Result<(), String> {
    let path = path.ok_or("the resuming process was given no rest path")?;
    let octets = std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    let rest = ErosRest::from_native_bytes(&octets)
        .map_err(|error| format!("the rest would not mount: {error:?}"))?;
    let organ = rest
        .organs()
        .iter()
        .find(|organ| organ.organ == LANGUAGE_ORGAN)
        .ok_or_else(|| format!("the rest carries no organ named {LANGUAGE_ORGAN:?}"))?;
    let mut ecology = CausalLanguageEcology::from_native_bytes(&organ.bytes)
        .map_err(|error| format!("the language body would not mount: {error:?}"))?;
    println!("  mounted from octets alone — no corpus was opened by this process");
    println!(
        "    {} passages, {} lexical occurrences, {} route receptors",
        ecology.passage_population(),
        ecology.lexical_occurrence_population(),
        ecology.route_receptor_population()
    );

    println!("\n  PRODUCTION, AFTER THE SEAM");
    // **The span receiver is BLIND on this side, and that is the second frame.** This process has
    // no corpus, so `PresentationMaterial` is empty and `InheritedSpan` returns the same face for
    // every candidate. Withholding a receiver axis is the ablation shape this corpus names as the
    // one to imitate: the division is retaken under a family one axis smaller, and the difference
    // between the two block counts is what that axis was carrying.
    //
    // It is also a real gap, stated as one: the sealed body carries every passage's suffix ecology,
    // so the inherited surfaces ARE in the octets and no reader returns them. Until one does, the
    // far side reads with three faces where the near side read with four.
    let blind = PresentationMaterial::default();
    for prompt in PROMPTS {
        let generation = ecology
            .generate(prompt, spec(), current()?, 8)
            .map_err(|error| format!("generation refused for {prompt:?}: {error:?}"))?;
        report(prompt, &generation);
        let division = divide_junction(
            &presented(&generation),
            &blind,
            &PresentationReceiver::COLLAPSING,
        )
        .map_err(|error| format!("the junction would not divide: {error:?}"))?;
        println!("    (the span receiver is blind here: no corpus in this process)");
        respond(&division);
    }

    // ---- ★ THE RETURN EDGE: absorb the production, re-seal ----
    println!("\n  THE RETURN — the body absorbs its OWN production and re-seals");
    let ridden = ecology
        .generate(PROMPTS[0], spec(), current()?, 8)
        .map_err(|error| format!("generation refused: {error:?}"))?;
    // The material returned is the body's own emission, rendered back as a passage. It is a
    // GENUINE return only because it crosses the seal below -- a private echo is not a return.
    let returned: String = ridden
        .outputs
        .iter()
        .map(|text| text.text.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    if returned.trim().is_empty() {
        return Err("the production was empty, so there is nothing to absorb".to_owned());
    }
    let before_passages = ecology.passage_population();
    let before_occurrences = ecology.lexical_occurrence_population();
    let before_receptors = ecology.route_receptor_population();
    let own = CausalLanguagePassage::new("eros/own-production", 99, returned.clone());
    ecology
        .absorb(&own, current()?, 8)
        .map_err(|error| format!("the body would not absorb its own production: {error:?}"))?;
    println!(
        "    absorbed {} octets of its own emission",
        returned.len()
    );
    println!(
        "    passages    {before_passages} -> {}",
        ecology.passage_population()
    );
    println!(
        "    occurrences {before_occurrences} -> {}",
        ecology.lexical_occurrence_population()
    );
    println!(
        "    receptors   {before_receptors} -> {}",
        ecology.route_receptor_population()
    );
    if ecology.passage_population() == before_passages {
        return Err("the absorb moved nothing: the body is frozen".to_owned());
    }
    // A repeated identity must refuse. Absorbing the same material twice is a different claim.
    if ecology.absorb(&own, current()?, 8).is_ok() {
        return Err("THE CONTROL FAILED: a repeated passage identity absorbed twice".to_owned());
    }
    println!("    a repeated passage identity REFUSED, as it must");

    let changed = ecology
        .encode_native_bytes()
        .map_err(|error| format!("the changed body would not re-seal: {error:?}"))?;
    let out = PathBuf::from("output/eros-language-rest");
    let changed_path = out.join("conditioned-language-after-return.erosrest");
    let changed_rest = ErosRest::seal(
        LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1))),
        Vec::new(),
        vec![OrganRest {
            organ: LANGUAGE_ORGAN.to_owned(),
            bytes: changed,
        }],
    )
    .map_err(|error| format!("the changed whole body would not seal: {error:?}"))?;
    let octets = changed_rest
        .encode_native_bytes()
        .map_err(|error| format!("{error:?}"))?;
    std::fs::write(&changed_path, &octets)
        .map_err(|error| format!("{}: {error}", changed_path.display()))?;
    println!(
        "    re-sealed   {} octets -> {}",
        octets.len(),
        changed_path.display()
    );
    println!("    The changed body is on disk. A later process rides it, or nothing rode.");

    println!("\n  ★ DOES A LATER CURRENT RIDE THE CHANGE?");
    println!("  Two further processes, each given ONE rest path and nothing else: the body as it");
    println!("  stood before the return, and the body after it. Same prompt, same law. If the two");
    println!("  productions are identical, the absorb changed nothing later current rides, and that");
    println!("  is the finding rather than a thing to hide.\n");
    let self_path = std::env::current_exe().map_err(|error| format!("current_exe: {error}"))?;
    for (label, rest) in [("BEFORE the return", &path), ("AFTER the return", &changed_path)] {
        println!("  --- {label} ---");
        let status = std::process::Command::new(&self_path)
            .arg("--ride")
            .arg(rest)
            .status()
            .map_err(|error| format!("could not launch the riding process: {error}"))?;
        if !status.success() {
            return Err(format!("the riding process refused for {label}"));
        }
    }

    println!("\n  THE ABSENT-MORPHOLOGY CONTROL");
    let control = ecology
        .generate(CONTROL_PROMPT, spec(), current()?, 8)
        .map_err(|error| format!("the control refused outright: {error:?}"))?;
    report(CONTROL_PROMPT, &control);
    // **The population is never empty; the SURFACES can be.** An earlier form of this control
    // tested `outputs.is_empty()` and reported a fabrication when the body returned one member
    // carrying the empty surface. That was the control misreading the return, not the body
    // fabricating: a member with nothing on it is the honest shape, because a population that
    // vanishes cannot say whether it was refused or never posed.
    let fabricated: Vec<&str> = control
        .outputs
        .iter()
        .map(|text| text.text.as_str())
        .filter(|surface| !surface.trim().is_empty())
        .collect();
    if fabricated.is_empty() {
        println!("    AS REQUIRED: {} member(s) returned and every surface is EMPTY. Material the",
            control.outputs.len());
        println!("    body never received emits nothing rather than fabricating.");
        println!("    (0 sources were recruited, so nothing conducted -- the empty surface is the");
        println!("     population saying so, not a vanished population.)");
    } else {
        println!("    THE CONTROL FIRED: {} non-empty surface(s) from words the corpus does not",
            fabricated.len());
        println!("    carry. That is a finding and it is reported rather than suppressed:");
        for surface in fabricated.iter().take(8) {
            println!("      -> {surface:?}");
        }
    }
    Ok(())
}
