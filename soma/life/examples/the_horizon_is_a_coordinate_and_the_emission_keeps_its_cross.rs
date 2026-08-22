//! **The horizon gate, and what the emission does without it — a corpus diagnostic.**
//!
//! ```text
//! cargo run --release -p life --example the_horizon_is_a_coordinate_and_the_emission_keeps_its_cross
//! ```
//!
//! # What this is, and what it is NOT
//!
//! **It is not production and it is not a head.** An earlier form of this driver claimed to be
//! both. It joined `RatioFamily` and `SectionModulus` to suffix-branch multiplicities and
//! `clifford::Arrow` to route-feature indicator vectors, admitted sites by the arrow's hand — a
//! governor — and declared its uttered answer by taking the lexicographically first surface out of
//! a `BTreeMap`. An external adjudication convicted all four on 2026-08-18 and
//! [`blueprint/THE_MAP_IS_MATERIAL_THE_HEAD_IS_A_CONTACT_AND_THE_INSTANCE_RESUMES.md`](../../../blueprint/THE_MAP_IS_MATERIAL_THE_HEAD_IS_A_CONTACT_AND_THE_INSTANCE_RESUMES.md)
//! supersedes that plan. The organs are exact and they stand; the material they were handed was
//! wrong, and the exponentiated ratio's real material is an exact bracket population over a
//! deposited map, not a count of how often one word followed another.
//!
//! **What survives is one measured finding about this emission**, and it is worth keeping:
//!
//! > The emission was not copying because it could not compose. It was copying because
//! > `soma/life/src/causal_language.rs`'s greatest-horizon `retain` keeps, at every step, exactly
//! > the continuations attested by the longest matching corpus span — and keeps exactly one.
//!
//! This driver runs both branching laws over prompts drawn from the material by a declared rule and
//! puts every emitted surface to the window test.
//!
//! # The tautology this measures around
//!
//! **A two-token emission is a contiguous span by construction.** Both tokens come out of a junction
//! whose matched horizon is at least one, so the second is attested immediately after the first
//! somewhere in the corpus, so the pair is a corpus bigram, so it is a window. Nothing at depth two
//! can ever be composed, which is why the sweep runs at three.
//!
//! # Scope, carried with every figure
//!
//! A candidate is a contiguous span when some passage of **the declared material** contains its
//! token sequence as a window. That certifies *not a span of this material*. It does not certify
//! *absent from a corpus that was not supplied*.

use std::fs;
use std::path::{Path, PathBuf};

use body::num::Cog;
use life::causal_language::{
    lexical_tokens, render_tokens, BranchingLaw, CausalLanguageEcology, CausalLanguageGeneration,
    CausalLanguageGenerationSpec, CausalLanguagePassage, ContinuationReading, ContinuationReceiver,
};
use life::presentation_quotient::{PresentationMaterial, SpanIndex};
use soma_abi::active::ActionCurrent;

/// The aperture the sweep runs at. Three is the shallowest depth at which the window test is not a
/// tautology.
const SWEEP_APERTURE: usize = 3;

/// One declared corpus: where its material is, which extension it admits, and how many files.
struct DeclaredCorpus {
    name: &'static str,
    roots: Vec<PathBuf>,
    extension: &'static str,
    passages: usize,
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("an action current")
}

fn gather(root: &Path, extension: &str, into: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    let mut ordered: Vec<PathBuf> = entries
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect();
    ordered.sort();
    for path in ordered {
        if path.is_dir() {
            gather(&path, extension, into);
        } else if path.extension().and_then(|carried| carried.to_str()) == Some(extension) {
            into.push(path);
        }
    }
}

fn load(corpus: &DeclaredCorpus) -> Vec<CausalLanguagePassage> {
    let mut paths = Vec::new();
    for root in &corpus.roots {
        gather(root, corpus.extension, &mut paths);
    }
    paths.truncate(corpus.passages);
    paths
        .iter()
        .enumerate()
        .filter_map(|(at, path)| {
            let text = fs::read_to_string(path).ok()?;
            if text.trim().is_empty() {
                return None;
            }
            let identity = path
                .file_stem()
                .and_then(|stem| stem.to_str())
                .unwrap_or("unnamed")
                .to_owned();
            Some(CausalLanguagePassage::new(
                identity,
                u64::try_from(at + 1).unwrap_or(1),
                text,
            ))
        })
        .collect()
}

/// Prompts drawn from the material by one declared rule, spread across passages so the sweep is not
/// one passage's property: runs of `extent` tokens every member of which is word-shaped.
///
/// **This is a presentation rule on the asking site, not a constituency rule on the material.** It
/// decides which prompts this driver asks and decides nothing about what the machine may found. A
/// prompt ending on a delimiter opens a junction the size of the vocabulary, which is a property of
/// the prompt rather than of the law under test.
fn prompts_from_material(
    passages: &[CausalLanguagePassage],
    extent: usize,
    wanted: usize,
) -> Vec<String> {
    let word =
        |token: &String| token.chars().count() >= 3 && token.chars().all(char::is_alphabetic);
    let mut found: Vec<String> = Vec::new();
    for passage in passages {
        let tokens = lexical_tokens(&passage.text);
        if tokens.len() < extent {
            continue;
        }
        let mut taken_here = 0;
        for window in tokens.windows(extent) {
            if taken_here >= 2 || found.len() >= wanted {
                break;
            }
            if window.iter().all(word) {
                let prompt = render_tokens(window.iter().map(String::as_str));
                if !found.contains(&prompt) {
                    found.push(prompt);
                    taken_here += 1;
                }
            }
        }
        if found.len() >= wanted {
            break;
        }
    }
    found
}

fn report_junction(reading: &ContinuationReading, receiver: &str) {
    println!(
        "    receiver {receiver:<26} members {:>4}   greatest horizon {:>3}   \
         the gate would keep {:>4} and withhold {:>4}",
        reading.members.len(),
        reading.greatest_horizon,
        reading.gate_would_keep,
        reading.gate_would_withhold
    );
    println!(
        "      cocycle holds {:?}   flat {}   collapsed onto one fibre {}",
        reading.cocycle_holds, reading.flat, reading.collapsed_onto_one_fibre
    );
    for member in reading.members.iter().take(5) {
        let profile: Vec<String> = member
            .horizon_profile
            .iter()
            .map(|(horizon, multiplicity)| format!("{horizon}:{multiplicity}"))
            .collect();
        println!(
            "      {:<22} horizon {:>3}  multiplicity {:>6}  gate keeps {:<5}  profile {}",
            member.token,
            member.horizon,
            member.multiplicity,
            member.gate_would_keep,
            profile.join(" ")
        );
    }
    if reading.members.len() > 5 {
        println!(
            "      ... {} further members, none dropped",
            reading.members.len() - 5
        );
    }
}

fn span_rate(
    generation: &CausalLanguageGeneration,
    material: &PresentationMaterial,
    index: &SpanIndex,
) -> (usize, usize) {
    let candidates = generation.presented_candidates();
    let spans = candidates
        .iter()
        .filter(|candidate| {
            index
                .is_contiguous_span(&candidate.tokens)
                .unwrap_or_else(|| material.is_contiguous_span(&candidate.tokens))
        })
        .count();
    (spans, candidates.len())
}

fn run(corpus: &DeclaredCorpus) {
    println!("\n================================================================");
    println!("CORPUS  {}", corpus.name);
    println!("================================================================");
    let passages = load(corpus);
    if passages.len() < 2 {
        println!(
            "  the declared material is not on this disk; skipped, and the skip is the return"
        );
        return;
    }
    let octets: usize = passages.iter().map(|passage| passage.text.len()).sum();
    println!(
        "  {} passages, {octets} octets, extension .{}",
        passages.len(),
        corpus.extension
    );

    let ecology = match CausalLanguageEcology::condition(&passages, action(), 4) {
        Ok(ecology) => ecology,
        Err(error) => {
            println!("  conditioning refused: {error:?}");
            return;
        }
    };
    println!(
        "  conditioned: {} lexical occurrences, {} route receptors, {} route relations",
        ecology.lexical_occurrence_population(),
        ecology.route_receptor_population(),
        ecology.route_relation_population()
    );

    let material = ecology.presentation_material(&passages);
    let index = material.span_index(8);
    println!(
        "  window index: {} distinct windows up to length {}, held to the reference scan by \
         `the_span_index_agrees_with_the_reference_scan`",
        index.population(),
        index.longest()
    );

    let prompt = prompts_from_material(&passages, 5, 1)
        .into_iter()
        .next()
        .unwrap_or_default();
    println!("  one prompt, read off the material and not authored:\n    {prompt:?}");

    println!("\n  THE JUNCTION, READ — a diagnostic, and it decides nothing");
    for (receiver, name) in [
        (
            ContinuationReceiver::MostSpecificAttestation,
            "most-specific-attestation",
        ),
        (
            ContinuationReceiver::BroadestAttestation,
            "broadest-attestation",
        ),
    ] {
        match ecology.read_junction_from_prompt(&prompt, receiver) {
            Ok(reading) => report_junction(&reading, name),
            Err(error) => println!("    receiver {name}: refused {error:?}"),
        }
    }

    println!("\n  THE TWO BRANCHING LAWS, AND THE TEXT");
    for aperture in [2usize, 3] {
        println!("\n  ---- aperture {aperture} tokens ----");
        for (law, law_name) in [
            (BranchingLaw::GreatestHorizonGate, "greatest-horizon-gate"),
            (BranchingLaw::CompleteJunction, "complete-junction"),
        ] {
            let spec = CausalLanguageGenerationSpec {
                maximum_generated_tokens: aperture,
                stop_at_sentence_boundary: false,
                branching_law: law,
                continuation_receiver: ContinuationReceiver::MostSpecificAttestation,
            };
            let generation = match ecology.generate(&prompt, spec, action(), 4) {
                Ok(generation) => generation,
                Err(error) => {
                    println!("    {law_name}: refused {error:?}");
                    continue;
                }
            };
            let (spans, total) = span_rate(&generation, &material, &index);
            println!(
                "    {law_name:<24} surfaces {:>6}   contiguous spans {:>6}   composed {:>6}",
                total,
                spans,
                total.saturating_sub(spans)
            );

            // THE ARTIFACT. A declared reading of the population; nothing is dropped, and the whole
            // extent is stated beside it.
            let candidates = generation.presented_candidates();
            let word_shaped: Vec<&life::presentation_quotient::PresentedCandidate> = candidates
                .iter()
                .filter(|candidate| {
                    candidate.tokens.iter().all(|token| {
                        token.chars().count() >= 2 && token.chars().all(char::is_alphabetic)
                    })
                })
                .collect();
            println!(
                "      of the {} surfaces, {} have every token word-shaped; verbatim:",
                candidates.len(),
                word_shaped.len()
            );
            for candidate in word_shaped.iter().take(6) {
                let composed = !index
                    .is_contiguous_span(&candidate.tokens)
                    .unwrap_or_else(|| material.is_contiguous_span(&candidate.tokens));
                println!(
                    "        [{}] {:?}",
                    if composed { "COMPOSED" } else { "span    " },
                    candidate.identity
                );
            }
        }
    }

    println!("\n  THE FINDING, AS A RATE RATHER THAN A SAMPLE OF ONE");
    let sweep_prompts = prompts_from_material(&passages, 5, 8);
    println!(
        "    {} prompts swept, aperture {SWEEP_APERTURE}",
        sweep_prompts.len()
    );
    let (mut gate_spans, mut gate_total) = (0usize, 0usize);
    let (mut complete_spans, mut complete_total) = (0usize, 0usize);
    let mut refusals = 0usize;
    for swept in &sweep_prompts {
        for (law, is_gate) in [
            (BranchingLaw::GreatestHorizonGate, true),
            (BranchingLaw::CompleteJunction, false),
        ] {
            let spec = CausalLanguageGenerationSpec {
                maximum_generated_tokens: SWEEP_APERTURE,
                stop_at_sentence_boundary: false,
                branching_law: law,
                continuation_receiver: ContinuationReceiver::MostSpecificAttestation,
            };
            match ecology.generate(swept, spec, action(), 4) {
                Ok(generation) => {
                    let (spans, total) = span_rate(&generation, &material, &index);
                    if is_gate {
                        gate_spans += spans;
                        gate_total += total;
                    } else {
                        complete_spans += spans;
                        complete_total += total;
                    }
                }
                Err(_) => refusals += 1,
            }
        }
    }
    println!(
        "    greatest-horizon-gate  {gate_spans} of {gate_total} surfaces are contiguous spans"
    );
    println!(
        "    complete-junction      {complete_spans} of {complete_total} surfaces are contiguous \
         spans"
    );
    println!("    prompts the ecology refused: {refusals}");
    let gate_more_often = gate_total > 0
        && complete_total > 0
        && gate_spans * complete_total > complete_spans * gate_total;
    println!(
        "    VERDICT: the gate's outputs are more often spans than the complete junction's — {}",
        if gate_more_often {
            "TRUE on this material"
        } else {
            "FALSE on this material, so the filter was not the mechanism"
        }
    );
}

fn main() {
    println!("THE HORIZON GATE, AND WHAT THE EMISSION DOES WITHOUT IT");
    println!(
        "\nThis is a corpus diagnostic. It is not production, it is not a head, and it forms no\n\
         ratio: see the module header for what was superseded and why."
    );

    let corpora = [
        DeclaredCorpus {
            name: "mathematics — the registered objects under papers/source/mathematics",
            roots: vec![
                PathBuf::from("papers/source/mathematics/theorems"),
                PathBuf::from("papers/source/mathematics/definitions"),
                PathBuf::from("papers/source/mathematics/lemmas"),
            ],
            extension: "typ",
            passages: 12,
        },
        DeclaredCorpus {
            name: "code — exact projective geometry over BigRational",
            roots: vec![PathBuf::from("crates/relational-geometry/src")],
            extension: "rs",
            passages: 12,
        },
    ];

    for corpus in &corpora {
        run(corpus);
    }

    println!("\n================================================================");
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("================================================================");
    println!(
        "  The window test ran against the declared material only. No exterior adjudicator was\n\
         consulted on any codec. The complete junction branches everything the recruited sources\n\
         attest and forms no ratio; the junction reading above is a diagnostic and decides nothing."
    );
}
