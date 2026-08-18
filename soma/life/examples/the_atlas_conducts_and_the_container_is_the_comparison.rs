//! **What the atlas DOES with tokens, and how that compares to a transformer and to safetensors.**
//!
//! Brandon, 2026-08-18: *"I can't make use of those scalars, they do not tell me anything about what
//! the machine is doing with the tokens and what it makes it capable of during inference. Review the
//! actual holonic structures that you can attain from further analysis/probing… I want you to
//! compare it to transformers and safetensors in general."*
//!
//! Block counts are a face. This driver returns the **conduct**: what happens to each token as it
//! crosses the material, what structure the material itself has, and what the two containers each
//! hold.
//!
//! Run:
//! ```text
//!   cargo run --release -p life --example the_atlas_conducts_and_the_container_is_the_comparison
//! ```

use std::collections::BTreeMap;

use body::num::Cog;
use life::causal_language::{
    fiber_bytes, lexical_tokens, CausalLanguageEcology, CausalLanguagePassage,
};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";
const MAP_DIR: &str = "/home/b/models/gemma-4-E4B-it";

/// The prompts whose conduct is traced. Short, so the whole trace is readable.
const TRACED: &[&str] = &[
    "the receiver is a declared",
    "a compression is a codec pivot",
    "the quantum wobbleflux transports",
];

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

/// ---------------------------------------------------------------------------------------------
/// PART ONE — THE CONDUCT
///
/// Token by token, what the material does with the current. This is the exact analogue of reading
/// an attention pattern, and every quantity is a caused fact rather than a learned weight.
/// ---------------------------------------------------------------------------------------------
fn trace(atlas: &ExactSuffixEcology, prompt: &str) -> Result<(), String> {
    let tokens = lexical_tokens(prompt);
    let germs = life::causal_language::token_germs_public(&tokens)
        .map_err(|error| format!("{error:?}"))?;
    println!("  PROMPT {prompt:?}  ->  {} tokens", tokens.len());
    println!(
        "    {:<14} {:>6} {:>6} {:>9} {:>7} {:>8}  {}",
        "token", "class", "depth", "standing", "breadth", "interval", "passage"
    );

    let mut current = life::suffix_ecology::ExactSuffixCurrent::root_public();
    for (token, germ) in tokens.iter().zip(germs.iter()) {
        let before = current.matched_length();
        current = atlas
            .carry(current, germ)
            .map_err(|error| format!("{error:?}"))?;
        let after = current.matched_length();
        let state = current.state();
        // Forward when the depth advanced by exactly one; otherwise the leader ARCED down a suffix
        // link because no forward transition existed, and the drop is what the material could not
        // carry through that junction.
        let passage = if after == before + 1 {
            "forward".to_owned()
        } else if after == 0 {
            "ARC to root — nothing of this context survived".to_owned()
        } else {
            format!("ARC — lost {} of context", before + 1 - after)
        };
        let (minimum, maximum) = atlas.class_interval(state).unwrap_or((0, 0));
        println!(
            "    {:<14} {:>6} {:>6} {:>9} {:>7} {:>4}..{:<3}  {passage}",
            truncate(token, 14),
            state,
            after,
            atlas.standing_at(state).unwrap_or(0),
            atlas.junction_breadth(state),
            minimum,
            maximum
        );
    }

    // The junction the prompt lands on, read at EVERY scale at once. `emanate` walks the whole
    // suffix-link chain, so this is not one reading -- it is the same current read through every
    // nested context, with each continuation carrying the depths that support it.
    let emanation = atlas
        .emanate_current(current)
        .map_err(|error| format!("{error:?}"))?;
    println!(
        "    landed: {} nested contexts, {} continuations, longest match {}",
        emanation.contexts().len(),
        emanation.branches().len(),
        emanation.longest_matched_length()
    );
    println!("    THE SUPPORT PROFILE — each continuation, and the depths that carry it:");
    let mut shown = 0usize;
    for branch in emanation.branches() {
        if shown >= 8 {
            println!(
                "      … {} more continuations, all retained",
                emanation.branches().len() - shown
            );
            break;
        }
        let token = fiber_bytes(branch.germ().identity()).unwrap_or_else(|_| "?".to_owned());
        let mut depths: Vec<String> = branch
            .supports()
            .iter()
            .map(|support| {
                format!(
                    "d{}x{}",
                    support.matched_length(),
                    support.recurrence_multiplicity()
                )
            })
            .collect();
        depths.sort();
        println!("      {:<16} {}", truncate(&token, 16), depths.join(" "));
        shown += 1;
    }
    if emanation.branches().is_empty() {
        println!("      none — the material offers no continuation from here");
    }
    println!();
    Ok(())
}

fn truncate(text: &str, at: usize) -> String {
    let cleaned: String = text.chars().filter(|c| !c.is_control()).collect();
    if cleaned.chars().count() <= at {
        cleaned
    } else {
        cleaned.chars().take(at.saturating_sub(1)).chain("…".chars()).collect()
    }
}

/// ---------------------------------------------------------------------------------------------
/// PART TWO — WHAT THE MATERIAL ITSELF IS
///
/// A census over every class. None of this depends on any prompt.
/// ---------------------------------------------------------------------------------------------
fn census(atlas: &ExactSuffixEcology) {
    let states = atlas.state_count();
    let mut breadth: BTreeMap<usize, usize> = BTreeMap::new();
    let mut interval_width: BTreeMap<usize, usize> = BTreeMap::new();
    let mut widest = (0usize, 0u32);
    let mut deepest = (0usize, 0u32);
    let mut forced = 0usize;
    let mut termini = 0usize;
    let mut forks = 0usize;
    for state in 0..states {
        let at = state as u32;
        let out = atlas.junction_breadth(at);
        *breadth.entry(out.min(8)).or_default() += 1;
        match out {
            0 => termini += 1,
            1 => forced += 1,
            _ => forks += 1,
        }
        if let Some((minimum, maximum)) = atlas.class_interval(at) {
            let width = maximum.saturating_sub(minimum) + 1;
            *interval_width.entry(width.min(8)).or_default() += 1;
            if width > widest.0 {
                widest = (width, at);
            }
            if maximum > deepest.0 {
                deepest = (maximum, at);
            }
        }
    }
    println!("  classes                      {states}");
    println!("  germ transitions             {}", atlas.material_transition_count());
    println!("  material occurrences         {}", atlas.material_occurrence_count());
    println!();
    println!("  JUNCTION BREADTH — where the material is decided and where it forks");
    println!("    termini      (breadth 0)   {termini}");
    println!("    FORCED       (breadth 1)   {forced}   <- exactly one continuation admitted:");
    println!("                                       nothing is decided here, no plurality to divide");
    println!("    forks        (breadth >1)  {forks}");
    for (out, count) in &breadth {
        if *out >= 2 {
            println!("      breadth {}{}          {count}", out, if *out == 8 { "+" } else { " " });
        }
    }
    println!();
    println!("  CLASS INTERVAL WIDTH — the tolerance each class carries");
    println!("    A class covers every substring length in [min, max] that shares its occurrence");
    println!("    set. Over that whole range no declared receiver can separate them, so the width");
    println!("    IS a tolerance — read off the tree, never set as a number.");
    for (width, count) in &interval_width {
        println!("    width {}{}                  {count}", width, if *width == 8 { "+" } else { " " });
    }
    println!("    widest interval            {} lengths, at class {}", widest.0, widest.1);
    println!("    longest class extent       {} tokens, at class {}", deepest.0, deepest.1);
}

/// ---------------------------------------------------------------------------------------------
/// PART THREE — THE TWO CONTAINERS
/// ---------------------------------------------------------------------------------------------
fn containers(atlas: &ExactSuffixEcology, sealed: usize) -> Result<(), String> {
    use holonic_engine::embedding_fiber::safetensors;
    let (_, header) = safetensors::read_header(MAP)?;
    let mut payload = 0u64;
    let mut dtypes: BTreeMap<String, usize> = BTreeMap::new();
    let mut two_dimensional = 0usize;
    for entry in header.map.values() {
        payload = payload.max(entry.end);
        *dtypes.entry(entry.dtype.clone()).or_default() += 1;
        if entry.shape.len() == 2 {
            two_dimensional += 1;
        }
    }
    println!("  THE SAFETENSORS CONTAINER  {MAP}");
    println!("    declared tensors           {}", header.map.len());
    println!("    payload octets             {payload}");
    println!("    dtypes                     {dtypes:?}");
    println!("    two-dimensional            {two_dimensional}");
    println!("    what a header row carries  name · dtype · shape · byte offsets");
    println!("    what it does NOT carry     how any tensor participates in any transport.");
    println!("                               The header is COORDINATES. The composition law lives");
    println!("                               in config.json plus the modelling code, outside the");
    println!("                               file. Hand someone this container with no architecture");
    println!("                               and they hold exact values that compose in no way.");

    let vocabulary = std::fs::metadata(format!("{MAP_DIR}/tokenizer.json"))
        .map(|meta| meta.len())
        .unwrap_or(0);
    println!("    the symbols                a row index reopens to a token ONLY through");
    println!("                               tokenizer.json, a separate {vocabulary}-octet artifact.");
    println!("                               Lose it and the rows address nothing.");
    println!();
    println!("  THE ATLAS CONTAINER  (one ErosRest organ)");
    println!("    sealed octets              {sealed}");
    println!("    classes                    {}", atlas.state_count());
    println!("    germ transitions           {}", atlas.material_transition_count());
    println!("    what the payload IS        the transport itself: classes, suffix links, the");
    println!("                               transitions between them, and the occurrence count of");
    println!("                               each class. There is no separate composition law,");
    println!("                               because the container is the composition law.");
    println!("    the symbols                a germ identity is a LENGTH-PREFIXED PACKING, not a");
    println!("                               digest, so `fiber_bytes` returns the token itself.");
    println!("                               No vocabulary file exists or is needed.");

    // Demonstrate the reopening rather than asserting it.
    let probe = lexical_tokens("receiver");
    let germs = life::causal_language::token_germs_public(&probe)
        .map_err(|error| format!("{error:?}"))?;
    if let Some(germ) = germs.first() {
        let back = fiber_bytes(germ.identity()).map_err(|error| format!("{error:?}"))?;
        println!("    demonstrated               \"receiver\" -> germ -> {back:?}");
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let sealed = ecology
        .encode_native_bytes()
        .map_err(|error| format!("{error:?}"))?
        .len();
    let atlas = ecology.global_suffix();

    println!("PART ONE — THE CONDUCT: what the material does with each token\n");
    println!("  class    = the transport class the current lands in (an occurrence set, one identity)");
    println!("  depth    = how far back the current is still coherent");
    println!("  standing = how much material stands behind that class");
    println!("  breadth  = how many germs continue out of it");
    println!("  interval = the substring lengths the class covers -- its tolerance\n");
    for prompt in TRACED {
        trace(atlas, prompt)?;
    }

    println!("PART TWO — WHAT THE MATERIAL ITSELF IS\n");
    census(atlas);

    println!("\nPART THREE — THE TWO CONTAINERS\n");
    containers(atlas, sealed)?;
    Ok(())
}
