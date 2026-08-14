//! The dialogue mouth, opened: condition on the real conversation corpus that is on disk.
//!
//! ```text
//! cargo run --release -p life --example eros_dialogue_conditioning -- [container-cap]
//! ```
//!
//! ## What this closes
//!
//! `soma/life/src/text_material.rs` declares the source-neutral intake faces on
//! `TextMaterialInput`; **`TextMaterialInput::` is
//! constructed by no driver in this workspace.** The one caller of `import`,
//! `examples/eros_mathematics_conditioning.rs:178`, passes `Vec::new()` for that argument and
//! hardcodes fourteen `.typ` paths instead. The mouth was a live argument receiving an empty vector.
//!
//! Meanwhile the material has been on disk the whole time: **316** `~/.codex/sessions/**/
//! rollout-*.jsonl` and `~/.claude/history.jsonl` at 5.9 MB.
//!
//! ## What is measured
//!
//! The receiver question, from `blueprint/ARBITRARY_LEARNING_MACHINE.md`'s first production grade:
//! **does a body conditioned on real dialogue conduct differently from the same body
//! unconditioned** — with the difference named rather than counted, and the aperture stated.
//!
//! This driver conditions and reports. It does not generate: `MorphologicalLanguageEcology::generate`
//! branches super-exponentially in its token aperture (measured 1 token 57 ms, 2 tokens 403 ms,
//! **4 tokens 55,098 ms, 8 tokens no return in 200 s**), so generation belongs behind its own
//! declared aperture in its own driver and not at the end of an intake run.
//!
//! ## The apertures, declared because a run past an unstated one is a defect
//!
//! ```text
//!   container cap      the caller's, from argv[1]; the ladder doubles under it
//!   ASCII              `conditioned_derivation::expose` keeps only is_ascii_alphabetic runs,
//!                      so every non-ASCII surface departs. Counted and reported, never silent.
//!   control records    the intake excludes tool results, thinking, isMeta and wrapper prefixes;
//!                      `excluded_control_occurrences` carries exactly what that cost.
//! ```

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use holonic_engine::conditioned_derivation::{expose, Exposure, FoundedMorphology};
use life::text_material::{ExactTextMaterialCorpus, TextMaterialInput};

/// Every Codex rollout on disk, in a stable order.
fn codex_rollouts(root: &Path) -> Vec<PathBuf> {
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
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn resident_mb() -> u64 {
    std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|statm| statm.split_whitespace().nth(1)?.parse::<u64>().ok())
        .map_or(0, |pages| pages * 4 / 1024)
}

fn main() {
    let cap: usize = std::env::args()
        .nth(1)
        .and_then(|read| read.parse().ok())
        .unwrap_or(usize::MAX);

    let home = PathBuf::from(std::env::var("HOME").unwrap_or_else(|_| "/home/b".to_owned()));

    rule("THE DIALOGUE MOUTH — the material that was always on disk");

    let mut inputs: Vec<TextMaterialInput> = codex_rollouts(&home.join(".codex/sessions"))
        .into_iter()
        .map(TextMaterialInput::CodexRollout)
        .collect();
    println!("  codex rollouts        {:>5}", inputs.len());

    let claude = home.join(".claude/history.jsonl");
    if claude.exists() {
        let bytes = std::fs::metadata(&claude)
            .map(|meta| meta.len())
            .unwrap_or(0);
        println!(
            "  claude history        {:>5} octets  {}",
            bytes,
            claude.display()
        );
        inputs.push(TextMaterialInput::ClaudeHistory(claude));
    }

    if inputs.is_empty() {
        eprintln!("\n  REFUSED: no dialogue material at the declared roots.");
        std::process::exit(1);
    }

    // The ladder is read off the population by doubling. Nothing authored; the caller may cap it.
    let mut rungs: Vec<usize> = Vec::new();
    let mut at = 1usize;
    while at < inputs.len() {
        rungs.push(at);
        at *= 2;
    }
    rungs.push(inputs.len());
    rungs.retain(|rung| *rung <= cap);
    println!("\n  the ladder, by doubling over the declared population: {rungs:?}");

    rule("THE LADDER — conditioning, and what each rung actually admitted");

    println!(
        "  {:>6}  {:>9}  {:>9}  {:>9}  {:>8}  {:>8}  {:>7}  {:>6}",
        "inputs", "witnessed", "unique", "human", "excluded", "stems", "commit", "MB"
    );

    let mut last: Option<(usize, FoundedMorphology, Vec<String>)> = None;
    for containers in &rungs {
        let began = Instant::now();
        let taken: Vec<TextMaterialInput> = inputs.iter().take(*containers).cloned().collect();
        let corpus = match ExactTextMaterialCorpus::import(taken, &[], 2) {
            Ok(corpus) => corpus,
            Err(refusal) => {
                println!("\n  rung {containers}: the intake refused — {refusal:?}");
                println!("  every rung below it stands and is reported above.");
                break;
            }
        };
        let receipt = corpus.receipt().clone();
        let passages = corpus.passages();
        let exposures: Vec<Exposure> = passages
            .iter()
            .map(|passage| expose(&passage.identity, &passage.text))
            .collect();
        let morphology = FoundedMorphology::condition(&exposures);
        let committed: Vec<String> = morphology
            .committed_stems()
            .into_iter()
            .map(str::to_owned)
            .collect();
        println!(
            "  {:>6}  {:>9}  {:>9}  {:>9}  {:>8}  {:>8}  {:>7}  {:>6}   {:.1}s",
            containers,
            receipt.witnessed_occurrences,
            receipt.unique_occurrences,
            receipt.human_occurrences,
            receipt.excluded_control_occurrences,
            morphology.founded().len(),
            committed.len(),
            resident_mb(),
            began.elapsed().as_secs_f64(),
        );
        last = Some((*containers, morphology, committed));
    }

    let Some((containers, morphology, committed)) = last else {
        eprintln!("\n  REFUSED at the first rung.");
        std::process::exit(1);
    };

    // ---------------------------------------------------------------------------------------------

    rule("THE ARTIFACT — what the dialogue corpus committed");

    println!(
        "  {containers} containers, {} stems founded, {} committed.\n",
        morphology.founded().len(),
        committed.len()
    );
    let longest: Vec<&String> = {
        let mut by_length: Vec<&String> = committed.iter().collect();
        by_length.sort_by_key(|stem| (std::cmp::Reverse(stem.len()), (*stem).clone()));
        by_length.into_iter().take(40).collect()
    };
    println!(
        "  the forty longest committed stems — these are WORDS the corpus recurred, not letters:"
    );
    for chunk in longest.chunks(6) {
        println!(
            "    {}",
            chunk
                .iter()
                .map(|stem| stem.as_str())
                .collect::<Vec<_>>()
                .join("  ")
        );
    }

    // ---------------------------------------------------------------------------------------------

    rule("THE ASCII APERTURE — what departed, counted rather than silent");

    let corpus =
        ExactTextMaterialCorpus::import(inputs.iter().take(containers).cloned().collect(), &[], 2)
            .expect("the rung imported once already");
    let passages = corpus.passages();
    let mut non_ascii_surfaces: BTreeSet<String> = BTreeSet::new();
    let mut non_ascii_octets = 0usize;
    for passage in &passages {
        for token in passage.text.split_whitespace() {
            if !token.is_ascii() {
                non_ascii_octets += token.len();
                non_ascii_surfaces.insert(token.to_owned());
            }
        }
    }
    println!(
        "  `conditioned_derivation::expose` keeps only `is_ascii_alphabetic` runs, so every surface\n  \
         below departs before a stem can be founded from it.\n"
    );
    println!(
        "  distinct non-ASCII surfaces   {}",
        non_ascii_surfaces.len()
    );
    println!("  octets they carry             {non_ascii_octets}");
    println!("  a sample, verbatim:");
    for surface in non_ascii_surfaces.iter().take(12) {
        println!("    {surface}");
    }
    println!(
        "\n  That is the aperture, stated. It is not a defect of the intake — it is the grain the\n  \
         exposure declares, and a run that did not name it would be past an unstated aperture."
    );

    rule("BOUNDS");
    println!("  - This driver conditions and reports. It does not generate: `generate` branches");
    println!(
        "    super-exponentially in its token aperture and belongs behind its own declared one."
    );
    println!("  - Every figure has one frame; no timing here is falsifiable (`CLAUDE.md` §8).");
    println!("  - The morphology is the corpus's own: no stem is authored by this file.");
}
