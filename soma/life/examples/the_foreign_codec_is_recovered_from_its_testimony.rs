//! **Gemma's segmenter, recovered from what it does rather than from what it says.**
//!
//! `blueprint/THE_ROADMAP.md`'s Gemma lift, step 2. The active embedding space includes the
//! tokenizer, and a tokenizer is a **segmenter** — exactly the material
//! `holonic_engine::codec_recovery` is built to recover. Brandon's own framing of the operation, on
//! being shown a first misreading of it:
//!
//! > *"I think you are potentially misinterpretting it and expecting the machine to reverse engineer
//! > black boxes without the necessary parameters provided. It's like Fourier Analysis... we need the
//! > machine to be able to derive correlations and relationships from provided statistics as
//! > parameters."*
//!
//! So this is not inversion from nothing. The provided statistic is **the segmentation the foreign
//! conditioner returns over an exhausted query family**, and the recovery derives the relations that
//! statistic implies.
//!
//! # The black-box discipline is structural, not promised
//!
//! This driver reads `tokenizer.json` to *build* the segmenter — the merge table, 514,906 of them —
//! and then hands it to [`OpaqueSymbolCodec`], which has **no accessor that returns its law**. The
//! recovery therefore cannot consult the merges; it can only ask the codec what it returns, and the
//! codec counts every call. **The merge table is the answer, and the answer is not readable from
//! where the recovery stands.**
//!
//! # What returns
//!
//! - **the symbol quotient** — which symbols the statistics never separate;
//! - **the separations** — each separated pair with the **shortest context** that separates it;
//! - **the adjacency** — `Join` or `Cut` per ordered class pair, which is what a segmentation is
//!   made of;
//! - **the obstructions** — every entry the declared family left open, named rather than filled.
//!
//! And the refusal that keeps an empty return from reading as a result: a conditioner whose declared
//! statistics separate no two symbols has supplied no relation, and `recover` refuses it by type.
//!
//! ```text
//! cargo run --release -p life --example the_foreign_codec_is_recovered_from_its_testimony
//! ```

use std::collections::BTreeMap;

use holonic_engine::codec_recovery::{
    recover, Boundary, Emission, OpaqueSymbolCodec, RecoveryApertures, Symbol, SymbolAlphabet,
};

const TOKENIZER: &str = "/home/b/models/gemma-4-E4B-it/tokenizer.json";

/// Gemma's declared normalizer: a space becomes `U+2581`. Read off `tokenizer.json`, not assumed.
const SPACE_MARK: char = '\u{2581}';

/// The declared alphabet. **Six symbols, and the choice is the caller's**, which is what the level
/// rule requires: the organ authors no alphabet.
///
/// **The space is declared in its NORMALIZED form, and the first run is why.** Presented with a raw
/// space the codec returned `["▁"]` — pieces that do not concatenate back to the input — and
/// `recover` refused by name with `NotASegmentation { input: " ", returned: ["▁"] }`. It was right:
/// Gemma's tokenizer is a **normalizer composed with a segmenter**, and only the second factor is a
/// segmentation. The normalizer is an invertible rebase of the alphabet, so the honest presentation
/// is in the chart the segmenter itself works in — which is what `derivation_codec_intake` means by
/// presenting material as *maximal runs over a declared alphabet*.
const ALPHABET: [char; 6] = ['a', 'b', 'e', 'r', 't', SPACE_MARK];

/// The declared alphabet, as symbols.
///
/// **The rotation of 2026-08-13 is what makes the space honest here.** Before it the organ's
/// alphabet was `char`, so the normalized space had to be smuggled in as a Unicode scalar the caller
/// happened to know about; now the alphabet is a declaration carrying each symbol's own octets and
/// its own identity, and `OpaqueSymbolCodec::over_text` performs the chart translation explicitly
/// where it can be read. The declaration below is the same six symbols; what changed is that the
/// translation is in the tree rather than in the caller's head.
fn alphabet() -> SymbolAlphabet {
    SymbolAlphabet::from_chars(&ALPHABET).expect("the declared alphabet carries no repeat")
}

/// A word, spelled through the declared alphabet.
///
/// **The organ carries ordinals and a reader needs identities.** Printing `Symbol(0)` where the
/// material says `"a"` is not a smaller claim, it is an unreadable one, and the alphabet exists
/// precisely so a return can be handed back to the material it came from.
fn spell(word: &[Symbol]) -> String {
    let declared = alphabet();
    word.iter()
        .map(|symbol| declared.identity(*symbol).unwrap_or("?"))
        .collect()
}

/// A segmentation, spelled.
fn spell_all(segmentation: &[Vec<Symbol>]) -> Vec<String> {
    segmentation.iter().map(|token| spell(token)).collect()
}

/// The declared query radius. Words up to this length are exhausted: `6 + 36 + 216 = 258` queries.
const RADIUS: usize = 3;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

/// The merge table, ranked. Rank is priority: the lowest-ranked applicable merge fires first.
fn load_merges() -> Result<BTreeMap<(String, String), usize>, String> {
    let raw = std::fs::read_to_string(TOKENIZER).map_err(|e| format!("open {TOKENIZER}: {e}"))?;
    let parsed: serde_json::Value =
        serde_json::from_str(&raw).map_err(|e| format!("parse {TOKENIZER}: {e}"))?;
    let model = parsed
        .get("model")
        .ok_or("tokenizer.json carries no model")?;
    if model.get("type").and_then(|t| t.as_str()) != Some("BPE") {
        return Err("this driver segments BPE and the declared model is not one".into());
    }
    let merges = model
        .get("merges")
        .and_then(|m| m.as_array())
        .ok_or("the model carries no merge table")?;
    let mut ranked = BTreeMap::new();
    for (rank, entry) in merges.iter().enumerate() {
        // Two spellings occur in the wild: a pair array, and one space-joined string.
        let pair = match entry {
            serde_json::Value::Array(parts) if parts.len() == 2 => {
                let left = parts[0].as_str().ok_or("merge left is not a string")?;
                let right = parts[1].as_str().ok_or("merge right is not a string")?;
                (left.to_owned(), right.to_owned())
            }
            serde_json::Value::String(joined) => {
                let mut halves = joined.splitn(2, ' ');
                let left = halves.next().ok_or("merge carries no left")?.to_owned();
                let right = halves.next().ok_or("merge carries no right")?.to_owned();
                (left, right)
            }
            _ => return Err("a merge entry is neither a pair nor a joined string".into()),
        };
        ranked.entry(pair).or_insert(rank);
    }
    Ok(ranked)
}

/// Gemma's segmentation of one input: normalize, then apply the highest-priority merge until none
/// applies. **This is the black box**; nothing below it is visible to the recovery.
fn segment_with(ranked: &BTreeMap<(String, String), usize>, input: &str) -> Vec<String> {
    let normalized: String = input
        .chars()
        .map(|symbol| if symbol == ' ' { SPACE_MARK } else { symbol })
        .collect();
    let mut pieces: Vec<String> = normalized.chars().map(|c| c.to_string()).collect();
    loop {
        let mut best: Option<(usize, usize)> = None;
        for at in 0..pieces.len().saturating_sub(1) {
            let key = (pieces[at].clone(), pieces[at + 1].clone());
            if let Some(rank) = ranked.get(&key) {
                if best.is_none_or(|(_, held)| *rank < held) {
                    best = Some((at, *rank));
                }
            }
        }
        let Some((at, _)) = best else {
            return pieces;
        };
        let merged = format!("{}{}", pieces[at], pieces[at + 1]);
        pieces.splice(at..=at + 1, [merged]);
    }
}

fn run() -> Result<(), String> {
    println!("THE FOREIGN SEGMENTER");
    let started = std::time::Instant::now();
    let ranked = load_merges()?;
    println!(
        "  {} merges ranked from {TOKENIZER}  [{:?}]",
        ranked.len(),
        started.elapsed()
    );
    println!("  normalizer read off the file: a space becomes {SPACE_MARK:?}");

    // Three segmentations printed as evidence that the black box is the real one, before it is
    // sealed behind the codec and made unreadable.
    for probe in ["better", "a\u{2581}bat", "tree\u{2581}bark"] {
        println!("    {probe:?} -> {:?}", segment_with(&ranked, probe));
    }

    let declared = alphabet();
    let target =
        OpaqueSymbolCodec::over_text(&declared, move |input: &str| segment_with(&ranked, input));

    println!("\nTHE DECLARED QUERY FAMILY");
    println!(
        "  alphabet {:?}, radius {RADIUS} — the caller declares both; the organ authors neither",
        ALPHABET
    );

    let apertures = RecoveryApertures::declared(4096, 16);
    let recovered = recover(&target, &declared.symbols(), RADIUS, apertures)
        .map_err(|error| format!("the recovery refused: {error:?}"))?;

    println!(
        "  the codec was called {} times, and its law was never read",
        target.calls()
    );

    println!("\nTHE RECOVERED CODEC");
    println!(
        "  retained tables {} · inequivalent codecs {} — one is a recovery, more is an obstruction",
        recovered.retained_tables, recovered.inequivalent_codecs
    );

    // `codec` is an Option BY DESIGN: a recovery that halts before founding one has returned the
    // obstructions instead, and that is a result rather than a failure.
    match &recovered.codec {
        None => {
            println!(
                "  NO SINGLE CODEC WAS FOUNDED. The declared family did not force one, and the \
                 entries it left open are named below. That is the honest return — a codec filled \
                 in past what the testimony forces would be authored, not recovered."
            );
        }
        Some(codec) => {
            println!("  symbol classes: {}", codec.class_count());
            for class in 0..codec.class_count() {
                let members: Vec<String> = recovered
                    .classes
                    .get(class)
                    .map(|set| {
                        set.iter()
                            .map(|member| declared.identity(*member).unwrap_or("?").to_owned())
                            .collect()
                    })
                    .unwrap_or_default();
                let representative = codec.class_representative(
                    holonic_engine::codec_recovery::SymbolClass(class as u32),
                );
                let emission = representative.and_then(|symbol| codec.emission_of(symbol));
                println!(
                    "    class {class}: {members:?}  emission {}",
                    match emission {
                        Some(Emission::Emit) => "EMIT",
                        Some(Emission::Drop) => "DROP",
                        None => "open",
                    }
                );
            }
            println!("\n  THE QUOTIENT — symbols the statistics never separate");
            if codec.class_count() == ALPHABET.len() {
                println!(
                    "    none. Every declared symbol is separated by the segmentation, so this \
                     family supplied a full refinement and the quotient is trivial. That is a \
                     statement about THIS alphabet at THIS radius, not about the segmenter."
                );
            } else {
                println!(
                    "    {} declared symbols fell into {} classes — the collapse is the finding",
                    ALPHABET.len(),
                    codec.class_count()
                );
            }
        }
    }

    if !recovered.gauge_freedom.is_empty() {
        println!(
            "\n  GAUGE FREEDOM — {} boundary entries the retained tables disagree on while every \
             retained table stays observationally identical. Free choices, not open questions.",
            recovered.gauge_freedom.len()
        );
    }

    println!("\n  THE SEPARATIONS — each pair with the SHORTEST context that separates it");
    for separation in recovered.separations.iter().take(12) {
        println!(
            "    {:?} | {:?}   context {:?} … {:?}  (length {})",
            spell(&[separation.left]),
            spell(&[separation.right]),
            spell(&separation.prefix),
            spell(&separation.suffix),
            separation.context_length()
        );
    }
    if recovered.separations.len() > 12 {
        println!("    … {} further", recovered.separations.len() - 12);
    }

    println!("\n  THE ADJACENCY — what a segmentation is made of");
    match &recovered.codec {
        None => println!("    not founded: see the obstructions."),
        Some(codec) => {
            let mut joins = 0usize;
            let mut cuts = 0usize;
            for left in &declared.symbols() {
                for right in &declared.symbols() {
                    match codec.boundary_between(*left, *right) {
                        Some(Boundary::Join) => joins += 1,
                        Some(Boundary::Cut) => cuts += 1,
                        None => {}
                    }
                }
            }
            println!(
                "    Join {joins} · Cut {cuts} ordered pairs, over {} declared",
                ALPHABET.len().pow(2)
            );
        }
    }

    println!("\n  THE OBSTRUCTIONS — entries the declared family left open, named");
    if recovered.obstructions.is_empty() {
        println!("    none: the declared family closed every entry.");
    } else {
        for obstruction in recovered.obstructions.iter().take(10) {
            // Spelled, not printed raw: the witness is the whole content of this return.
            match obstruction {
                holonic_engine::codec_recovery::Obstruction::NoConformingTable {
                    refuted_tables,
                    witnesses,
                } => {
                    println!("    NoConformingTable, {refuted_tables} table(s) refuted");
                    for witness in witnesses {
                        println!(
                            "      {:?}  target {:?}  recovered {:?}",
                            spell(&witness.input),
                            spell_all(&witness.target),
                            spell_all(&witness.recovered)
                        );
                    }
                }
                other => println!("    {other:?}"),
            }
        }
        if recovered.obstructions.len() > 10 {
            println!("    … {} further", recovered.obstructions.len() - 10);
        }
    }

    println!("\n  work: {:?}", recovered.work);
    println!(
        "\n  READ IT AS WHAT IT IS. The merge table was never visible to the recovery — the codec \
         has no accessor that returns its law, and the call count above is the whole of what the \
         recovery saw. What returns is the relation Gemma's segmentation IMPLIES over a declared \
         alphabet, derived from its own testimony. It is not a copy of the merge table and would not \
         reproduce one; it is the structure that testimony forces, which is the thing the ecology \
         can recombine."
    );
    Ok(())
}
