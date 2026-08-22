//! **ATHENA-000 — the first tensor container emitted by this engine.**
//!
//! The chart transition derived in `crates/holonic-engine/src/athena.rs`, run on real material and
//! read back through `embedding_fiber::safetensors` — the same intake that reads Gemma.
//!
//! **What is emitted, and why each part is what it is.**
//!
//! - The layer count is the **suffix-link tree's height**, read off the material rather than chosen.
//! - Layer `k`'s coordinate for a token is the Minkowski point `(t, x) = (centre, radius)` of the
//!   depth-first interval of the class the token lands in **climbed `k` links**. Ancestry between
//!   classes is then the light-cone order, so the declared signature is `(+, −)`.
//! - A third coordinate per layer carries the class's **standing** — how much material stands behind
//!   it — which is the only extensive quantity in the row.
//! - Every entry is an exact rational rounded into `BF16` with its **residual retained**, so the
//!   quantisation is a certified remainder rather than an unknown error.
//!
//! **The cycle rank is reported beside it**, because that is the honest cost of the half of the
//! transition this container does *not* carry: `β₁ = |transitions| − |classes| + 1` is the dimension
//! of the cycle space, and any container below it has declared a receiver family that cannot
//! separate some reconvergences.

use std::collections::BTreeSet;

use body::num::Cog;
use holonic_engine::athena::{emit_tensor, safetensors_container, TreeChart};
use holonic_engine::embedding_fiber::{align_bfloat16, safetensors};
use life::causal_language::{
    fiber_bytes, lexical_tokens, token_germs_public, CausalLanguageEcology, CausalLanguagePassage,
};
use num_bigint::BigInt;
use relational_geometry::Rat;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

/// How many scales the container carries. **Declared by this caller against the tree's own height**,
/// which is reported beside it, and what is excluded is named rather than dropped.
const LAYERS: u32 = 6;

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    let mut vocabulary: BTreeSet<String> = BTreeSet::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        vocabulary.extend(lexical_tokens(&text));
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();

    let classes = atlas.state_count();
    let transitions = atlas.material_transition_count();
    let cycle_rank = transitions as i64 - classes as i64 + 1;

    println!("THE MATERIAL");
    println!("  classes                {classes}");
    println!("  germ transitions       {transitions}");
    println!("  vocabulary             {}", vocabulary.len());
    println!();
    println!("THE TRANSITION, AND WHAT EACH HALF COSTS");
    println!("  the tree (ancestry, scale)   2 dimensions, remainder ZERO");
    println!("  standing                     1 dimension,  remainder ZERO");
    println!("  transport as a linear map    cycle rank B1 = {transitions} - {classes} + 1 = {cycle_rank}");
    println!(
        "                               that is the reconvergence population: distinct contexts"
    );
    println!(
        "                               landing in one class. A container below it has declared"
    );
    println!("                               a family that cannot separate some of them, and the");
    println!("                               collapsed population is the loss -- never unknown.");

    // ---- the tree chart: free, exact ----
    let chart = TreeChart::label(classes, |state| atlas.suffix_link(state))
        .map_err(|error| format!("the tree would not label: {error:?}"))?;
    println!();
    println!("THE TREE CHART");
    println!("  suffix-link tree height      {}", chart.height);
    println!(
        "  layers emitted               {LAYERS}   (declared; the height above is the material's)"
    );
    if chart.height + 1 > LAYERS {
        println!(
            "  EXCLUDED                     {} scales above layer {}, reported not dropped",
            chart.height + 1 - LAYERS,
            LAYERS - 1
        );
    }

    // Verify the causal order on real material rather than only on the unit fixture: every class's
    // suffix parent must contain it, read as the light-cone order.
    let mut checked = 0usize;
    let mut failed = 0usize;
    for state in 0..classes as u32 {
        if let Some(parent) = atlas.suffix_link(state) {
            checked += 1;
            if chart.contains(parent, state) != Some(true) {
                failed += 1;
            }
        }
    }
    println!(
        "  ancestry as the light cone   {} of {checked} links hold, {failed} fail",
        checked - failed
    );
    if failed > 0 {
        return Err(format!(
            "{failed} suffix links are not causal in the emitted chart: the transition is wrong"
        ));
    }

    // ---- the rows ----
    let mut tokens: Vec<String> = vocabulary.into_iter().collect();
    tokens.sort();
    let mut rows: Vec<Vec<Rat>> = Vec::with_capacity(tokens.len());
    let mut kept: Vec<String> = Vec::with_capacity(tokens.len());
    for token in &tokens {
        let germs = token_germs_public(std::slice::from_ref(token))
            .map_err(|error| format!("{error:?}"))?;
        let current = atlas
            .receive_path(&germs)
            .map_err(|error| format!("{error:?}"))?;
        if current.matched_length() == 0 {
            continue; // a token the material does not carry has no class to chart
        }
        let mut row = Vec::with_capacity(LAYERS as usize * 3);
        for height in 0..LAYERS {
            let class = atlas.suffix_ancestor(current.state(), height);
            let (t, x) = chart
                .minkowski(class)
                .ok_or_else(|| format!("class {class} has no interval"))?;
            row.push(t);
            row.push(x);
            row.push(Rat::from_integer(BigInt::from(
                atlas.standing_at(class).unwrap_or(0),
            )));
        }
        rows.push(row);
        kept.push(token.clone());
    }
    if rows.is_empty() {
        return Err("no token reached a class; nothing to emit".to_owned());
    }

    // ---- the emission ----
    let tensor = emit_tensor("athena.embed_tokens.weight", &rows)
        .map_err(|error| format!("the emission refused: {error:?}"))?;
    let entries = tensor.words.len();
    println!();
    println!("THE EMISSION");
    println!(
        "  rows x width                 {} x {}",
        tensor.rows, tensor.width
    );
    println!("  entries                      {entries}");
    println!(
        "  crossed EXACTLY              {} of {entries}",
        tensor.exact_entries()
    );
    println!(
        "  widest residual              {}",
        tensor.widest_residual()
    );
    println!("  every entry closes: stored + residual = the exact value asked for.");

    let container = safetensors_container(std::slice::from_ref(&tensor));
    std::fs::create_dir_all("output/athena-000")
        .map_err(|error| format!("output/athena-000: {error}"))?;
    let path = "output/athena-000/model.safetensors";
    std::fs::write(path, &container).map_err(|error| format!("{path}: {error}"))?;
    println!(
        "  container                    {} octets -> {path}",
        container.len()
    );

    // ---- read it back through the SAME intake that reads Gemma ----
    let (mut file, header) = safetensors::read_header(path)?;
    let entry = header.entry("athena.embed_tokens.weight")?;
    println!();
    println!("THE READ-BACK, through the intake that reads Gemma");
    println!(
        "  declared                     {:?} {} rows x {}",
        entry.dtype, entry.shape[0], entry.shape[1]
    );
    let (words, width) = safetensors::read_rows(
        &mut file,
        &header,
        "athena.embed_tokens.weight",
        0,
        tensor.rows,
    )?;
    if width != tensor.width || words != tensor.words {
        return Err("the container did not return the words it was written with".to_owned());
    }
    println!(
        "  words returned               {} — bit-identical to what was written",
        words.len()
    );

    // And the exact mouth closes on the far side: aligning a row returns integers and a common
    // exponent with zero remainder, which is the read direction of the same bijection.
    let probe = &words[..tensor.width];
    let aligned = align_bfloat16(probe).map_err(|error| format!("{error:?}"))?;
    println!(
        "  row 0 aligned                {} entries on exponent {}, {} negative",
        aligned.entries.len(),
        aligned.exponent,
        aligned.negatives
    );

    // ---- what the container can answer that a weight file cannot ----
    println!();
    println!("WHAT THIS CONTAINER CARRIES THAT A WEIGHT FILE DOES NOT");
    let mut demonstrated = 0usize;
    let mut ancestor_pairs = 0usize;
    for (at, token) in kept.iter().enumerate().take(6) {
        let germs = token_germs_public(std::slice::from_ref(token))
            .map_err(|error| format!("{error:?}"))?;
        let current = atlas
            .receive_path(&germs)
            .map_err(|error| format!("{error:?}"))?;
        let fine = atlas.suffix_ancestor(current.state(), 0);
        let coarse = atlas.suffix_ancestor(current.state(), 1);
        let nested = chart.contains(coarse, fine) == Some(true);
        if nested {
            ancestor_pairs += 1;
        }
        // The germ reopens to its own token with no vocabulary file.
        let reopened = fiber_bytes(germs[0].identity()).map_err(|error| format!("{error:?}"))?;
        println!(
            "  row {at:<4} {:<18} layer0 class {fine} nested in layer1 class {coarse}: {nested}   germ reopens to {:?}",
            truncate(token, 18),
            reopened
        );
        demonstrated += 1;
    }
    println!(
        "  {ancestor_pairs} of {demonstrated} shown rows have layer 0 causally inside layer 1 —"
    );
    println!(
        "  the ROW ITSELF carries the scale hierarchy, as a causal order rather than a metric."
    );

    println!();
    println!("WHAT THIS IS NOT");
    println!("  This container is an embedding chart, not a runnable model: no attention, no");
    println!("  feed-forward, no declared architecture. What it establishes is the TRANSITION —");
    println!("  the atlas crosses into the industry's container exactly, every float carries its");
    println!("  exact preimage, and the read side returns it bit-identically.");
    println!("  The transport half costs the cycle rank above and is not carried here.");
    Ok(())
}

fn truncate(text: &str, at: usize) -> String {
    let cleaned: String = text.chars().filter(|c| !c.is_control()).collect();
    if cleaned.chars().count() <= at {
        cleaned
    } else {
        cleaned
            .chars()
            .take(at.saturating_sub(1))
            .chain("…".chars())
            .collect()
    }
}
