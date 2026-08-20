//! **Deed P0, the rest-building half: the native rest is emitted from declared canon material and
//! carries the statements of the laws that read it.**
//!
//! Plan: `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md` §8 Deed
//! P0. This driver is the ecology side of the deed: the suffix ecology and its atlas live in
//! `soma/life`, so the container is built here and **nothing here conducts**. The engine driver
//! `crates/holonic-engine/examples/the_native_baseline_conducts_from_its_own_rest.rs` mounts what
//! this writes and is the only thing that touches a card.
//!
//! **What is added to ATHENA-002's shape, and why.** ATHENA-002 already emits the transport as
//! compressed sparse rows, the standings, the suffix links, the vocabulary and a declared
//! architecture. A resident law cannot bind to any of that: the front passage refuses a law whose
//! testimony no witness authenticates, and a native rest has no implementation text to resolve a
//! symbol against. So the rest carries, **in the container's own metadata**, the statement of every
//! law that reads it — and `native_occurrence::NativeOccurrence` refuses a law the rest does not
//! declare exactly as `source_occurrence::SourceOccurrence` refuses a slice the implementation does
//! not carry. The rest is its own authority; that is the whole addition.
//!
//! **The ablation is construction-level and says so.** A second container is emitted from the same
//! material minus one declared document. That is a rebuild, not a deletion in place: class indices,
//! standings and the vocabulary are all corpus-wide, so withdrawing a document moves the whole
//! atlas. Deleting a founded class from a standing atlas is a different operation and is not
//! claimed here.
//!
//! ```text
//! cargo run --release -q -p life --example the_native_rest_is_built_and_declares_its_own_laws
//! ```

use std::collections::{BTreeMap, BTreeSet};

use body::num::Cog;
use holonic_engine::athena::{emit_integers, IntegerDtype, IntegerTensor, TreeChart};
use holonic_engine::native_law::{DEPTH_LAW, FUTURE_LAW, WALK_LAW};
use life::causal_language::{fiber_bytes, CausalLanguageEcology, CausalLanguagePassage};
use soma_abi::active::ActionCurrent;

/// **The declared material.** ATHENA-002's four are the standing precedent; four more canon tablets
/// are added so the atlas is large enough that the future section's launch covers more than one
/// residency wave, and every one of them is named here rather than globbed.
const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
    ("canon/TABLET_THE_TURN.md", 5),
    ("canon/TABLET_THE_MANIFOLD.md", 6),
    ("canon/TABLET_THE_HEXIS.md", 7),
    ("canon/TABLET_THE_REASONING_CYCLE.md", 8),
];

/// The document the ablated rest is built without.
const WITHDRAWN: &str = "canon/TABLET_THE_HEXIS.md";

const SCHEMA: &str = "holonic-engine.athena-native-rest.v1";
const OUT: &str = "output/the_native_baseline_conducts";

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

struct Built {
    classes: usize,
    transitions: usize,
    vocabulary: usize,
    height: u32,
    octets: usize,
}

fn build(material: &[(&str, u64)], into: &str) -> Result<Built, String> {
    let mut passages = Vec::new();
    for (path, receiver) in material {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8).map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();
    let classes = atlas.state_count();
    let chart = TreeChart::label(classes, |state| atlas.suffix_link(state)).map_err(|error| format!("{error:?}"))?;

    // ---- vocabulary, canonical ----
    let mut index_of: BTreeMap<String, u32> = BTreeMap::new();
    let mut ordered: Vec<String> = Vec::new();
    {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for state in 0..classes as u32 {
            for (germ, _) in atlas.outgoing(state) {
                seen.insert(fiber_bytes(germ.identity()).map_err(|error| format!("{error:?}"))?);
            }
        }
        for (at, token) in seen.into_iter().enumerate() {
            index_of.insert(token.clone(), at as u32);
            ordered.push(token);
        }
    }

    // ---- transport, rows SORTED BY GERM INDEX because the card searches them ----
    let mut indptr: Vec<u64> = vec![0];
    let mut germ: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    let mut suffix: Vec<u64> = Vec::with_capacity(classes);
    for state in 0..classes as u32 {
        let mut rows: Vec<(u32, u32)> = atlas
            .outgoing(state)
            .into_iter()
            .map(|(g, t)| {
                let token = fiber_bytes(g.identity()).unwrap_or_default();
                (index_of.get(&token).copied().unwrap_or(u32::MAX), t)
            })
            .collect();
        rows.sort();
        for (index, reaches) in rows {
            germ.push(u64::from(index));
            target.push(u64::from(reaches));
        }
        indptr.push(germ.len() as u64);
        standing.push(atlas.standing_at(state).unwrap_or(0));
        suffix.push(u64::from(atlas.suffix_link(state).unwrap_or(0)));
    }

    // ---- the vocabulary's surfaces as octets plus offsets: integers, and the surfaces come back
    let mut vocabulary_octets: Vec<u64> = Vec::new();
    let mut vocabulary_offsets: Vec<u64> = vec![0];
    for token in &ordered {
        vocabulary_octets.extend(token.as_bytes().iter().map(|octet| u64::from(*octet)));
        vocabulary_offsets.push(vocabulary_octets.len() as u64);
    }

    // **The germ carrier is U32, not U16.** The card's transport rows are searched with `u32`
    // comparisons and the walk's prompt marks an unseen germ by an index at or above the
    // vocabulary; a 16-bit carrier would put a second ceiling under the first and refuse a
    // vocabulary the material can perfectly well found.
    let integers: Vec<IntegerTensor> = vec![
        emit_integers("athena.transport.indptr", &indptr, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.transport.germ", &germ, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.transport.target", &target, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.class.standing", &standing, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.class.suffix", &suffix, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.vocabulary.octets", &vocabulary_octets, 1, IntegerDtype::U16).map_err(|e| format!("{e:?}"))?,
        emit_integers("athena.vocabulary.offsets", &vocabulary_offsets, 1, IntegerDtype::U32).map_err(|e| format!("{e:?}"))?,
        emit_integers(
            "athena.architecture",
            &[u64::from(chart.height), classes as u64, germ.len() as u64, ordered.len() as u64],
            1,
            IntegerDtype::U32,
        )
        .map_err(|e| format!("{e:?}"))?,
    ];

    // ---- the metadata: the rest's own declarations, which are what a law binds against ----
    let mut metadata: BTreeMap<String, String> = BTreeMap::new();
    metadata.insert("schema".to_owned(), SCHEMA.to_owned());
    metadata.insert("law.walk".to_owned(), WALK_LAW.to_owned());
    metadata.insert("law.future".to_owned(), FUTURE_LAW.to_owned());
    metadata.insert("law.depth".to_owned(), DEPTH_LAW.to_owned());
    metadata.insert(
        "architecture".to_owned(),
        "the depth receiver is the suffix-link height: reading at height k is the atlas at a coarser \
         grain, the height is the tree's own and is read off the material rather than chosen, and the \
         transport is compressed sparse rows with the suffix link as the arc. No layer, head, rank or \
         latent width is declared and none is needed to run it."
            .to_owned(),
    );
    metadata.insert(
        "material".to_owned(),
        material.iter().map(|(path, receiver)| format!("{path}@{receiver}")).collect::<Vec<_>>().join(" "),
    );
    metadata.insert(
        "carriers".to_owned(),
        "every population is an integer carrier at grain 2^0; the walk's mark is 1 forward, 0 arc, 2 unseen".to_owned(),
    );

    let container = write_container(&integers, &metadata);
    std::fs::create_dir_all(OUT).map_err(|error| format!("{OUT}: {error}"))?;
    std::fs::write(into, &container).map_err(|error| format!("{into}: {error}"))?;
    Ok(Built { classes, transitions: germ.len(), vocabulary: ordered.len(), height: chart.height, octets: container.len() })
}

/// The safetensors header with a `__metadata__` object. Written here because the format is a
/// length, a JSON map and a flat payload, and the reader (`foreign_map::manifest_safetensors`) is
/// already in this project's own source.
fn write_container(tensors: &[IntegerTensor], metadata: &BTreeMap<String, String>) -> Vec<u8> {
    let escape = |text: &str| text.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n");
    let mut header = String::from("{\"__metadata__\":{");
    for (at, (key, value)) in metadata.iter().enumerate() {
        if at > 0 {
            header.push(',');
        }
        header.push_str(&format!("\"{}\":\"{}\"", escape(key), escape(value)));
    }
    header.push('}');
    let mut offset = 0usize;
    for tensor in tensors {
        let end = offset + tensor.octets.len();
        header.push_str(&format!(
            ",\"{}\":{{\"dtype\":\"{}\",\"shape\":[{},{}],\"data_offsets\":[{offset},{end}]}}",
            tensor.name,
            tensor.dtype.name(),
            tensor.rows,
            tensor.width
        ));
        offset = end;
    }
    header.push('}');
    while header.len() % 8 != 0 {
        header.push(' ');
    }
    let mut octets = Vec::with_capacity(8 + header.len() + offset);
    octets.extend_from_slice(&(header.len() as u64).to_le_bytes());
    octets.extend_from_slice(header.as_bytes());
    for tensor in tensors {
        octets.extend_from_slice(&tensor.octets);
    }
    octets
}

fn run() -> Result<(), String> {
    println!("THE NATIVE REST IS BUILT AND DECLARES ITS OWN LAWS — Deed P0, the ecology half\n");

    let whole = format!("{OUT}/rest.safetensors");
    let built = build(MATERIAL, &whole)?;
    println!("  THE REST — {} declared documents", MATERIAL.len());
    for (path, receiver) in MATERIAL {
        println!("      {path}  receiver {receiver}");
    }
    println!(
        "    classes {}   transitions {}   vocabulary {}   suffix-link tree height {}",
        built.classes, built.transitions, built.vocabulary, built.height
    );
    println!("    cycle rank of the transition graph  b1 = |E| - |S| + 1 = {}", built.transitions as i64 - built.classes as i64 + 1);
    println!("    container {} octets = {} KiB  -> {whole}", built.octets, built.octets / 1024);
    println!("    declared laws in the container's own metadata: walk, future, depth");

    let ablated_material: Vec<(&str, u64)> = MATERIAL.iter().copied().filter(|(path, _)| *path != WITHDRAWN).collect();
    let ablated_path = format!("{OUT}/rest-without-hexis.safetensors");
    let ablated = build(&ablated_material, &ablated_path)?;
    println!();
    println!("  THE ABLATED REST — the same material minus {WITHDRAWN}");
    println!(
        "    classes {}   transitions {}   vocabulary {}   suffix-link tree height {}",
        ablated.classes, ablated.transitions, ablated.vocabulary, ablated.height
    );
    println!("    cycle rank b1 = {}", ablated.transitions as i64 - ablated.classes as i64 + 1);
    println!("    container {} octets = {} KiB  -> {ablated_path}", ablated.octets, ablated.octets / 1024);
    println!();
    println!(
        "    the withdrawal removes {} classes, {} transitions and {} vocabulary germs",
        built.classes as i64 - ablated.classes as i64,
        built.transitions as i64 - ablated.transitions as i64,
        built.vocabulary as i64 - ablated.vocabulary as i64
    );
    println!();
    println!("  This is CONSTRUCTION-LEVEL ablation: the rest is rebuilt without one document, so");
    println!("  class indices, standings and the vocabulary all move. Deleting a founded class in");
    println!("  place is a different operation and is not claimed.");
    Ok(())
}
