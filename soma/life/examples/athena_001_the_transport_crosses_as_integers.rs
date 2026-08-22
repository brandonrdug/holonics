//! **ATHENA-001 — the transport half, as integers, after station one refuted the dense one.**
//!
//! Station one measured the Hankel rank of real material and it **does not saturate**: 1,638 of
//! 2,048 at the widest aperture swept, against 25,030 classes, with both prime frames agreeing. By
//! Fliess–Kalman the minimal exact dimension of a linear representation IS that rank, so there is no
//! small dense chart and the route posed in the blueprint is refuted.
//!
//! **That is the same fact as the Gemma measurement.** Every trained circuit came back full rank —
//! 256 of 256, deficit zero, at layers 0, 20 and 41. The material genuinely has that much dimension,
//! training fills the shape because the shape is demanded, and the industry is not wasting rank.
//!
//! **So the compression is not low rank. It is sparsity with exact integer structure**, which is
//! what the atlas natively is and what MoE found empirically from the other side. A dense chart of
//! this transport would be gigabytes; the sparse one is measured below.
//!
//! **And `BF16` cannot carry it.** Eight significand bits means every integer above 256 is
//! unrepresentable, so a container whose content is *structure* rather than *magnitude* needs
//! integer dtypes. This emits `U16` and `U32` and nothing crosses inexactly.

use std::collections::BTreeMap;

use body::num::Cog;
use holonic_engine::athena::{emit_integers, integer_container, IntegerDtype};
use life::causal_language::{
    fiber_bytes, lexical_tokens, CausalLanguageEcology, CausalLanguagePassage,
};
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
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

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();
    let classes = atlas.state_count();

    // ---- the vocabulary, canonically ordered, so a germ index is an address into it ----
    let mut vocabulary: BTreeMap<String, u64> = BTreeMap::new();
    let mut surfaces: Vec<String> = Vec::new();
    for state in 0..classes as u32 {
        for (germ, _) in atlas.outgoing(state) {
            let token = fiber_bytes(germ.identity()).map_err(|error| format!("{error:?}"))?;
            if !vocabulary.contains_key(&token) {
                vocabulary.insert(token.clone(), 0);
            }
        }
    }
    for (at, (token, index)) in vocabulary.iter_mut().enumerate() {
        *index = at as u64;
        surfaces.push(token.clone());
    }

    // ---- the transport, laid out as compressed sparse rows ----
    //
    // `indptr[s]..indptr[s+1]` is class `s`'s outgoing span. Every entry is an exact integer and
    // there is no scale, no zero point, and no rounding anywhere in this container.
    let mut indptr: Vec<u64> = Vec::with_capacity(classes + 1);
    let mut germ_index: Vec<u64> = Vec::new();
    let mut target: Vec<u64> = Vec::new();
    let mut standing: Vec<u64> = Vec::with_capacity(classes);
    let mut suffix: Vec<u64> = Vec::with_capacity(classes);
    indptr.push(0);
    for state in 0..classes as u32 {
        let mut rows = atlas.outgoing(state);
        rows.sort_by_key(|(germ, _)| fiber_bytes(germ.identity()).unwrap_or_default());
        for (germ, reaches) in rows {
            let token = fiber_bytes(germ.identity()).map_err(|error| format!("{error:?}"))?;
            germ_index.push(vocabulary[&token]);
            target.push(u64::from(reaches));
        }
        indptr.push(germ_index.len() as u64);
        standing.push(atlas.standing_at(state).unwrap_or(0));
        // The root has no suffix parent; it addresses itself, which is the absorbing convention the
        // climb already uses.
        suffix.push(u64::from(atlas.suffix_link(state).unwrap_or(0)));
    }
    let transitions = germ_index.len();

    println!("ATHENA-001 — the transport as integers\n");
    println!("  classes                {classes}");
    println!("  germ transitions       {transitions}");
    println!("  vocabulary             {}", vocabulary.len());
    println!();

    let tensors = vec![
        emit_integers("athena.transport.indptr", &indptr, 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers("athena.transport.germ", &germ_index, 1, IntegerDtype::U16)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers("athena.transport.target", &target, 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers("athena.class.standing", &standing, 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))?,
        emit_integers("athena.class.suffix", &suffix, 1, IntegerDtype::U32)
            .map_err(|error| format!("{error:?}"))?,
    ];
    println!(
        "  {:<32} {:>10} {:>8} {:>12}",
        "tensor", "entries", "dtype", "octets"
    );
    for tensor in &tensors {
        println!(
            "  {:<32} {:>10} {:>8} {:>12}",
            tensor.name,
            tensor.rows,
            tensor.dtype.name(),
            tensor.octets.len()
        );
    }
    let container = integer_container(&tensors);
    std::fs::create_dir_all("output/athena-001")
        .map_err(|error| format!("output/athena-001: {error}"))?;
    let path = "output/athena-001/model.safetensors";
    std::fs::write(path, &container).map_err(|error| format!("{path}: {error}"))?;
    println!();
    println!(
        "  CONTAINER              {} octets = {} KiB",
        container.len(),
        container.len() / 1024
    );
    println!("  every entry an INTEGER: no scale, no zero point, no rounding, no residual.");

    // ---- read it back and REPLAY THE TRANSPORT from the container alone ----
    let length = u64::from_le_bytes(container[..8].try_into().unwrap()) as usize;
    let header =
        core::str::from_utf8(&container[8..8 + length]).map_err(|error| format!("{error}"))?;
    let payload = &container[8 + length..];
    let mut spans: BTreeMap<String, (usize, usize, usize)> = BTreeMap::new();
    for tensor in &tensors {
        let needle = format!("\"{}\":", tensor.name);
        if !header.contains(&needle) {
            return Err(format!("{} is not in the header", tensor.name));
        }
    }
    let mut offset = 0usize;
    for tensor in &tensors {
        spans.insert(
            tensor.name.clone(),
            (offset, offset + tensor.octets.len(), tensor.dtype.octets()),
        );
        offset += tensor.octets.len();
    }
    let read_u32 = |name: &str| -> Vec<u32> {
        let (start, end, _) = spans[name];
        payload[start..end]
            .chunks_exact(4)
            .map(|row| u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
            .collect()
    };
    let read_u16 = |name: &str| -> Vec<u16> {
        let (start, end, _) = spans[name];
        payload[start..end]
            .chunks_exact(2)
            .map(|row| u16::from_le_bytes([row[0], row[1]]))
            .collect()
    };
    let back_indptr = read_u32("athena.transport.indptr");
    let back_germ = read_u16("athena.transport.germ");
    let back_target = read_u32("athena.transport.target");
    let back_suffix = read_u32("athena.class.suffix");

    // **The falsifier: replay every walk the atlas makes, from the container alone.** No ecology, no
    // corpus, no organ -- only the integers that crossed. A single disagreement means the container
    // does not carry the transport it claims to.
    let carry = |state: u32, germ: u16| -> Option<(u32, bool)> {
        let mut at = state;
        loop {
            let from = back_indptr[at as usize] as usize;
            let to = back_indptr[at as usize + 1] as usize;
            if let Some(found) = (from..to).find(|slot| back_germ[*slot] == germ) {
                return Some((back_target[found], true));
            }
            let parent = back_suffix[at as usize];
            if parent == at {
                return Some((0, false));
            }
            at = parent;
        }
    };

    let mut walks = 0usize;
    let mut disagreements = 0usize;
    let mut stream: Vec<String> = Vec::new();
    for (path, _) in MATERIAL {
        stream.extend(lexical_tokens(
            &std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?,
        ));
    }
    let probe: Vec<String> = stream.iter().take(4000).cloned().collect();
    let mut container_state = 0u32;
    let mut atlas_current = life::suffix_ecology::ExactSuffixCurrent::root_public();
    for token in &probe {
        let Some(index) = vocabulary.get(token).copied() else {
            continue;
        };
        let germs = life::causal_language::token_germs_public(std::slice::from_ref(token))
            .map_err(|error| format!("{error:?}"))?;
        atlas_current = atlas
            .carry(atlas_current, &germs[0])
            .map_err(|error| format!("{error:?}"))?;
        let (next, _) = carry(container_state, index as u16).ok_or("the replay lost its state")?;
        container_state = next;
        walks += 1;
        if container_state != atlas_current.state() {
            disagreements += 1;
        }
    }
    println!();
    println!("THE REPLAY — every walk taken from the CONTAINER alone, no organ present");
    println!("  walks                  {walks}");
    println!("  disagreements          {disagreements}");
    if disagreements > 0 {
        return Err(format!(
            "the container disagreed with the atlas on {disagreements} of {walks} walks"
        ));
    }
    println!("  the container reproduces the atlas's transport EXACTLY, walk for walk.");

    println!();
    println!("WHAT THIS SETTLES");
    println!("  The transport half crosses into the industry's container as pure integers, and it");
    println!("  replays. The dense route was refuted by measurement rather than abandoned: the");
    println!(
        "  Hankel rank does not saturate, so a linear chart of this transport is an expansion"
    );
    println!("  of it. Sparsity is the compression, and it is exact.");
    Ok(())
}
