use std::fs;
use std::path::{Path, PathBuf};

use life::mathematical_particle::{
    AddressedHistorySystem, HistoricalInterior, LongHorizonRetainedBoundary,
};
use holonic_engine::receiver_exact_compression::ObservedSystem;
use serde::Serialize;
use serde_json::{json, Value};

use super::artifact;

const R0: &str = "output/the_rich_mathematical_inquiry_returns_the_i5_baseline_boundary";
const R2: &str =
    "output/the_material_derivation_recurs_until_the_requested_receiver_returns_or_obstructs";
const R3: &str = "output/the_returned_constraints_found_dynamic_local_morphology";

pub struct MountedHistory {
    pub interiors: Vec<HistoricalInterior>,
    pub occurrences: Vec<String>,
    pub source_closure: Value,
}

#[derive(Clone, Debug, Serialize)]
pub struct InquiryFront {
    pub occurrence: String,
    pub final_interior: usize,
    pub physical_start: u32,
    pub word: Vec<u32>,
    pub consequence: String,
}

#[derive(Debug)]
pub struct PassageInputs {
    pub source_words: Vec<u32>,
    pub source_word_offsets: Vec<u32>,
    pub source_starts: Vec<u32>,
    pub source_front_task_ranges: Vec<(usize, usize)>,
    pub uncondensed_starts: Vec<u32>,
    pub compact_words: Vec<u32>,
    pub compact_word_offsets: Vec<u32>,
    pub compact_starts: Vec<u32>,
    pub source_standing: Value,
    pub source_decoder: Value,
    pub source_fibres: Value,
    pub uncondensed_standing: Value,
    pub uncondensed_decoder: Value,
    pub uncondensed_fibres: Value,
}

pub fn mount(root: &Path) -> Result<MountedHistory, String> {
    let r0 = root.join(R0);
    let r2 = root.join(R2);
    let r3 = root.join(R3);
    let (_, r0_manifest) = artifact::read_json(&r0.join("MANIFEST.json"))?;
    let (_, r2_manifest) = artifact::read_json(&r2.join("MANIFEST.json"))?;
    let (_, r3_manifest) = artifact::read_json(&r3.join("MANIFEST.json"))?;
    if r0_manifest["schema"] != "holonics.r0.product-manifest.v1"
        || r2_manifest["schema"] != "holonics.r2.product-manifest.v1"
        || r3_manifest["schema"] != "holonics.r3.product-manifest.v1"
    {
        return Err("the admitted R0/R2/R3 product family moved".to_owned());
    }

    let materials: Vec<(PathBuf, Option<usize>)> = vec![
        (root.join("research/fixtures/r0_rich_inquiry/inquiry.md"), None),
        (root.join("research/fixtures/r0_rich_inquiry/inquiry.lean"), Some(0)),
        (r2.join("06-returned-constraint.lean"), Some(1)),
        (r2.join("15-complete-derivation-and-obstruction.md"), Some(2)),
        (root.join("research/fixtures/r0_rich_inquiry/support-route-a.svg"), None),
        (r2.join("08-derivation-complex.svg"), Some(4)),
        (r0.join("02-receiver-basis-and-controls.json"), Some(0)),
        (r3.join("02-local-morphology-delta.json"), Some(3)),
        (r3.join("05-held-out-inquiry.json"), Some(7)),
        (r3.join("09-world-return-and-later-conduct.json"), Some(8)),
    ];
    let mut interiors = Vec::with_capacity(materials.len());
    let mut occurrences: Vec<String> = Vec::with_capacity(materials.len());
    let mut addressed_sources = Vec::with_capacity(materials.len());
    for (path, predecessor) in materials {
        let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
        let payload_sha256 = artifact::digest(&bytes);
        let occurrence = format!("r4/history/{payload_sha256}");
        let predecessor = predecessor.map(|at| occurrences[at].clone());
        addressed_sources.push(json!({
            "occurrence": occurrence,
            "payload_sha256": payload_sha256,
            "octets": bytes.len(),
            "predecessor": predecessor,
            "locator_is_lineage_not_identity": path.strip_prefix(root).unwrap_or(&path).display().to_string(),
        }));
        interiors.push(HistoricalInterior {
            occurrence: occurrence.clone(),
            predecessor,
            payload_sha256,
            payload: bytes,
        });
        occurrences.push(occurrence);
    }
    Ok(MountedHistory {
        interiors,
        occurrences,
        source_closure: json!({
            "schema": "holonics.r4.source-predecessor-closure.v1",
            "truth_status": "implemented-exact",
            "r0_manifest_rolled_sha256": r0_manifest["rolled_sha256"],
            "r2_manifest_rolled_sha256": r2_manifest["rolled_sha256"],
            "r3_manifest_rolled_sha256": r3_manifest["rolled_sha256"],
            "addressed_sources": addressed_sources,
            "worktree_formal_sources_accessed": false,
            "uncommitted_material_accessed": false,
        }),
    })
}

pub fn inquiry_fronts(occurrences: &[String]) -> Vec<InquiryFront> {
    vec![
        InquiryFront {
            occurrence: format!("r4/front/proof/{}", occurrences[9]),
            final_interior: 9,
            physical_start: 1,
            word: vec![0, 1],
            consequence: "later proof return requires the remote family-support construction"
                .to_owned(),
        },
        InquiryFront {
            occurrence: format!("r4/front/diagram/{}", occurrences[5]),
            final_interior: 5,
            physical_start: 0,
            word: vec![1],
            consequence: "later diagram incidence requires the remote route geometry".to_owned(),
        },
        InquiryFront {
            occurrence: format!("r4/front/correction/{}", occurrences[6]),
            final_interior: 6,
            physical_start: 1,
            word: vec![1, 0],
            consequence: "the n=0 boundary correction reopens the hypothesis lineage".to_owned(),
        },
        InquiryFront {
            occurrence: format!("r4/front/predecessor-control/{}", occurrences[5]),
            final_interior: 5,
            physical_start: 0,
            word: vec![0],
            consequence: "the immediate predecessor action is the matched cultivation control"
                .to_owned(),
        },
    ]
}

pub fn passages(
    boundary: &LongHorizonRetainedBoundary,
    system: &AddressedHistorySystem,
    fronts: &[InquiryFront],
) -> Result<PassageInputs, String> {
    let mut source_words = Vec::new();
    let mut source_word_offsets = vec![0u32];
    let mut source_starts = Vec::new();
    let mut source_front_task_ranges = Vec::new();
    let mut source_fronts = Vec::new();
    let mut source_decoder = Vec::new();
    let mut source_fibres = Vec::new();
    let mut compact_words = Vec::new();
    let mut compact_word_offsets = vec![0u32];
    let mut compact_starts = Vec::new();

    for front in fronts {
        let chain = chain_indices(&boundary.decoder.interiors, front.final_interior)?;
        let first_task = source_starts.len();
        let mut prefix_replays = Vec::new();
        for interior in &chain {
            let source = system
                .source_item(*interior, front.physical_start)
                .ok_or("source start outside history system")?;
            source_starts.push(source.0 as u32);
            source_words.extend_from_slice(&front.word);
            source_word_offsets.push(source_words.len() as u32);
            let occurrence = &boundary.decoder.interiors[*interior].occurrence;
            let reconstructed = boundary
                .reconstruct_history(occurrence)
                .map_err(|error| error.to_string())?;
            prefix_replays.push(reconstructed.clone());
            source_decoder.push(json!({
                "front": front.occurrence,
                "source_item": source,
                "occurrence": occurrence,
                "exact_reconstruction": reconstructed,
            }));
            source_fibres.push(json!({
                "front": front.occurrence,
                "source_item": source,
                "source_state_fibre": [source],
                "reopened_history": prefix_replays.last(),
                "word": front.word,
            }));
        }
        let after_task = source_starts.len();
        source_front_task_ranges.push((first_task, after_task));
        source_fronts.push(json!({
            "occurrence": front.occurrence,
            "consequence": front.consequence,
            "word": front.word,
            "complete_prefix_replays": prefix_replays,
            "first_task": first_task,
            "after_task": after_task,
        }));

        let source = system
            .source_item(front.final_interior, front.physical_start)
            .ok_or("compact start outside history system")?;
        compact_starts.push(
            boundary
                .native_of_source(source)
                .map_err(|error| error.to_string())?
                .0 as u32,
        );
        compact_words.extend_from_slice(&front.word);
        compact_word_offsets.push(compact_words.len() as u32);
    }

    let uncondensed_fibres = system
        .items()
        .into_iter()
        .map(|item| json!({"source_item": item, "singleton_fibre": [item]}))
        .collect::<Vec<_>>();
    let uncondensed_starts = source_front_task_ranges
        .iter()
        .map(|(_, after)| source_starts[after - 1])
        .collect();
    let uncondensed_standing = json!({
        "schema": "holonics.r4.uncondensed-native-history-standing.v1",
        "states": system.interiors() * system.states(),
        "generators": system.generators(),
        "generator_table": system.source_generator_table(),
        "starts": &source_starts,
        "words": &source_words,
        "word_offsets": &source_word_offsets,
    });
    let uncondensed_decoder = json!({
        "schema": "holonics.r4.uncondensed-native-history-decoder.v1",
        "interiors": &boundary.decoder.interiors,
        "source_members": &boundary.decoder.source_members,
    });
    let uncondensed_fibres = json!({
        "schema": "holonics.r4.uncondensed-native-history-fibres.v1",
        "fibres": uncondensed_fibres,
    });
    Ok(PassageInputs {
        source_words,
        source_word_offsets,
        source_starts,
        source_front_task_ranges,
        uncondensed_starts,
        compact_words,
        compact_word_offsets,
        compact_starts,
        source_standing: json!({
            "schema": "holonics.r4.source-complete-replay-standing.v1",
            "realization": "complete-prefix-replay",
            "fronts": source_fronts,
        }),
        source_decoder: json!({
            "schema": "holonics.r4.source-complete-replay-decoder.v1",
            "entries": source_decoder,
        }),
        source_fibres: json!({
            "schema": "holonics.r4.source-complete-replay-fibres.v1",
            "fibres": source_fibres,
        }),
        uncondensed_standing,
        uncondensed_decoder,
        uncondensed_fibres,
    })
}

fn chain_indices(interiors: &[HistoricalInterior], final_at: usize) -> Result<Vec<usize>, String> {
    let by_occurrence = interiors
        .iter()
        .enumerate()
        .map(|(at, interior)| (interior.occurrence.as_str(), at))
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut chain = Vec::new();
    let mut at = final_at;
    loop {
        let interior = interiors.get(at).ok_or("history interior absent")?;
        chain.push(at);
        match interior.predecessor.as_deref() {
            Some(predecessor) => at = *by_occurrence
                .get(predecessor)
                .ok_or("history predecessor absent")?,
            None => break,
        }
    }
    chain.reverse();
    Ok(chain)
}
