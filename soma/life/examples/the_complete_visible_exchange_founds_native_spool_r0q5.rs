use std::{collections::BTreeMap, error::Error, fs, ops::Range, path::PathBuf};

use holonic_engine::{
    native_spool::NativeTransportScaffold, receiver_exact_compression::ReceiverId,
    receiver_history_compression::NativeStateId,
};
use life::{
    dialogue_lineage::{
        import_claude_visible_prefix, CodexDialogueImportSpec, DialoguePhase, DialogueSpeaker,
        ExactDialogueLineage,
    },
    dialogue_native_spool::{found_addressed_dialogue_native_spool, AddressedDialogueOccurrence},
    exchange_world_tube::{
        derive_continuation_aperture, discover_complete_exchange_aperture, ContainerLineageFaces,
        CorrespondenceFibres, DeviceContactReceipt, Digest32, ExchangeContainer, ExchangeRecord,
        ExchangeWorldTube, ExcludedPopulation, VisibleMessageFace,
    },
};
use rayon::prelude::*;
use serde::Serialize;

const OUTPUT: &str = "output/the_complete_visible_exchange_founds_native_spool_r0q5";

#[derive(Serialize)]
struct FoundingReceipt {
    truth_status: &'static str,
    container_population: usize,
    visible_occurrence_population: usize,
    native_state_population: usize,
    native_thread_population: usize,
    reconstruction_occurrence_population: usize,
    source_text_retained_in_native_wire: bool,
    provider_or_speaker_routes_native_transport: bool,
    source_detached_remount_exact: bool,
    resident_word_returned: bool,
    resident_complex_current_returned: bool,
    cpu_semantic_replay_after_device: bool,
    continuation_family_population: usize,
    richer_world_join_receiver_open: bool,
}

struct LocalVisible {
    raw_record: u64,
    raw_range: Range<u64>,
    occurrence: String,
    text: String,
    speaker: &'static str,
    phase: &'static str,
}

struct StagedContainer {
    addressed: Vec<AddressedDialogueOccurrence>,
    visible: Vec<LocalVisible>,
    complete_records: u64,
    captured_extent: u64,
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing R0Q5 founding {}", output.display()).into());
    }
    fs::create_dir_all(&output)?;
    let discovery = discover_complete_exchange_aperture(
        &root.join("/home/b/.codex/sessions"),
        &root.join("/home/b/.claude/projects/-home-b-Workspaces-holonics"),
        &root,
    )?;
    let staged = discovery
        .specs
        .par_iter()
        .enumerate()
        .map(|(container, spec)| -> Result<StagedContainer, String> {
            let extent = spec
                .locator
                .metadata()
                .map_err(|error| error.to_string())?
                .len();
            if spec.provider_face == "codex" {
                let lineage = ExactDialogueLineage::import_codex_rollout_prefix(
                    &spec.locator,
                    extent,
                    &CodexDialogueImportSpec::default(),
                )?;
                let local = lineage
                    .occurrences()
                    .iter()
                    .map(|occurrence| {
                        (
                            occurrence.identity.as_str(),
                            format!(
                                "exchange/{container}/{}-{}",
                                occurrence.raw_range.start, occurrence.raw_range.end
                            ),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                let addressed = lineage
                    .occurrences()
                    .iter()
                    .enumerate()
                    .map(|(at, occurrence)| AddressedDialogueOccurrence {
                        address: local[occurrence.identity.as_str()].clone(),
                        predecessor: at.checked_sub(1).map(|prior| {
                            local[lineage.occurrences()[prior].identity.as_str()].clone()
                        }),
                        caused_by: occurrence
                            .caused_by
                            .iter()
                            .filter_map(|cause| local.get(cause.as_str()).cloned())
                            .collect(),
                    })
                    .collect();
                let visible = lineage
                    .occurrences()
                    .iter()
                    .map(|occurrence| LocalVisible {
                        raw_record: occurrence.raw_record,
                        raw_range: occurrence.raw_range.clone(),
                        occurrence: local[occurrence.identity.as_str()].clone(),
                        text: occurrence.text.clone(),
                        speaker: match occurrence.speaker {
                            DialogueSpeaker::User => "user",
                            DialogueSpeaker::Assistant => "assistant",
                        },
                        phase: match occurrence.phase {
                            DialoguePhase::Received => "received",
                            DialoguePhase::Commentary => "commentary",
                            DialoguePhase::FinalAnswer => "final-answer",
                            DialoguePhase::Other(_) => "other",
                        },
                    })
                    .collect();
                Ok(StagedContainer {
                    addressed,
                    visible,
                    complete_records: lineage.receipt().complete_records,
                    captured_extent: extent,
                })
            } else {
                let (visible, receipt) = import_claude_visible_prefix(&spec.locator, extent)?;
                let addresses = visible
                    .iter()
                    .map(|occurrence| {
                        format!(
                            "exchange/{container}/{}-{}",
                            occurrence.raw_range.start, occurrence.raw_range.end
                        )
                    })
                    .collect::<Vec<_>>();
                let addressed = addresses
                    .iter()
                    .enumerate()
                    .map(|(at, address)| AddressedDialogueOccurrence {
                        address: address.clone(),
                        predecessor: at.checked_sub(1).map(|prior| addresses[prior].clone()),
                        caused_by: at
                            .checked_sub(1)
                            .map(|prior| [addresses[prior].clone()].into_iter().collect())
                            .unwrap_or_default(),
                    })
                    .collect();
                let visible = visible
                    .into_iter()
                    .zip(&addresses)
                    .map(|(occurrence, address)| LocalVisible {
                        raw_record: occurrence.raw_record,
                        raw_range: occurrence.raw_range,
                        occurrence: address.clone(),
                        text: occurrence.text,
                        speaker: match occurrence.speaker {
                            DialogueSpeaker::User => "user",
                            DialogueSpeaker::Assistant => "assistant",
                        },
                        phase: "visible",
                    })
                    .collect();
                Ok(StagedContainer {
                    addressed,
                    visible,
                    complete_records: receipt.complete_records,
                    captured_extent: extent,
                })
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let occurrences = staged
        .iter()
        .flat_map(|container| container.addressed.iter().cloned())
        .collect::<Vec<_>>();
    let source_occurrence = Digest32::of(&serde_json::to_vec(&occurrences)?);
    let mut containers = Vec::with_capacity(staged.len());
    let mut records = Vec::new();
    let mut visible_messages = Vec::new();
    for (container, local) in staged.iter().enumerate() {
        let record_from = records.len() as u64;
        for face in &local.visible {
            let record = records.len() as u64;
            let content = Digest32::of(face.text.as_bytes());
            records.push(ExchangeRecord {
                container: container as u32,
                ordinal: face.raw_record,
                raw_range: face.raw_range.clone(),
                raw_sha256: content,
                root_sha256: content,
                node_from: 0,
                node_extent: 0,
                field_from: 0,
                field_extent: 0,
            });
            visible_messages.push(VisibleMessageFace {
                container: container as u32,
                record,
                raw_range: face.raw_range.clone(),
                occurrence: face.occurrence.clone(),
                text_sha256: content,
                text: face.text.clone(),
                provider_face: discovery.specs[container].provider_face.clone(),
                speaker_face: face.speaker.to_owned(),
                phase_face: face.phase.to_owned(),
            });
        }
        containers.push(ExchangeContainer {
            ordinal: container as u32,
            captured_extent: local.captured_extent,
            prefix_sha256: Digest32::ZERO,
            record_from,
            record_extent: local.complete_records,
            incomplete_tail: None,
            blank_records: Vec::new(),
            lineage: ContainerLineageFaces {
                locator: discovery.specs[container].locator.clone(),
                provider: discovery.specs[container].provider_face.clone(),
                material_kind: discovery.specs[container].material_kind_face.clone(),
            },
        });
    }
    let visible_world = ExchangeWorldTube {
        schema: "soma-life.visible-continuation-world.v1".to_owned(),
        source_occurrence_sha256: source_occurrence,
        content_law_sha256: Digest32::ZERO,
        containers,
        records,
        nodes: Vec::new(),
        fields: Vec::new(),
        scalar_sites: Vec::new(),
        visible_messages,
        fibres: CorrespondenceFibres {
            singleton_classes: 0,
            repeated_classes: 0,
            repeated_sites: 0,
            class_members: BTreeMap::new(),
        },
        excluded: ExcludedPopulation {
            blank_records: 0,
            incomplete_tails: 0,
            visible_membrane_controls: 0,
            unavailable_private_reasoning_required: false,
        },
        device: DeviceContactReceipt {
            schema: "soma-life.visible-continuation-apparatus.v1".to_owned(),
            device: "not-invoked".to_owned(),
            scalar_sites: 0,
            contact_classes: 0,
            launches: 0,
            block_threads: 0,
            warp_size: 0,
            cpu_semantic_replay: false,
        },
    };
    let mut aperture = derive_continuation_aperture(&visible_world)?;
    for container in 0..staged.len() {
        aperture.exclusions.push(life::exchange_world_tube::ContinuationExclusion {
            container: container as u32,
            visible_index: None,
            occurrence: None,
            obstruction: "richer parent/tool/world joins remain open outside the visible-only continuation receiver".to_owned(),
        });
    }
    let returned = found_addressed_dialogue_native_spool(&occurrences)?;
    let wire = returned.native.canonical_bytes()?;
    let witness = serde_json::to_vec_pretty(&returned.exterior)?;
    fs::write(output.join("native-transport-scaffold.rest"), &wire)?;
    fs::write(output.join("exterior-dialogue-lineage.json"), witness)?;
    fs::write(
        output.join("continuation-aperture.json"),
        serde_json::to_vec_pretty(&aperture)?,
    )?;

    let remounted = NativeTransportScaffold::read(&wire)?;
    let spool = remounted
        .spools
        .first()
        .ok_or("the native dialogue scaffold has no spool")?;
    let generator = *spool
        .generator_family
        .first()
        .ok_or("the native dialogue spool has no generator")?;
    let mut word = remounted.mount_word(&spool.address, &[generator])?;
    let word_return = word.conduct(&[NativeStateId(0), NativeStateId(1)], ReceiverId(0))?;
    let mut current = remounted.mount_thread_current(&spool.address, &spool.threads[0].address)?;
    let current_return = current.conduct()?;
    let receipt = FoundingReceipt {
        truth_status: "established-bounded",
        container_population: discovery.specs.len(),
        visible_occurrence_population: occurrences.len(),
        native_state_population: spool.native_population.len(),
        native_thread_population: spool.threads.len(),
        reconstruction_occurrence_population: spool
            .reconstruction_fibres
            .iter()
            .map(|fibre| fibre.occurrences.len())
            .sum(),
        source_text_retained_in_native_wire: false,
        provider_or_speaker_routes_native_transport: false,
        source_detached_remount_exact: remounted.canonical_bytes()? == wire,
        resident_word_returned: !word_return.native_end.is_empty(),
        resident_complex_current_returned: !current_return.sections.is_empty(),
        cpu_semantic_replay_after_device: current_return.cpu_semantic_replay_after_device,
        continuation_family_population: aperture.families.len(),
        richer_world_join_receiver_open: true,
    };
    if receipt.visible_occurrence_population == 0
        || receipt.visible_occurrence_population != receipt.reconstruction_occurrence_population
        || !receipt.source_detached_remount_exact
        || !receipt.resident_word_returned
        || !receipt.resident_complex_current_returned
        || receipt.cpu_semantic_replay_after_device
    {
        return Err("the complete visible exchange did not found one native spool".into());
    }
    fs::write(
        output.join("founding-receipt.json"),
        serde_json::to_vec_pretty(&receipt)?,
    )?;
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut root = std::env::current_dir()?;
    while !root.join("Cargo.toml").is_file() || !root.join("blueprint/THE_ROADMAP.md").is_file() {
        if !root.pop() {
            return Err("repository root was not found".into());
        }
    }
    Ok(root)
}
