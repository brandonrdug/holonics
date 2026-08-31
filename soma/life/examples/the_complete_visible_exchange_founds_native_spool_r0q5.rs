use std::{collections::BTreeMap, error::Error, fs, path::PathBuf};

use holonic_engine::{
    native_spool::NativeSpoolBundle,
    receiver_exact_compression::ReceiverId,
    receiver_history_compression::NativeStateId,
};
use life::{
    dialogue_lineage::{
        import_claude_visible_prefix, CodexDialogueImportSpec, ExactDialogueLineage,
    },
    dialogue_native_spool::{
        found_addressed_dialogue_native_spool, AddressedDialogueOccurrence,
    },
    exchange_world_tube::discover_complete_exchange_aperture,
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
        .map(|(container, spec)| -> Result<Vec<AddressedDialogueOccurrence>, String> {
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
                Ok(lineage
                    .occurrences()
                    .iter()
                    .map(|occurrence| AddressedDialogueOccurrence {
                        address: local[occurrence.identity.as_str()].clone(),
                        caused_by: occurrence
                            .caused_by
                            .iter()
                            .filter_map(|cause| local.get(cause.as_str()).cloned())
                            .collect(),
                    })
                    .collect())
            } else {
                let (visible, _) = import_claude_visible_prefix(&spec.locator, extent)?;
                let addresses = visible
                    .iter()
                    .map(|occurrence| {
                        format!(
                            "exchange/{container}/{}-{}",
                            occurrence.raw_range.start, occurrence.raw_range.end
                        )
                    })
                    .collect::<Vec<_>>();
                Ok(addresses
                    .iter()
                    .enumerate()
                    .map(|(at, address)| AddressedDialogueOccurrence {
                        address: address.clone(),
                        caused_by: at
                            .checked_sub(1)
                            .map(|prior| [addresses[prior].clone()].into_iter().collect())
                            .unwrap_or_default(),
                    })
                    .collect())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let occurrences = staged.into_iter().flatten().collect::<Vec<_>>();
    let returned = found_addressed_dialogue_native_spool(&occurrences)?;
    let wire = returned.native.canonical_bytes()?;
    let witness = serde_json::to_vec_pretty(&returned.exterior)?;
    fs::write(output.join("native-spool-bundle.rest"), &wire)?;
    fs::write(output.join("exterior-dialogue-lineage.json"), witness)?;

    let remounted = NativeSpoolBundle::read(&wire)?;
    let spool = remounted
        .spools
        .first()
        .ok_or("the native dialogue bundle has no spool")?;
    let generator = *spool
        .generator_family
        .first()
        .ok_or("the native dialogue spool has no generator")?;
    let mut word = remounted.mount_word(&spool.address, &[generator])?;
    let word_return = word.conduct(&[NativeStateId(0), NativeStateId(1)], ReceiverId(0))?;
    let mut current = remounted.mount_thread_current(
        &spool.address,
        &spool.threads[0].address,
    )?;
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
