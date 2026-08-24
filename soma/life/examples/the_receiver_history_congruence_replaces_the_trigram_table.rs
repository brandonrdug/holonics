use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    receiver_exact_compression::InputId,
};
use life::{
    athena_receiver_history::{
        AthenaReceiverHistoryCongruence, ProposalRelationKind, TransportSpecies,
    },
    exchange_world_tube::ContinuationAperture,
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const ACTIVE_OWNER: &str = concat!(
    include_str!("../src/athena_receiver_history.rs"),
    include_str!("../src/athena_receiver_history/system.rs"),
    include_str!("../src/athena_receiver_history/roles.rs"),
    include_str!("../src/athena_receiver_history/types.rs"),
);

fn main() -> Result<(), String> {
    let (aperture_path, output) = arguments()?;
    let aperture_bytes = fs::read(&aperture_path).map_err(|error| error.to_string())?;
    let aperture: ContinuationAperture =
        serde_json::from_slice(&aperture_bytes).map_err(|error| error.to_string())?;
    let mut executor = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let product = AthenaReceiverHistoryCongruence::found_on_device(&aperture, &mut executor)?;
    inspect_ordered_words(&product)?;
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;

    write_json(
        &output.join("00-receiver-history-congruence.json"),
        &product,
    )?;
    write_json(
        &output.join("01-source-to-native-fibres.json"),
        &product.native.reconstruction_fibres,
    )?;
    write_json(
        &output.join("02-shortest-separators.json"),
        &product.exact.collapsed,
    )?;
    write_json(
        &output.join("03-proposal-relative-roles.json"),
        &product.proposal_roles,
    )?;
    write_json(
        &output.join("04-surface-only-counterexamples.json"),
        &product.surface_only_counterexamples,
    )?;
    write_json(
        &output.join("05-resident-apparatus.json"),
        &product.resident,
    )?;
    write_json(
        &output.join("06-formal-obligations.json"),
        &json!({
            "schema": "holonics.athena-receiver-history-formal-obligations.v1",
            "lean_source": "soma/formal/elementary-holonics/ElementaryHolonics/Millennium/AthenaReceiverHistory.lean",
            "verification_command": "lake env lean ElementaryHolonics/Millennium/AthenaReceiverHistory.lean",
            "theorems": [
                "CompleteReceiverHistoryQuotient.quotientEq_iff_causalSignatureEq",
                "CompleteReceiverHistoryQuotient.quotientNe_returnsSeparatingReceiverHistory",
                "CompleteReceiverHistoryQuotient.quotientEqualityRetainsBothOccurrences"
            ]
        }),
    )?;

    let role_kinds = product
        .proposal_roles
        .iter()
        .map(|role| role.relation)
        .collect::<BTreeSet<_>>();
    let overlapping_roles = product
        .proposal_roles
        .iter()
        .fold(BTreeMap::<(&str, &str), usize>::new(), |mut found, role| {
            *found
                .entry((role.proposal.as_str(), role.target.as_str()))
                .or_default() += 1;
            found
        })
        .values()
        .filter(|population| **population > 1)
        .count();
    let rebase = product
        .transport_generators
        .iter()
        .find(|generator| generator.species == TransportSpecies::ExactRebase)
        .map(|generator| generator.generator)
        .ok_or("the exact rebase generator did not return")?;
    let rebase_closes = product.native.source_population.iter().all(|source| {
        product
            .native
            .ordered_word_consequence(*source, &[rebase, rebase])
            .is_ok_and(|word| word.source_end == *source && word.commutes())
    });
    let no_trigram_state = !ACTIVE_OWNER.contains("windows(3)")
        && !ACTIVE_OWNER.contains("len() == 3")
        && !ACTIVE_OWNER.contains("ContinuationPartition");
    let grade = json!({
        "schema": "holonics.athena-receiver-history-congruence-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "complete_source_population": product.sections.len(),
        "native_population": product.native.native_population.len(),
        "complete_fibre_population": product.native.reconstruction_fibres.len(),
        "shortest_separator_population": product.exact.collapsed.len(),
        "surface_only_counterexample_population": product.surface_only_counterexamples.len(),
        "memory_order": product.exact.memory_order(),
        "proposal_role_population": product.proposal_roles.len(),
        "overlapping_proposal_target_role_population": overlapping_roles,
        "every_required_role_relation_returned": ([
            ProposalRelationKind::Development,
            ProposalRelationKind::Sibling,
            ProposalRelationKind::HeldOut,
            ProposalRelationKind::Revisit,
            ProposalRelationKind::Rebase,
            ProposalRelationKind::Control,
        ]).into_iter().all(|role| role_kinds.contains(&role)),
        "generator_naturality_squares": product.native.generators.len(),
        "every_inspected_ordered_word_commutes": true,
        "exact_rebase_returns_both_identity_compositions": rebase_closes,
        "active_owner_contains_no_trigram_or_global_partition": no_trigram_state,
        "resident_gpu_quotient_returned": product.resident.launches > 0,
        "cpu_device_partition_equal": product.resident.cpu_device_partition_equal,
        "cpu_semantic_replay_after_device": product.resident.cpu_semantic_replay_after_device,
        "passed": product.validate().is_ok()
            && no_trigram_state
            && rebase_closes
            && overlapping_roles > 0
            && !product.surface_only_counterexamples.is_empty()
            && product.resident.launches > 0
    });
    write_json(&output.join("07-grade.json"), &grade)?;
    write_inspection(&output, &product, &grade)?;
    write_manifest(&output)?;
    if grade["passed"] != true {
        return Err("the receiver-history congruence grade refused".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn inspect_ordered_words(product: &AthenaReceiverHistoryCongruence) -> Result<(), String> {
    let generators = product
        .transport_generators
        .iter()
        .map(|generator| generator.generator)
        .collect::<Vec<_>>();
    let mut words = vec![Vec::<InputId>::new()];
    words.extend(generators.iter().map(|generator| vec![*generator]));
    for left in &generators {
        for right in &generators {
            words.push(vec![*left, *right]);
        }
    }
    for source in &product.native.source_population {
        for word in &words {
            if !product
                .native
                .ordered_word_consequence(*source, word)
                .map_err(|error| error.to_string())?
                .commutes()
            {
                return Err(format!("ordered native word failed at source {}", source.0));
            }
        }
    }
    Ok(())
}

fn arguments() -> Result<(PathBuf, PathBuf), String> {
    let mut aperture = PathBuf::from(
        "output/the_complete_laboratory_exchange_returns_for_athena_alpha/04-continuation-aperture.json",
    );
    let mut output =
        PathBuf::from("output/the_receiver_history_congruence_replaces_the_trigram_table");
    let mut args = env::args_os().skip(1);
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("{} carries no value", flag.to_string_lossy()))?;
        match flag.to_str() {
            Some("--aperture") => aperture = value.into(),
            Some("--output") => output = value.into(),
            _ => return Err(format!("unknown argument {}", flag.to_string_lossy())),
        }
    }
    Ok((aperture, output))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn write_inspection(
    output: &Path,
    product: &AthenaReceiverHistoryCongruence,
    grade: &serde_json::Value,
) -> Result<(), String> {
    let first = product
        .surface_only_counterexamples
        .first()
        .ok_or("no surface counterexample returned")?;
    let text = format!(
        "# Receiver-history congruence inspected return\n\n- Source causal sections: {}.\n- Native receiver/history states: {}.\n- Reconstruction fibres: {}.\n- Derived memory order: {:?}.\n- Resident device: `{}` in {} launches.\n- Proposal-relative role incidences: {}.\n- Surface-only counterexamples: {}.\n- First counterexample: `{}` and `{}` return surface `{}` but separate at receiver `{:?}` after {} addressed transports.\n- Complete station grade: `{}`.\n",
        product.sections.len(),
        product.native.native_population.len(),
        product.native.reconstruction_fibres.len(),
        product.exact.memory_order(),
        product.resident.device,
        product.resident.launches,
        product.proposal_roles.len(),
        product.surface_only_counterexamples.len(),
        first.left_family,
        first.right_family,
        first.equal_returned_surface_sha256,
        first.separating_receiver,
        first.shortest_ordered_word.len(),
        grade["passed"],
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(|error| error.to_string())
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file() && path.file_name().is_some_and(|name| name != "MANIFEST.json")
        })
        .collect::<Vec<_>>();
    files.sort();
    let entries = files
        .iter()
        .map(|path| {
            let bytes = fs::read(path).map_err(|error| error.to_string())?;
            Ok(json!({
                "path": path.file_name().unwrap().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": hex(Sha256::digest(&bytes).as_slice()),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let identity = {
        let bytes = serde_json::to_vec(&entries).map_err(|error| error.to_string())?;
        hex(Sha256::digest(bytes).as_slice())
    };
    write_json(
        &output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.athena-receiver-history-manifest.v1",
            "identity": identity,
            "files": entries,
        }),
    )
}

fn hex(octets: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(octets.len() * 2);
    for octet in octets {
        out.push(DIGITS[(octet >> 4) as usize] as char);
        out.push(DIGITS[(octet & 15) as usize] as char);
    }
    out
}
