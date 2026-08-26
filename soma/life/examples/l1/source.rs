use std::path::Path;
use std::process::Command;

use life::mathematical_particle::{
    LaboratoryChronology, LaboratoryCommitOccurrence, LaboratoryPartition, LaboratoryPartitionKind,
    LaboratorySourceChange, LABORATORY_CHRONOLOGY_SCHEMA,
};

use super::artifact;

pub const PREDECESSOR_COMMIT: &str = "4ba0cb0af51bcad9f5e45c7ef3f7c7ac6f7db0e3";
pub const PREFIX_COMMIT: &str = "443cd61dd3e7e06e395350ee5d6b98a6db3c890a";
pub const PREFIX_TREE: &str = "88cad5e993d44fd6c7e2f4ec76b409c2f783ae04";

fn git(root: &Path, arguments: &[&str]) -> Result<Vec<u8>, String> {
    let returned = Command::new("git")
        .args(arguments)
        .current_dir(root)
        .output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "git {} refused: {}",
            arguments.join(" "),
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(returned.stdout)
}

pub fn mount(root: &Path) -> Result<LaboratoryChronology, String> {
    let range = format!("{PREDECESSOR_COMMIT}..{PREFIX_COMMIT}");
    let revisions = String::from_utf8(git(root, &["rev-list", "--reverse", &range])?)
        .map_err(|error| error.to_string())?
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if revisions.len() != 14 {
        return Err(format!(
            "the frozen L1 chronology expected fourteen addressed commits and returned {}",
            revisions.len()
        ));
    }
    let actual_tree = String::from_utf8(git(
        root,
        &["rev-parse", &format!("{PREFIX_COMMIT}^{{tree}}")],
    )?)
    .map_err(|error| error.to_string())?;
    if actual_tree.trim() != PREFIX_TREE {
        return Err("the frozen L1 prefix tree moved".to_owned());
    }
    let mut occurrences = Vec::with_capacity(revisions.len());
    let mut mounted_octets = 0_u64;
    for revision in revisions {
        let metadata = git(
            root,
            &[
                "show",
                "-s",
                "--format=%H%x00%P%x00%T%x00%ct%x00%s",
                &revision,
            ],
        )?;
        let fields = metadata
            .split(|byte| *byte == 0)
            .map(|field| String::from_utf8_lossy(field).trim().to_owned())
            .collect::<Vec<_>>();
        if fields.len() != 5 {
            return Err(format!(
                "commit metadata for {revision} did not return five fields"
            ));
        }
        let changes_text = String::from_utf8(git(
            root,
            &[
                "diff-tree",
                "--no-commit-id",
                "--name-status",
                "-r",
                &revision,
            ],
        )?)
        .map_err(|error| error.to_string())?;
        let mut changes = Vec::new();
        for line in changes_text.lines() {
            let mut columns = line.splitn(2, '\t');
            let status = columns.next().ok_or("change status absent")?.to_owned();
            let lineage_path = columns.next().ok_or("change path absent")?.to_owned();
            let bytes = git(root, &["show", &format!("{revision}:{lineage_path}")])?;
            let blob_sha256 = artifact::digest(&bytes);
            mounted_octets = mounted_octets
                .checked_add(bytes.len() as u64)
                .ok_or("incremental L1 source extent overflow")?;
            changes.push(LaboratorySourceChange {
                occurrence: format!("git/{revision}/{lineage_path}/{blob_sha256}"),
                status,
                lineage_path,
                blob_sha256,
                octets: bytes.len() as u64,
            });
        }
        occurrences.push(LaboratoryCommitOccurrence {
            occurrence: format!("git/commit/{}", fields[0]),
            commit: fields[0].clone(),
            parent: fields[1].clone(),
            tree: fields[2].clone(),
            committed_unix_seconds: fields[3]
                .parse()
                .map_err(|error| format!("commit time refused: {error}"))?,
            summary: fields[4].clone(),
            changes,
        });
    }
    let address = |needle: &str| -> Result<String, String> {
        occurrences
            .iter()
            .flat_map(|commit| &commit.changes)
            .find(|change| change.lineage_path.ends_with(needle))
            .map(|change| change.occurrence.clone())
            .ok_or_else(|| format!("frozen L1 occurrence {needle} absent"))
    };
    let partitions = vec![
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::Development,
            occurrences: vec![address("NavierStokesPeriodicFlux.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::HeldOutSuccessor,
            occurrences: vec![address("GeneralClassCoordinates.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::CodecNotationLayoutRebase,
            occurrences: vec![address("HilbertTransportSpectrum.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::PhysicalApparatusPerturbation,
            occurrences: vec![address("GeneralRealPlace.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::EqualAnswerDifferentRoute,
            occurrences: vec![address("GeneralQuotientCardinality.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::SubjectPortDisjointControl,
            occurrences: vec![address("GeneralOddPlace.lean")?],
        },
        LaboratoryPartition {
            kind: LaboratoryPartitionKind::LaterChronology,
            occurrences: vec![address("GeneralMordell.lean")?],
        },
    ];
    let chronology = LaboratoryChronology {
        schema: LABORATORY_CHRONOLOGY_SCHEMA.to_owned(),
        predecessor_commit: PREDECESSOR_COMMIT.to_owned(),
        prefix_commit: PREFIX_COMMIT.to_owned(),
        prefix_tree: PREFIX_TREE.to_owned(),
        occurrences,
        partitions,
        incrementally_mounted_octets: mounted_octets,
        whole_repository_semantic_materializations: 0,
    };
    chronology.validate().map_err(|error| error.to_string())?;
    Ok(chronology)
}
