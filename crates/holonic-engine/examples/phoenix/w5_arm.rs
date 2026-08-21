//! Authenticated ARM-N W5 receipt adapter.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use holonic_engine::exact_work::ExactWork;
use holonic_engine::phoenix::w5::{
    ApparatusUtility, Body, BodyObservation, BoundDeed, Calibrated, ExecutionKind,
    ExecutionWitness, Face, ReceiverReturn, SourceAccessWitness, WorkReceipt,
};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn unknown(reason: &str) -> Calibrated<BigUint> {
    Calibrated::Unknown {
        reason: reason.to_owned(),
    }
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_le_bytes());
    out.extend(bytes);
}
fn intervals_bytes(intervals: &[(i64, i64)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + intervals.len() * 16);
    out.extend((intervals.len() as u64).to_le_bytes());
    for (lo, hi) in intervals {
        out.extend(lo.to_le_bytes());
        out.extend(hi.to_le_bytes());
    }
    out
}
fn return_digest(faces: &[Face]) -> String {
    let mut bytes = Vec::new();
    for face in faces {
        frame(&mut bytes, face.name.as_bytes());
        frame(&mut bytes, face.material_digest.as_bytes());
        frame(&mut bytes, &intervals_bytes(&face.intervals));
    }
    digest(&bytes)
}
fn family_digest(names: &[String]) -> String {
    digest(&serde_json::to_vec(names).expect("receiver names serialize"))
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArmReceipt {
    schema: String,
    schema_version: String,
    rest_identity: ArmRestIdentity,
    codebook_identity: String,
    codebook_extent: u32,
    material_lineage_digest: String,
    closure_identity: String,
    current: ArmDeed,
    prior: ArmDeed,
    artifacts: Vec<ArmArtifact>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArmRestIdentity {
    sha256: String,
    extent: u64,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ArmDeed {
    deed_identity: String,
    faces: Vec<ArmFace>,
    return_digest: String,
    source_audit: ArmSourceAudit,
    exact_work: ExactWork,
    admission_digest: String,
    apparatus_prediction_digest: String,
    admission_json: String,
    owner_receipt_digest: String,
    execution_kind: String,
    device_name: String,
    mode: String,
    kernel_identity: String,
    launches: u64,
    synchronizations: u64,
    transfer_octets: u64,
    active_warps: String,
    energy: String,
    calibration: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ArmSourceAudit {
    audit_identity: String,
    forbidden: Vec<String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArmArtifact {
    role: String,
    locator: String,
    sha256: String,
    extent: u64,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArmDeedArtifact {
    schema: String,
    rest_identity: ArmRestIdentity,
    codebook_identity: String,
    codebook_extent: u32,
    material_lineage_digest: String,
    closure_identity: String,
    deed: ArmDeed,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct ArmFace {
    name: String,
    material_digest: String,
    intervals: Vec<(i64, i64)>,
}

impl ArmFace {
    fn into_face(self) -> Face {
        Face {
            name: self.name,
            material_digest: self.material_digest,
            intervals: self.intervals,
        }
    }
}

pub fn arm_n(path: &Path) -> Result<BodyObservation, String> {
    let bytes =
        fs::read(path).map_err(|error| format!("ARM N receipt {}: {error}", path.display()))?;
    let receipt: ArmReceipt =
        serde_json::from_slice(&bytes).map_err(|error| format!("ARM N receipt schema: {error}"))?;
    if receipt.schema != "holonic-engine.phoenix.w5-arm-n-return.v1"
        || receipt.schema_version != "v1"
        || receipt.rest_identity.sha256.len() != 64
        || receipt.rest_identity.extent == 0
        || receipt.codebook_identity.len() != 64
        || receipt.codebook_extent == 0
        || receipt.material_lineage_digest.len() != 64
        || receipt.closure_identity.len() != 64
        || receipt.current.deed_identity == receipt.prior.deed_identity
        || receipt.current.faces != receipt.prior.faces
        || receipt.current.return_digest != receipt.prior.return_digest
        || [&receipt.current, &receipt.prior].iter().any(|r| {
            r.deed_identity.is_empty()
                || r.execution_kind != "NativeRuntime"
                || r.device_name.is_empty()
                || r.mode.is_empty()
                || r.kernel_identity.is_empty()
                || r.active_warps != "Unknown"
                || r.energy != "Unknown"
                || r.admission_digest.len() != 64
                || r.apparatus_prediction_digest.len() != 64
                || r.owner_receipt_digest.len() != 64
                || r.admission_json.is_empty()
                || r.source_audit.audit_identity.is_empty()
                || !r.source_audit.forbidden.is_empty()
                || r.calibration.is_empty()
                || r.calibration
                    .get("coordinates")
                    .is_none_or(String::is_empty)
                || r.calibration
                    .get("active_warps")
                    .is_none_or(String::is_empty)
                || r.calibration.get("energy").is_none_or(String::is_empty)
                || return_digest(
                    &r.faces
                        .iter()
                        .cloned()
                        .map(ArmFace::into_face)
                        .collect::<Vec<_>>(),
                ) != r.return_digest
        })
    {
        return Err("ARM N receipt failed strict identity/return validation".to_owned());
    }
    for deed in [&receipt.current, &receipt.prior] {
        let owner_expected = digest(
            &serde_json::to_vec(&(
                deed.exact_work.clone(),
                deed.admission_digest.clone(),
                deed.return_digest.clone(),
            ))
            .map_err(|e| e.to_string())?,
        );
        if owner_expected != deed.owner_receipt_digest {
            return Err("ARM N owner work receipt digest drifted".to_owned());
        }
        if digest(deed.admission_json.as_bytes()) != deed.admission_digest {
            return Err("ARM N admission digest drifted".to_owned());
        }
    }
    if receipt
        .current
        .faces
        .iter()
        .any(|face| face.material_digest != receipt.material_lineage_digest)
        || receipt
            .prior
            .faces
            .iter()
            .any(|face| face.material_digest != receipt.material_lineage_digest)
    {
        return Err("ARM N material lineage differs across faces".to_owned());
    }
    verify_arm_artifacts(&receipt)?;
    let current = &receipt.current;
    let prior = &receipt.prior;
    let current_faces = current
        .faces
        .clone()
        .into_iter()
        .map(ArmFace::into_face)
        .collect::<Vec<_>>();
    let prior_faces = prior
        .faces
        .clone()
        .into_iter()
        .map(ArmFace::into_face)
        .collect::<Vec<_>>();
    let execution = |arm: &ArmDeed| ExecutionWitness {
        kind: ExecutionKind::NativeRuntime,
        deed_identity: arm.deed_identity.clone(),
        resident_owner: "p0-arm-n".to_owned(),
        returned_artifact_digest: arm.return_digest.clone(),
        source_access: SourceAccessWitness {
            audit_identity: arm.source_audit.audit_identity.clone(),
            forbidden: arm.source_audit.forbidden.clone(),
        },
    };
    let apparatus = arm_apparatus(current);
    let prior_apparatus = arm_apparatus(prior);
    let current_deed = BoundDeed {
        body: Body::ArmN,
        execution: execution(current),
        work: WorkReceipt {
            work: current.exact_work.clone(),
            admission_digest: current.admission_digest.clone(),
            admission_evidence: current.admission_json.clone(),
            returned_artifact_digest: current.return_digest.clone(),
            owner_receipt_digest: current.owner_receipt_digest.clone(),
        },
        apparatus,
    };
    let prior_deed = BoundDeed {
        body: Body::ArmN,
        execution: execution(prior),
        work: WorkReceipt {
            work: prior.exact_work.clone(),
            admission_digest: prior.admission_digest.clone(),
            admission_evidence: prior.admission_json.clone(),
            returned_artifact_digest: prior.return_digest.clone(),
            owner_receipt_digest: prior.owner_receipt_digest.clone(),
        },
        apparatus: prior_apparatus,
    };
    Ok(BodyObservation {
        body: Body::ArmN,
        body_digest: receipt.rest_identity.sha256.clone(),
        base_material_digest: receipt.material_lineage_digest.clone(),
        deed_closure_digest: receipt.closure_identity,
        source_closure_identity: receipt.rest_identity.sha256.clone(),
        codebook_digest: receipt.codebook_identity.clone(),
        codebook_extent: receipt.codebook_extent,
        receiver_family_digest: family_digest(
            &current_faces
                .iter()
                .map(|f| f.name.clone())
                .collect::<Vec<_>>(),
        ),
        base_return_digest: current.return_digest.clone(),
        faces: current_faces,
        return_digest: current.return_digest.clone(),
        deed: current_deed,
        base_replay_return_digest: prior.return_digest.clone(),
        base_replay_deed: prior_deed.clone(),
        interventions: Vec::new(),
        cultivation_delta_id: String::new(),
        prior_return: Some(prior_return(prior_faces, prior.return_digest.clone())),
        prior_deed: Some(prior_deed),
    })
}

fn arm_apparatus(deed: &ArmDeed) -> ApparatusUtility {
    let coordinates = deed
        .calibration
        .get("coordinates")
        .cloned()
        .expect("ARM receipt calibration was validated");
    let calibration = BTreeMap::from([
        (
            "launches".to_owned(),
            format!("{coordinates}; TransferCensus.deed_launches delta"),
        ),
        (
            "synchronizations".to_owned(),
            format!("{coordinates}; TransferCensus.synchronizations delta"),
        ),
        (
            "transfer_octets".to_owned(),
            format!("{coordinates}; ingress/egress/device-to-device deltas"),
        ),
        (
            "active_warps".to_owned(),
            deed.calibration
                .get("active_warps")
                .cloned()
                .expect("ARM active-warp calibration was validated"),
        ),
        (
            "energy".to_owned(),
            deed.calibration
                .get("energy")
                .cloned()
                .expect("ARM energy calibration was validated"),
        ),
    ]);
    let evidence = serde_json::to_string(deed).expect("ARM apparatus evidence serializes");
    ApparatusUtility {
        device_name: deed.device_name.clone(),
        mode: deed.mode.clone(),
        kernel_identity: deed.kernel_identity.clone(),
        launches: Calibrated::Known(BigUint::from(deed.launches)),
        synchronizations: Calibrated::Known(BigUint::from(deed.synchronizations)),
        transfer_octets: Calibrated::Known(BigUint::from(deed.transfer_octets)),
        active_warps: unknown("ARM N active warps not calibrated"),
        energy: unknown("ARM N energy not calibrated"),
        calibration,
        apparatus_evidence: evidence.clone(),
        apparatus_digest: digest(evidence.as_bytes()),
        returned_artifact_digest: deed.return_digest.clone(),
    }
}

fn verify_arm_artifacts(receipt: &ArmReceipt) -> Result<(), String> {
    if receipt.artifacts.is_empty() {
        return Err("ARM N artifact addresses are absent".to_owned());
    }
    let mut roles = std::collections::BTreeSet::new();
    for artifact in &receipt.artifacts {
        if artifact.role.is_empty()
            || artifact.locator.is_empty()
            || artifact.sha256.len() != 64
            || artifact.extent == 0
            || ["gemma", "corpus", "canon", "phoenix"]
                .iter()
                .any(|needle| artifact.locator.contains(needle))
            || !roles.insert(artifact.role.clone())
        {
            return Err("ARM N artifact address is incomplete".to_owned());
        }
        let bytes = fs::read(&artifact.locator)
            .map_err(|e| format!("ARM N artifact {}: {e}", artifact.locator))?;
        if bytes.len() as u64 != artifact.extent || digest(&bytes) != artifact.sha256 {
            return Err(format!("ARM N artifact {} drifted", artifact.locator));
        }
        match artifact.role.as_str() {
            "rest"
                if artifact.sha256 == receipt.rest_identity.sha256
                    && artifact.extent == receipt.rest_identity.extent => {}
            "executable" if artifact.sha256 == receipt.closure_identity => {}
            "prior-deed" => {
                let prior: ArmDeedArtifact = serde_json::from_slice(&bytes)
                    .map_err(|e| format!("ARM N prior deed artifact schema: {e}"))?;
                if prior.schema != "holonic-engine.phoenix.w5-arm-n-deed.v1"
                    || prior.rest_identity.sha256 != receipt.rest_identity.sha256
                    || prior.rest_identity.extent != receipt.rest_identity.extent
                    || prior.codebook_identity != receipt.codebook_identity
                    || prior.codebook_extent != receipt.codebook_extent
                    || prior.material_lineage_digest != receipt.material_lineage_digest
                    || prior.closure_identity != receipt.closure_identity
                    || prior.deed.deed_identity != receipt.prior.deed_identity
                    || prior.deed.return_digest != receipt.prior.return_digest
                {
                    return Err("ARM N prior deed artifact does not bind the receipt".to_owned());
                }
            }
            _ => {
                return Err(format!(
                    "ARM N artifact role {} is not authenticated",
                    artifact.role
                ));
            }
        }
    }
    let expected = ["rest", "executable", "prior-deed"]
        .into_iter()
        .map(str::to_owned)
        .collect::<std::collections::BTreeSet<_>>();
    if roles != expected {
        return Err("ARM N rest/executable/prior artifact roles are incomplete".to_owned());
    }
    Ok(())
}

fn prior_return(faces: Vec<Face>, digest: String) -> ReceiverReturn {
    ReceiverReturn { faces, digest }
}
