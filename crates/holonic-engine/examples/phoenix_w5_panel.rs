//! W5's resident returned-deed panel.
//!
//! This is deliberately an adapter, not a second Phoenix owner.  It mounts the authenticated
//! product once, conducts source and predecessor deeds before any cultivated deed, and constructs
//! the non-deserializable W5 input directly from owner returns.

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/streamed.rs"]
mod streamed;
#[path = "phoenix/tower.rs"]
mod tower;
#[path = "phoenix/w5_arm.rs"]
mod w5_arm;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_work::ExactWork;
use holonic_engine::phoenix::native_streamed::NativeMaterialSource;
use holonic_engine::phoenix::runtime::{OverlayAbsenceProof, ProductSession, RuntimeReceipt};
use holonic_engine::phoenix::streamed::{self as resident, MaterialSource, ReceiverOption, Site};
use holonic_engine::phoenix::tower::Intervention;
use holonic_engine::phoenix::w5::{
    self, AblationControlKind, ApparatusUtility, Body, BodyObservation, BoundDeed, Calibrated,
    CauseAblation, CodecVariantPath, ComponentEvidence, CondensationRemainder, ControlSpan,
    ExecutionKind, ExecutionWitness, Face, FourBodyInput, HeldOutBodyReturn, HeldOutCase,
    HeldOutKind, InterventionManifestRow, MatchedIntervention, NativeRecombinationReceipt,
    ReceiverReturn, SourceAccessWitness, SourceClosureAbsenceWitness, SourceNativeCorrespondence,
    WorkReceipt,
};
use holonic_engine::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};

const DEFAULT_PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const DEFAULT_SOURCE: &str = "/home/b/models/gemma-4-E4B-it";
const DEFAULT_ARM_N: &str = "output/the_native_baseline_conducts/arm-n-receipt.json";
const DEFAULT_OUT: &str = "output/the_phoenix_rebirth_is_graded/grade.json";
const TEXT: &str = "The capital of France is";

struct Args {
    product: PathBuf,
    source: PathBuf,
    arm_n: PathBuf,
    output: PathBuf,
    components: PathBuf,
    condensation: PathBuf,
    text: String,
    grain: u32,
    terms: u32,
    preflight: bool,
}

fn args() -> Args {
    let mut out = Args {
        product: PathBuf::from(DEFAULT_PRODUCT),
        source: PathBuf::from(DEFAULT_SOURCE),
        arm_n: PathBuf::from(DEFAULT_ARM_N),
        output: PathBuf::from(DEFAULT_OUT),
        components: PathBuf::from("output"),
        condensation: PathBuf::from(
            "output/the_lifted_body_condenses_only_where_future_receivers_factor/condensation.json",
        ),
        text: TEXT.to_owned(),
        grain: 48,
        terms: 14,
        preflight: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--product" => out.product = PathBuf::from(it.next().expect("--product <path>")),
            "--source" => out.source = PathBuf::from(it.next().expect("--source <path>")),
            "--arm-n-receipt" => {
                out.arm_n = PathBuf::from(it.next().expect("--arm-n-receipt <path>"))
            }
            "--arm-n" => out.arm_n = PathBuf::from(it.next().expect("--arm-n <path>")),
            "--output" => out.output = PathBuf::from(it.next().expect("--output <path>")),
            "--components" => {
                out.components = PathBuf::from(it.next().expect("--components <dir>"))
            }
            "--condensation" => {
                out.condensation = PathBuf::from(it.next().expect("--condensation <path>"))
            }
            "--text" => out.text = it.next().expect("--text <text>"),
            "--grain" => out.grain = it.next().expect("--grain <n>").parse().expect("grain"),
            "--terms" => out.terms = it.next().expect("--terms <n>").parse().expect("terms"),
            "--preflight" => out.preflight = true,
            other => panic!("unknown argument {other}"),
        }
    }
    out
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn lineage_digest(ids: &[u32]) -> String {
    digest(&serde_json::to_vec(ids).expect("input lineage serializes"))
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_le_bytes());
    out.extend(bytes);
}

fn interval_bytes(intervals: &[(i64, i64)]) -> Vec<u8> {
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
        frame(&mut bytes, &interval_bytes(&face.intervals));
    }
    digest(&bytes)
}

fn receiver(faces: Vec<Face>) -> ReceiverReturn {
    let digest = return_digest(&faces);
    ReceiverReturn { faces, digest }
}

fn family_digest(names: &[String]) -> String {
    digest(&serde_json::to_vec(names).expect("receiver names serialize"))
}

fn complete_faces(
    faces: &resident::ReceiverFaces,
    potential: Option<&[(i64, i64)]>,
    material_digest: &str,
) -> Vec<Face> {
    let mut result = Vec::with_capacity(faces.layers.len() * 3 + 2);
    for layer in &faces.layers {
        for (suffix, values) in [
            ("PLE", &layer.ple),
            ("contact", &layer.contact),
            ("enclosure", &layer.layer_return),
        ] {
            result.push(Face {
                name: format!("layer {} {suffix}", layer.layer),
                material_digest: material_digest.to_owned(),
                intervals: values.clone(),
            });
        }
    }
    result.push(Face {
        name: "final normed".to_owned(),
        material_digest: material_digest.to_owned(),
        intervals: faces.final_normed.clone(),
    });
    result.push(Face {
        name: "potential".to_owned(),
        material_digest: material_digest.to_owned(),
        intervals: potential.unwrap_or(&faces.potential).to_vec(),
    });
    result
}

#[derive(Clone)]
struct Deed {
    returned: ReceiverReturn,
    work: WorkReceipt,
    apparatus: ApparatusUtility,
    execution: ExecutionWitness,
    closure_digest: String,
    morphology_id: Option<String>,
}

fn known(value: u64, why: &str) -> Calibrated<BigUint> {
    let _ = why;
    Calibrated::Known(BigUint::from(value))
}

fn unknown(why: &str) -> Calibrated<BigUint> {
    Calibrated::Unknown {
        reason: why.to_owned(),
    }
}

fn live_descriptor_audit(forbidden: &[String]) -> String {
    let mut descriptors = fs::read_dir("/proc/self/fd")
        .ok()
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    descriptors.sort();
    digest(&serde_json::to_vec(&(descriptors, forbidden)).expect("descriptor audit serializes"))
}

fn classify_forbidden(admitted: &[String]) -> Vec<String> {
    fs::read_dir("/proc/self/fd")
        .ok()
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.to_string_lossy().into_owned())
        .filter(|path| {
            [
                "gemma",
                "corpus",
                "tokenizer.json",
                "/canon/",
                "/research/",
                "/blueprint/",
                "/examples/",
                ".gguf",
            ]
            .iter()
            .any(|needle| path.contains(needle))
                && !admitted.iter().any(|root| path.starts_with(root))
        })
        .collect()
}

fn transfer_delta(
    before: &holonic_engine::resident_section::TransferCensus,
    after: &holonic_engine::resident_section::TransferCensus,
) -> u64 {
    after.ingress_octets.saturating_sub(before.ingress_octets)
        + after
            .egress_section_octets
            .saturating_sub(before.egress_section_octets)
        + after
            .egress_receipt_octets
            .saturating_sub(before.egress_receipt_octets)
        + after
            .device_to_device_octets
            .saturating_sub(before.device_to_device_octets)
}

fn apparatus(
    surface: &ResidentSurface<'_>,
    census: &resident::ApparatusCensus,
    returned: &str,
) -> ApparatusUtility {
    let transfer = transfer_delta(&census.resident_before, &census.resident_after)
        + census.streamed.asynchronous_copy_octets;
    let sync = census.streamed.mount_synchronizations
        + census.streamed.staging_synchronizations
        + census.streamed.terminal_synchronizations;
    let evidence = serde_json::to_string(census).expect("apparatus census serializes");
    let mut calibration = BTreeMap::new();
    calibration.insert(
        "launches".to_owned(),
        "ApparatusCensus.total_deed_launches".to_owned(),
    );
    calibration.insert(
        "synchronizations".to_owned(),
        "StreamedCensus mount + staging + terminal synchronizations; TransferCensus terminal not added".to_owned(),
    );
    calibration.insert(
        "transfer_octets".to_owned(),
        "ApparatusCensus resident ingress/egress/device-to-device delta + streamed asynchronous_copy_octets".to_owned(),
    );
    calibration.insert(
        "active_warps".to_owned(),
        "unknown: no calibrated receiver".to_owned(),
    );
    calibration.insert(
        "energy".to_owned(),
        "unknown: no calibrated receiver".to_owned(),
    );
    ApparatusUtility {
        device_name: surface.device_name().to_owned(),
        mode: format!("{:?}", surface.mode()),
        kernel_identity: surface.ptx_sha256().to_owned(),
        launches: known(census.total_deed_launches, "total deed launches"),
        synchronizations: known(sync, "stream synchronizations"),
        transfer_octets: known(transfer, "transfers"),
        active_warps: unknown("active warps are not calibrated by this receipt"),
        energy: unknown("energy is not calibrated by this receipt"),
        calibration,
        apparatus_evidence: evidence.clone(),
        apparatus_digest: digest(evidence.as_bytes()),
        returned_artifact_digest: returned.to_owned(),
    }
}

fn work_receipt(work: ExactWork, admission_evidence: String, returned: &str) -> WorkReceipt {
    let admission_digest = digest(admission_evidence.as_bytes());
    let owner_receipt_digest = digest(
        &serde_json::to_vec(&(work.clone(), admission_digest.clone(), returned.to_owned()))
            .expect("work receipt serializes"),
    );
    WorkReceipt {
        work,
        admission_digest,
        admission_evidence,
        returned_artifact_digest: returned.to_owned(),
        owner_receipt_digest,
    }
}

fn deed_from_base(
    base: resident::Circulated,
    surface: &ResidentSurface<'_>,
    body: &str,
    deed_id: &str,
    forbidden: Vec<String>,
    material_digest: &str,
) -> Result<Deed, String> {
    let complete = base
        .receiver_faces
        .as_ref()
        .ok_or("complete receiver did not return faces")?;
    let returned = receiver(complete_faces(&complete, None, material_digest));
    let execution = ExecutionWitness {
        kind: ExecutionKind::ResidentGpu,
        deed_identity: digest(format!("{body}:{deed_id}:{:?}", base.graph_key).as_bytes()),
        resident_owner: "phoenix::streamed::circulation".to_owned(),
        returned_artifact_digest: returned.digest.clone(),
        source_access: SourceAccessWitness {
            audit_identity: live_descriptor_audit(&forbidden),
            forbidden,
        },
    };
    let work = work_receipt(
        base.tower_work.clone(),
        base.tower_admission.serialized.clone(),
        &returned.digest,
    );
    let apparatus = apparatus(surface, &base.apparatus_census(), &returned.digest);
    Ok(Deed {
        returned,
        work,
        apparatus,
        execution,
        closure_digest: digest(format!("{:?}", base.graph_key).as_bytes()),
        morphology_id: None,
    })
}

fn deed_from_cultivated(
    base: resident::CultivatedCirculated,
    receipt: &RuntimeReceipt,
    body: &str,
    deed_id: &str,
    material_digest: &str,
) -> Result<Deed, String> {
    let complete = base
        .base
        .receiver_faces
        .as_ref()
        .ok_or("complete W3 receiver did not return faces")?;
    let returned = receiver(complete_faces(
        &complete,
        Some(&base.cultivated_potential),
        material_digest,
    ));
    let execution = ExecutionWitness {
        kind: ExecutionKind::NativeRuntime,
        deed_identity: digest(
            format!(
                "{body}:{deed_id}:{}",
                base.overlay_execution.identity_sha256
            )
            .as_bytes(),
        ),
        resident_owner: "phoenix::runtime::ProductSession/cultivation".to_owned(),
        returned_artifact_digest: returned.digest.clone(),
        source_access: SourceAccessWitness {
            audit_identity: digest(
                &serde_json::to_vec(&(
                    receipt.source_access.product_root.clone(),
                    receipt.source_access.descriptors.clone(),
                    receipt.source_access.forbidden.clone(),
                ))
                .expect("runtime source audit serializes"),
            ),
            forbidden: receipt.source_access.forbidden.clone(),
        },
    };
    let composed_admission = serde_json::to_string(&(
        &base.base.tower_admission.deeds,
        base.overlay_admission.clone(),
    ))
    .map_err(|e| format!("W3 admission testimony: {e}"))?;
    let work = work_receipt(
        base.total_work.clone(),
        composed_admission,
        &returned.digest,
    );
    let census = base.apparatus_census();
    let transfer = transfer_delta(&census.resident_before, &census.resident_after)
        + census.streamed.asynchronous_copy_octets;
    let apparatus = ApparatusUtility {
        device_name: base.execution.device_name.clone(),
        mode: base.execution.mode.clone(),
        kernel_identity: base.execution.kernel_sha256.clone(),
        launches: known(
            base.total_deed_launches,
            "ApparatusCensus total_deed_launches",
        ),
        synchronizations: known(
            census.streamed.mount_synchronizations
                + census.streamed.staging_synchronizations
                + census.streamed.terminal_synchronizations,
            "StreamedCensus mount + staging + terminal; TransferCensus terminal excluded",
        ),
        transfer_octets: known(
            transfer,
            "ApparatusCensus resident delta + streamed async copies",
        ),
        active_warps: unknown("active warps are not calibrated by this receipt"),
        energy: unknown("energy is not calibrated by this receipt"),
        calibration: BTreeMap::from([
            (
                "launches".to_owned(),
                "ApparatusCensus.total_deed_launches".to_owned(),
            ),
            (
                "synchronizations".to_owned(),
                "StreamedCensus mount + staging + terminal; TransferCensus terminal excluded"
                    .to_owned(),
            ),
            (
                "transfer_octets".to_owned(),
                "resident ingress/egress/device-to-device + streamed asynchronous copies"
                    .to_owned(),
            ),
            (
                "active_warps".to_owned(),
                "unknown: no calibrated receiver".to_owned(),
            ),
            (
                "energy".to_owned(),
                "unknown: no calibrated receiver".to_owned(),
            ),
        ]),
        apparatus_evidence: serde_json::to_string(&census).expect("W3 apparatus census serializes"),
        apparatus_digest: String::new(),
        returned_artifact_digest: returned.digest.clone(),
    };
    let apparatus = ApparatusUtility {
        apparatus_digest: digest(apparatus.apparatus_evidence.as_bytes()),
        ..apparatus
    };
    Ok(Deed {
        returned,
        work,
        apparatus,
        execution,
        closure_digest: digest(
            &serde_json::to_vec(&(
                digest(format!("{:?}", base.base.graph_key).as_bytes()),
                base.overlay_execution.identity_sha256.clone(),
                receipt.morphology_identity.sha256.clone(),
                receipt.product_identity.sha256.clone(),
            ))
            .expect("W3 deed closure serializes"),
        ),
        morphology_id: Some(receipt.morphology_identity.sha256.clone()),
    })
}

fn run_w2(
    surface: &ResidentSurface<'_>,
    readout: &ResidentReadout,
    source: &mut dyn MaterialSource,
    ids: &[u32],
    grain: ResidentGrain,
    terms: SeriesAperture,
    site: Site,
    intervention: &Intervention,
    deed_id: &str,
    forbidden: Vec<String>,
    material_digest: &str,
) -> Result<Deed, String> {
    let base = resident::circulate_with_intervention(
        surface,
        readout,
        source,
        &ids.iter().map(|id| *id as usize).collect::<Vec<_>>(),
        grain,
        terms,
        tower::Chart::Midpoint,
        true,
        site,
        intervention,
        ReceiverOption::Complete,
    )?;
    deed_from_base(
        base,
        surface,
        "resident",
        deed_id,
        classify_forbidden(&forbidden),
        material_digest,
    )
}

fn run_w3(
    session: &ProductSession,
    text: &str,
    expected_ids: &[u32],
    material_digest: &str,
    site: Site,
    intervention: &Intervention,
    deed_id: &str,
) -> Result<Deed, String> {
    let source_ids = session.source_ids(expected_ids)?;
    let reconstructed = session.reconstruct_source_ids(&source_ids)?;
    if reconstructed.native_ids != expected_ids {
        return Err("W3 reconstructed native IDs differ from the expected occurrence".to_owned());
    }
    if session.encode(text)? != expected_ids {
        return Err("W3 runtime text crossed to unexpected native IDs".to_owned());
    }
    let result =
        session.infer_with_intervention(text, site, intervention, ReceiverOption::Complete)?;
    if result.receipt.input.native_ids != expected_ids {
        return Err("W3 runtime receipt native IDs differ from the expected occurrence".to_owned());
    }
    deed_from_cultivated(
        result.cultivated,
        &result.receipt,
        "w3",
        deed_id,
        material_digest,
    )
}

fn run_noop(
    session: &ProductSession,
    surface: &ResidentSurface<'_>,
    readout: &ResidentReadout,
    ids: &[u32],
    grain: ResidentGrain,
    terms: SeriesAperture,
    material_digest: &str,
) -> Result<Deed, String> {
    session
        .mounted()
        .verify_still()
        .map_err(|e| e.to_string())?;
    let mut deed = run_w2(
        surface,
        readout,
        &mut NativeMaterialSource::from_mounted(session.predecessor()),
        ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "product-predecessor-no-morphology",
        Vec::new(),
        material_digest,
    )?;
    deed.execution.kind = ExecutionKind::NoMorphologyControl;
    deed.execution.resident_owner = "ProductSession::predecessor/no-morphology-control".to_owned();
    session
        .mounted()
        .verify_still()
        .map_err(|e| e.to_string())?;
    Ok(deed)
}

fn panel(tokens: usize) -> Vec<(&'static str, Site, Intervention)> {
    vec![
        (
            "embedding-columns",
            Site::EveryLayer,
            Intervention::WithdrawEmbeddingColumns { from: 0, span: 256 },
        ),
        ("ple", Site::Layer(1), Intervention::WithdrawPle),
        (
            "pre-rebase-scale",
            Site::Layer(1),
            Intervention::ScaleBeforeInputRebase { by: 2 },
        ),
        (
            "post-rebase-scale",
            Site::Layer(1),
            Intervention::ScaleAfterInputRebase { by: 2 },
        ),
        (
            "identity-chronology",
            Site::Layer(1),
            Intervention::IdentityChronology,
        ),
        (
            "reversed-chronology",
            Site::Layer(1),
            Intervention::ReversedPositions,
        ),
        (
            "receiver-permutation",
            Site::Layer(1),
            Intervention::PermuteReceiverHeads { a: 0, b: 1 },
        ),
        (
            "receiver-scale",
            Site::Layer(1),
            Intervention::ScaleReceiver { by: 2 },
        ),
        (
            "own-kv",
            Site::Layer(1),
            Intervention::WithdrawKvFamily { family: 0 },
        ),
        (
            "stored-kv",
            Site::Layer(22),
            Intervention::WithdrawKvFamily { family: 0 },
        ),
        (
            "shared-kv",
            Site::Layer(24),
            Intervention::WithdrawSharedKvFamily { family: 0 },
        ),
        (
            "carried-permutation",
            Site::Layer(1),
            Intervention::PermuteCarriedHeads { a: 0, b: 1 },
        ),
        (
            "residual-reentry",
            Site::Layer(1),
            Intervention::WithdrawResidualAtFirstReEntry,
        ),
        (
            "gate-span",
            Site::Layer(1),
            Intervention::WithdrawGateSpan {
                from: 0,
                span: tower::HIDDEN,
            },
        ),
        (
            "one-key-full-chronology",
            Site::Layer(5),
            Intervention::KeepOnlyLastKeyPosition { tokens },
        ),
        (
            "final-span",
            Site::Final,
            Intervention::WithdrawFinalSpan { from: 0, span: 256 },
        ),
    ]
}

fn law_digest(row: &str, site: Site, intervention: &Intervention) -> String {
    digest(format!("{row}|{site:?}|{intervention:?}").as_bytes())
}

fn manifest(tokens: usize) -> Vec<InterventionManifestRow> {
    panel(tokens)
        .into_iter()
        .enumerate()
        .map(
            |(index, (row, site, intervention))| InterventionManifestRow {
                id: row.to_owned(),
                site: format!("{site:?}"),
                law_digest: law_digest(row, site, &intervention),
                pre_intervention_prefix: [0, 3, 3, 3, 3, 3, 3, 3, 3, 66, 72, 3, 3, 3, 15, 126]
                    [index],
                requires_separation: index != 2,
                order_face_control: index == 2,
                exact_control_span: if matches!(index, 4 | 6 | 7 | 11) {
                    Some(ControlSpan {
                        face_index: 5,
                        start: 0,
                        extent: tower::HIDDEN,
                    })
                } else {
                    None
                },
                unseparated_control_span: (index == 5).then_some(ControlSpan {
                    face_index: 5,
                    start: 0,
                    extent: tower::HIDDEN,
                }),
            },
        )
        .collect()
}

fn matched(
    body: Body,
    row: &InterventionManifestRow,
    before: &Deed,
    after: &Deed,
) -> Result<MatchedIntervention, String> {
    let declaration = format!("{}:{}:{}", row.id, row.site, row.law_digest);
    Ok(MatchedIntervention {
        body,
        row_id: row.id.clone(),
        site: row.site.clone(),
        law_digest: row.law_digest.clone(),
        pre_intervention_prefix: row.pre_intervention_prefix,
        before: before.returned.clone(),
        after: after.returned.clone(),
        deed: BoundDeed {
            body,
            execution: after.execution.clone(),
            work: after.work.clone(),
            apparatus: after.apparatus.clone(),
        },
        intervention_occurrence_digest: digest(
            format!("{declaration}|{}", after.execution.deed_identity).as_bytes(),
        ),
        order_face_before_digest: order_face_digest(&before.returned)?,
        order_face_after_digest: order_face_digest(&after.returned)?,
    })
}

fn order_face_digest(returned: &ReceiverReturn) -> Result<String, String> {
    let potential = returned
        .faces
        .last()
        .ok_or("receiver return has no potential face")?;
    if potential.intervals.is_empty() || potential.intervals.len() % tower::VOCABULARY != 0 {
        return Err("potential face is not row-addressable by the vocabulary".to_owned());
    }
    let row = &potential.intervals[potential.intervals.len() - tower::VOCABULARY..];
    let top_lower = row
        .iter()
        .map(|(lower, _)| *lower)
        .max()
        .ok_or("terminal potential row is empty")?;
    let plural = row
        .iter()
        .enumerate()
        .filter_map(|(id, (_, upper))| (*upper >= top_lower).then_some(id))
        .collect::<Vec<_>>();
    let mut ordered = row
        .iter()
        .enumerate()
        .map(|(id, (lower, _))| (id, *lower))
        .collect::<Vec<_>>();
    ordered.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
    ordered.truncate(16);
    let top_ids = ordered.into_iter().map(|(id, _)| id).collect::<Vec<_>>();
    Ok(digest(
        &serde_json::to_vec(&(plural, top_ids)).expect("order face serializes"),
    ))
}

fn observation(
    body: Body,
    body_digest: &str,
    material_digest: &str,
    codebook_digest: &str,
    codebook_extent: u32,
    base: Deed,
    replay: Deed,
    interventions: Vec<MatchedIntervention>,
    cultivation_delta_id: String,
    source_closure_identity: &str,
) -> BodyObservation {
    BodyObservation {
        body,
        body_digest: body_digest.to_owned(),
        base_material_digest: material_digest.to_owned(),
        deed_closure_digest: base.closure_digest,
        source_closure_identity: source_closure_identity.to_owned(),
        codebook_digest: codebook_digest.to_owned(),
        codebook_extent,
        receiver_family_digest: family_digest(
            &base
                .returned
                .faces
                .iter()
                .map(|f| f.name.clone())
                .collect::<Vec<_>>(),
        ),
        base_return_digest: base.returned.digest.clone(),
        faces: base.returned.faces.clone(),
        return_digest: base.returned.digest.clone(),
        deed: BoundDeed {
            body,
            execution: base.execution,
            work: base.work,
            apparatus: base.apparatus,
        },
        base_replay_return_digest: replay.returned.digest,
        base_replay_deed: BoundDeed {
            body,
            execution: replay.execution,
            work: replay.work,
            apparatus: replay.apparatus,
        },
        interventions,
        cultivation_delta_id,
        prior_return: None,
        prior_deed: None,
    }
}

fn held_case(
    kind: HeldOutKind,
    source_ids: &[u32],
    foreign: Deed,
    w2: Deed,
    w3: Deed,
    baseline: &str,
) -> HeldOutCase {
    let lineage_digest = digest(&serde_json::to_vec(source_ids).expect("held-out ids serialize"));
    let lineage_for_inputs = lineage_digest.clone();
    let input_lineage = |body: Body| digest(format!("{lineage_for_inputs}:{:?}", body).as_bytes());
    HeldOutCase {
        kind,
        lineage_digest,
        input_baseline_digest: baseline.to_owned(),
        returns: vec![
            HeldOutBodyReturn {
                body: Body::ForeignSource,
                input_lineage_digest: input_lineage(Body::ForeignSource),
                returned: foreign.returned,
                deed: BoundDeed {
                    body: Body::ForeignSource,
                    execution: foreign.execution,
                    work: foreign.work,
                    apparatus: foreign.apparatus,
                },
            },
            HeldOutBodyReturn {
                body: Body::W2Predecessor,
                input_lineage_digest: input_lineage(Body::W2Predecessor),
                returned: w2.returned,
                deed: BoundDeed {
                    body: Body::W2Predecessor,
                    execution: w2.execution,
                    work: w2.work,
                    apparatus: w2.apparatus,
                },
            },
            HeldOutBodyReturn {
                body: Body::W3Cultivated,
                input_lineage_digest: input_lineage(Body::W3Cultivated),
                returned: w3.returned,
                deed: BoundDeed {
                    body: Body::W3Cultivated,
                    execution: w3.execution,
                    work: w3.work,
                    apparatus: w3.apparatus,
                },
            },
        ],
        codec_paths: Vec::new(),
    }
}

fn bound_deed(body: Body, deed: &Deed) -> BoundDeed {
    BoundDeed {
        body,
        execution: deed.execution.clone(),
        work: deed.work.clone(),
        apparatus: deed.apparatus.clone(),
    }
}

fn prefix_return(deed: &Deed, faces: usize) -> ReceiverReturn {
    receiver(deed.returned.faces.iter().take(faces).cloned().collect())
}

fn component_ledger(
    root: &Path,
    arm_path: &Path,
    native_rest_digest: &str,
) -> Result<Vec<ComponentEvidence>, String> {
    let paths = [
        (
            "w1-source-manifest",
            "the_whole_foreign_map_crosses_into_native_rest/w1_receipt.json",
        ),
        (
            "w1-potential-active-atlas-rest",
            "the_whole_foreign_map_crosses_into_native_rest/operation_correspondence.json",
        ),
        (
            "station-d-source-dissection",
            "the_source_is_dissected/dissection-5-tokens-grain-48-terms-14.form",
        ),
        (
            "station-d-nontext-control",
            "the_source_is_dissected/vision-soft-tokens.tsv",
        ),
        (
            "w2-correspondence-condensation",
            "the_lifted_body_condenses_only_where_future_receivers_factor/condensation.json",
        ),
        (
            "w3-cultivation-rank-adjoint-rest",
            "the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/receipt.json",
        ),
        (
            "w4-application-fresh-inference",
            "the_application_infers_from_the_cultivated_phoenix_rest_on_the_card/receipt.json",
        ),
    ];
    let mut paths = paths
        .into_iter()
        .map(|(row, path)| (row, root.join(path)))
        .collect::<Vec<_>>();
    paths.push(("p0-arm-n", arm_path.to_owned()));
    let expected_schema = |row_id: &str| match row_id {
        "w1-source-manifest" => "holonic-engine.phoenix.w1-receipt.v1",
        "w1-potential-active-atlas-rest" => "holonic-engine.operation-correspondence.v1",
        "station-d-source-dissection" => "holonic-engine.phoenix.source-dissection.form.v1",
        "station-d-nontext-control" => "holonic-engine.phoenix.vision-projection.tsv.v1",
        "w2-correspondence-condensation" => "holonic-engine.phoenix.w2-structural-condensation.v1",
        "w3-cultivation-rank-adjoint-rest" => "holonic-engine.phoenix.w3-receipt.v1",
        "w4-application-fresh-inference" => "holonic-engine.phoenix.w4-fresh-process.v1",
        "p0-arm-n" => "holonic-engine.phoenix.w5-arm-n-return.v1",
        _ => unreachable!(),
    };
    paths
        .into_iter()
        .map(|(row_id, relative)| {
            let bytes = fs::read(&relative)
                .map_err(|e| format!("component {row_id} {}: {e}", relative.display()))?;
            let schema = expected_schema(row_id).to_owned();
            if row_id.ends_with("receipt")
                || row_id == "w1-source-manifest"
                || row_id == "w1-potential-active-atlas-rest"
                || row_id == "w2-correspondence-condensation"
                || row_id == "w3-cultivation-rank-adjoint-rest"
                || row_id == "w4-application-fresh-inference"
                || row_id == "p0-arm-n"
            {
                let value: serde_json::Value = serde_json::from_slice(&bytes)
                    .map_err(|e| format!("component {row_id} JSON schema: {e}"))?;
                if row_id != "w1-source-manifest"
                    && value.get("schema").and_then(serde_json::Value::as_str)
                        != Some(schema.as_str())
                {
                    return Err(format!("component {row_id} declared schema differs"));
                }
                if row_id == "w1-source-manifest"
                    && value
                        .get("rest_sha256")
                        .and_then(serde_json::Value::as_str)
                        .map_or(true, |v| v != native_rest_digest)
                {
                    return Err("W1 receipt lacks canonical rest identity".to_owned());
                }
            }
            Ok(ComponentEvidence {
                row_id: row_id.to_owned(),
                artifact_identity: digest(&bytes),
                extent: bytes.len() as u64,
                schema,
            })
        })
        .collect()
}

fn condensation(path: &Path, enlarged: Vec<String>) -> Result<CondensationRemainder, String> {
    let bytes = fs::read(path).map_err(|e| format!("condensation {}: {e}", path.display()))?;
    let value: serde_json::Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if value.get("schema").and_then(serde_json::Value::as_str)
        != Some("holonic-engine.phoenix.w2-structural-condensation.v1")
    {
        return Err("condensation schema is not the authenticated W2 artifact".to_owned());
    }
    let prior = value
        .get("receiver_atlases")
        .and_then(serde_json::Value::as_array)
        .ok_or("condensation receiver testimony")?;
    let prior_names = prior
        .iter()
        .filter_map(|v| {
            v.get("name")
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
        })
        .collect::<Vec<_>>();
    let mut enlarged = prior_names
        .clone()
        .into_iter()
        .chain(enlarged)
        .collect::<Vec<_>>();
    enlarged.sort();
    enlarged.dedup();
    let separators = value
        .get("no_factor")
        .and_then(serde_json::Value::as_array)
        .ok_or("condensation no-factor testimony")?;
    if separators.len() != 4 {
        return Err(
            "condensation no-factor testimony is not the complete four-entry family".to_owned(),
        );
    }
    let retained = separators
        .iter()
        .map(|v| serde_json::to_vec(v).expect("separator serializes"))
        .collect::<Vec<_>>();
    if prior_names.is_empty() || retained.is_empty() {
        return Err("condensation has no prior receiver/separator testimony".to_owned());
    }
    let candidates = separators
        .iter()
        .flat_map(|entry| {
            entry
                .get("candidate")
                .and_then(serde_json::Value::as_array)
                .into_iter()
                .flatten()
        })
        .filter_map(serde_json::Value::as_str)
        .collect::<std::collections::BTreeSet<_>>();
    let prior_collapsed = candidates.len() as u64;
    let enlarged_collapsed = 0u64;
    let open = separators
        .iter()
        .map(|entry| serde_json::to_string(entry).expect("no-factor witness serializes"))
        .collect::<Vec<_>>();
    let refinement_digest = digest(
        &serde_json::to_vec(&(
            digest(&bytes),
            prior_names.clone(),
            enlarged.clone(),
            BigUint::from(prior_collapsed),
            BigUint::from(enlarged_collapsed),
            retained.clone(),
            open.clone(),
        ))
        .expect("condensation receipt serializes"),
    );
    Ok(CondensationRemainder {
        prior_artifact_digest: digest(&bytes),
        prior_receiver_family: prior_names,
        enlarged_receiver_family: enlarged,
        prior_collapsed_population: BigUint::from(prior_collapsed),
        enlarged_collapsed_population: BigUint::from(enlarged_collapsed),
        retained_separators: retained,
        open_fibres: open,
        refinement_digest,
    })
}

fn main() -> Result<(), String> {
    let args = args();
    let session = ProductSession::open(&args.product)?;
    let arm = w5_arm::arm_n(&args.arm_n)?;
    w5::validate_body_observation(&arm).map_err(|error| error.to_string())?;
    let components = component_ledger(
        &args.components,
        &args.arm_n,
        &session.predecessor().content_identity().sha256,
    )?;
    let expected_receiver_names = (0..tower::LAYERS)
        .flat_map(|layer| {
            [
                format!("layer {layer} PLE"),
                format!("layer {layer} contact"),
                format!("layer {layer} enclosure"),
            ]
        })
        .chain(["final normed".to_owned(), "potential".to_owned()])
        .collect::<Vec<_>>();
    let condensation = condensation(
        &args.condensation,
        expected_receiver_names
            .iter()
            .cloned()
            .chain([
                "cultivated potential".to_owned(),
                "overlay return".to_owned(),
            ])
            .collect(),
    )?;
    if args.preflight {
        println!(
            "W5 preflight passed: {} component artifacts, ARM N {}, {} prior receiver faces, {} retained no-factor witnesses",
            components.len(),
            arm.return_digest,
            condensation.prior_receiver_family.len(),
            condensation.retained_separators.len(),
        );
        return Ok(());
    }
    let native_ids = session.encode(&args.text)?;
    let source_ids = session.source_ids(&native_ids)?;
    let base_material_digest = lineage_digest(&source_ids);
    let readout = ResidentReadout::new().map_err(|e| format!("resident card: {e:?}"))?;
    let surface = ResidentSurface::on(&readout).map_err(|e| format!("resident surface: {e:?}"))?;
    let grain = ResidentGrain(args.grain);
    let terms = SeriesAperture(args.terms);
    let foreign_name = args.source.to_string_lossy().into_owned();

    // Source deeds are completed and their source handle is dropped before W2/W3.  W2 deeds are
    // likewise completed and dropped before the first W3 call.
    println!("W5 phase 1/6: foreign base, replay, and 16 interventions");
    let mut foreign_source = streamed::ForeignMaterialSource::open(&foreign_name, None)?;
    let foreign_base = run_w2(
        &surface,
        &readout,
        &mut foreign_source,
        &source_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "base",
        vec![foreign_name.clone()],
        &base_material_digest,
    )?;
    let mut foreign_panel = Vec::new();
    for (row, site, intervention) in panel(native_ids.len()) {
        foreign_panel.push(run_w2(
            &surface,
            &readout,
            &mut foreign_source,
            &source_ids,
            grain,
            terms,
            site,
            &intervention,
            row,
            vec![foreign_name.clone()],
            &base_material_digest,
        )?);
    }
    let foreign_replay = run_w2(
        &surface,
        &readout,
        &mut foreign_source,
        &source_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "base-replay",
        vec![foreign_name.clone()],
        &base_material_digest,
    )?;
    drop(foreign_source);

    println!("W5 phase 2/6: W2 base, replay, and 16 interventions");
    let mut w2_source = NativeMaterialSource::from_mounted(session.predecessor());
    let w2_base = run_w2(
        &surface,
        &readout,
        &mut w2_source,
        &native_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "base",
        Vec::new(),
        &base_material_digest,
    )?;
    let mut w2_panel = Vec::new();
    for (row, site, intervention) in panel(native_ids.len()) {
        w2_panel.push(run_w2(
            &surface,
            &readout,
            &mut w2_source,
            &native_ids,
            grain,
            terms,
            site,
            &intervention,
            row,
            Vec::new(),
            &base_material_digest,
        )?);
    }
    let w2_replay = run_w2(
        &surface,
        &readout,
        &mut w2_source,
        &native_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "base-replay",
        Vec::new(),
        &base_material_digest,
    )?;
    drop(w2_source);

    println!("W5 phase 3/6: W3 base, replay, and 16 interventions");
    let w3_base = run_w3(
        &session,
        &args.text,
        &native_ids,
        &base_material_digest,
        Site::Nowhere,
        &Intervention::None,
        "base",
    )?;
    let w3_replay = run_w3(
        &session,
        &args.text,
        &native_ids,
        &base_material_digest,
        Site::Nowhere,
        &Intervention::None,
        "base-replay",
    )?;
    let mut w3_panel = Vec::new();
    for (row, site, intervention) in panel(native_ids.len()) {
        w3_panel.push(run_w3(
            &session,
            &args.text,
            &native_ids,
            &base_material_digest,
            site,
            &intervention,
            row,
        )?);
    }
    let manifest = manifest(native_ids.len());
    let mut f_interventions = Vec::new();
    let mut w2_interventions = Vec::new();
    let mut w3_interventions = Vec::new();
    for index in 0..manifest.len() {
        f_interventions.push(matched(
            Body::ForeignSource,
            &manifest[index],
            &foreign_base,
            &foreign_panel[index],
        )?);
        w2_interventions.push(matched(
            Body::W2Predecessor,
            &manifest[index],
            &w2_base,
            &w2_panel[index],
        )?);
        w3_interventions.push(matched(
            Body::W3Cultivated,
            &manifest[index],
            &w3_base,
            &w3_panel[index],
        )?);
    }
    let codebook = session.source_native_correspondence();
    let receiver_names = w2_base
        .returned
        .faces
        .iter()
        .map(|f| f.name.clone())
        .collect::<Vec<_>>();
    let receiver_digest = family_digest(&receiver_names);
    let correspondence = SourceNativeCorrespondence {
        source_codebook_digest: session.source_codec_identity().to_owned(),
        native_codebook_digest: session.codebook_digest().to_owned(),
        source_extent: codebook.source_extent,
        native_extent: codebook.native_extent,
        source_to_native: codebook.source_to_native,
        unresolved_source: codebook.unresolved_source,
        receiver_names: receiver_names.clone(),
        receiver_family_digest: receiver_digest,
        relation_digest: digest(
            &serde_json::to_vec(&(
                session.source_codec_identity(),
                session.codebook_digest(),
                codebook.source_extent,
                codebook.native_extent,
                session.source_native_rows(),
                session.unresolved_source_ids(),
                receiver_names.clone(),
                family_digest(&receiver_names),
            ))
            .expect("correspondence serializes"),
        ),
    };
    let foreign_body_digest = session
        .predecessor()
        .source()
        .container_content_sha256
        .clone()
        .ok_or("W1 predecessor has no authenticated foreign container identity")?;
    let source_closure_identity = session.source_closure_identity().digest;
    let foreign_observation = observation(
        Body::ForeignSource,
        &foreign_body_digest,
        &base_material_digest,
        &correspondence.source_codebook_digest,
        correspondence.source_extent,
        foreign_base.clone(),
        foreign_replay,
        f_interventions,
        String::new(),
        &source_closure_identity,
    );
    let w2_observation = observation(
        Body::W2Predecessor,
        &session.predecessor().content_identity().sha256,
        &base_material_digest,
        &correspondence.native_codebook_digest,
        correspondence.native_extent,
        w2_base.clone(),
        w2_replay,
        w2_interventions,
        String::new(),
        &source_closure_identity,
    );
    let cultivation_delta_id = w3_base
        .morphology_id
        .clone()
        .ok_or("W3 runtime did not return authenticated morphology identity")?;
    let w3_observation = observation(
        Body::W3Cultivated,
        &session.mounted().product_identity().sha256,
        &base_material_digest,
        &correspondence.native_codebook_digest,
        correspondence.native_extent,
        w3_base.clone(),
        w3_replay,
        w3_interventions,
        cultivation_delta_id.clone(),
        &source_closure_identity,
    );
    w5::validate_lifted_panel(
        &correspondence,
        &manifest,
        &foreign_observation,
        &w2_observation,
        &w3_observation,
    )
    .map_err(|error| error.to_string())?;
    println!("  common base/replay/intervention grade passed");

    let held_ids = [
        (HeldOutKind::StructuralChanged, vec![1509, 563, 506, 15374]),
        (
            HeldOutKind::SubjectDisjointUnchanged,
            vec![236776, 3761, 5192, 563, 614, 19396],
        ),
        (HeldOutKind::NoOp, vec![818, 4187, 563, 506, 9199]),
        (HeldOutKind::MatchedFoil, vec![818, 9199, 4187, 563, 506]),
    ];
    let mut held_out = Vec::new();
    let mut structural_lineage = String::new();
    println!("W5 phase 4/6: four held-out material arms");
    for (kind, ids) in held_ids {
        println!("  held-out {kind:?}");
        let reconstructed = session.reconstruct_source_ids(&ids)?;
        let mapped = reconstructed.native_ids.clone();
        let mut foreign_source = streamed::ForeignMaterialSource::open(&foreign_name, None)?;
        let foreign = run_w2(
            &surface,
            &readout,
            &mut foreign_source,
            &ids,
            grain,
            terms,
            Site::Nowhere,
            &Intervention::None,
            "held",
            vec![foreign_name.clone()],
            &lineage_digest(&ids),
        )?;
        drop(foreign_source);
        let mut w2_source = NativeMaterialSource::from_mounted(session.predecessor());
        let w2 = run_w2(
            &surface,
            &readout,
            &mut w2_source,
            &mapped,
            grain,
            terms,
            Site::Nowhere,
            &Intervention::None,
            "held",
            Vec::new(),
            &lineage_digest(&ids),
        )?;
        drop(w2_source);
        let w3 = if kind == HeldOutKind::NoOp {
            run_noop(
                &session,
                &surface,
                &readout,
                &mapped,
                grain,
                terms,
                &lineage_digest(&ids),
            )?
        } else {
            run_w3(
                &session,
                &reconstructed.surface,
                &mapped,
                &lineage_digest(&ids),
                Site::Nowhere,
                &Intervention::None,
                "held",
            )?
        };
        let baseline = if matches!(
            kind,
            HeldOutKind::NoOp | HeldOutKind::SubjectDisjointUnchanged
        ) {
            w2.returned.digest.clone()
        } else {
            w2_base.returned.digest.clone()
        };
        let case = held_case(kind, &ids, foreign, w2, w3, &baseline);
        if kind == HeldOutKind::StructuralChanged {
            structural_lineage = case.lineage_digest.clone();
        }
        held_out.push(case);
    }
    let codec_source_ids = [818, 4187, 563, 506, 9199];
    println!("W5 phase 5/6: codec-variant body returns");
    let codec_sequence = session.reconstruct_source_ids(&codec_source_ids)?;
    let codec_material = lineage_digest(&codec_source_ids);
    let mut codec_foreign_source = streamed::ForeignMaterialSource::open(&foreign_name, None)?;
    let codec_foreign = run_w2(
        &surface,
        &readout,
        &mut codec_foreign_source,
        &codec_source_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "codec-foreign",
        vec![foreign_name.clone()],
        &codec_material,
    )?;
    drop(codec_foreign_source);
    let codec_w2 = run_w2(
        &surface,
        &readout,
        &mut NativeMaterialSource::from_mounted(session.predecessor()),
        &codec_sequence.native_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "codec-w2",
        Vec::new(),
        &codec_material,
    )?;
    let codec_w3 = run_w3(
        &session,
        &codec_sequence.surface,
        &codec_sequence.native_ids,
        &codec_material,
        Site::Nowhere,
        &Intervention::None,
        "codec-w3",
    )?;
    let codec_lineage = codec_material.clone();
    held_out.push(HeldOutCase {
        kind: HeldOutKind::CodecVariant,
        lineage_digest: codec_lineage,
        input_baseline_digest: codec_w2.returned.digest.clone(),
        returns: vec![
            HeldOutBodyReturn {
                body: Body::ForeignSource,
                input_lineage_digest: digest(
                    &serde_json::to_vec(&(codec_material.clone(), session.source_codec_identity()))
                        .expect("codec lineage serializes"),
                ),
                returned: codec_foreign.returned.clone(),
                deed: bound_deed(Body::ForeignSource, &codec_foreign),
            },
            HeldOutBodyReturn {
                body: Body::W2Predecessor,
                input_lineage_digest: digest(
                    &serde_json::to_vec(&(codec_material.clone(), session.codebook_digest()))
                        .expect("codec lineage serializes"),
                ),
                returned: codec_w2.returned.clone(),
                deed: bound_deed(Body::W2Predecessor, &codec_w2),
            },
            HeldOutBodyReturn {
                body: Body::W3Cultivated,
                input_lineage_digest: digest(
                    &serde_json::to_vec(&(
                        codec_material.clone(),
                        codec_w3.execution.deed_identity.clone(),
                    ))
                    .expect("codec lineage serializes"),
                ),
                returned: codec_w3.returned.clone(),
                deed: bound_deed(Body::W3Cultivated, &codec_w3),
            },
        ],
        codec_paths: vec![
            CodecVariantPath {
                path_identity: session.source_codec_identity().to_owned(),
                token_word_digest: digest(
                    &serde_json::to_vec(&codec_sequence.native_ids).expect("tokens serialize"),
                ),
            },
            CodecVariantPath {
                path_identity: format!("pretokenized:{}", session.codebook_digest()),
                token_word_digest: digest(
                    &serde_json::to_vec(&codec_sequence.native_ids).expect("tokens serialize"),
                ),
            },
        ],
    });
    w5::validate_held_out_panel(
        &held_out,
        &foreign_observation,
        &w2_observation,
        &w3_observation,
    )
    .map_err(|error| error.to_string())?;
    println!("  held-out/codec grade passed");

    let structural_ids = [1509, 563, 506, 15374];
    println!("W5 phase 6/6: structural recombination and cause/delta ablations");
    let structural_sequence = session.reconstruct_source_ids(&structural_ids)?;
    let structural_material = lineage_digest(&structural_ids);
    let subject_control = held_out
        .iter()
        .find(|case| case.kind == HeldOutKind::SubjectDisjointUnchanged)
        .ok_or("subject-disjoint held-out control is absent")?;
    let subject_material = subject_control.lineage_digest.clone();
    let subject_w3_control = subject_control
        .returns
        .iter()
        .find(|returned| returned.body == Body::W3Cultivated)
        .cloned()
        .ok_or("subject-disjoint W3 control is absent")?;
    let subject_w2_control = subject_control
        .returns
        .iter()
        .find(|returned| returned.body == Body::W2Predecessor)
        .cloned()
        .ok_or("subject-disjoint W2 control is absent")?;
    let structural_w2 = run_w2(
        &surface,
        &readout,
        &mut NativeMaterialSource::from_mounted(session.predecessor()),
        &structural_sequence.native_ids,
        grain,
        terms,
        Site::Nowhere,
        &Intervention::None,
        "structural-recombined-w2",
        Vec::new(),
        &structural_material,
    )?;
    let structural_w3 = run_w3(
        &session,
        &structural_sequence.surface,
        &structural_sequence.native_ids,
        &structural_material,
        Site::Nowhere,
        &Intervention::None,
        "structural-recombined-w3",
    )?;
    let ple_ablation = run_w3(
        &session,
        &structural_sequence.surface,
        &structural_sequence.native_ids,
        &structural_material,
        Site::Layer(1),
        &Intervention::WithdrawPle,
        "structural-ple-ablation",
    )?;
    let ple_restore = run_w3(
        &session,
        &structural_sequence.surface,
        &structural_sequence.native_ids,
        &structural_material,
        Site::Nowhere,
        &Intervention::None,
        "structural-ple-restoration",
    )?;
    let residual_ablation = run_w3(
        &session,
        &structural_sequence.surface,
        &structural_sequence.native_ids,
        &structural_material,
        Site::Layer(1),
        &Intervention::WithdrawResidualAtFirstReEntry,
        "structural-residual-ablation",
    )?;
    let residual_restore = run_w3(
        &session,
        &structural_sequence.surface,
        &structural_sequence.native_ids,
        &structural_material,
        Site::Nowhere,
        &Intervention::None,
        "structural-residual-restoration",
    )?;
    let baseline = structural_w2.returned.clone();
    let recombined = structural_w3.returned.clone();
    let causes = vec![
        manifest[1].law_digest.clone(),
        manifest[12].law_digest.clone(),
    ];
    let absence: OverlayAbsenceProof =
        session.overlay_absence_proof(&session.prepare(&structural_sequence.native_ids)?)?;
    let absence_witness = SourceClosureAbsenceWitness {
        source_closure_identity: absence.source_closure_identity.clone(),
        overlay_topology_absent: absence.overlay_topology_absent,
        absent_overlay_operation_ids: absence.overlay_operations_absent,
        absent_factor_populations: absence.factor_populations_absent,
        held_out_difference_digest: digest(
            &serde_json::to_vec(&(baseline.digest.clone(), recombined.digest.clone()))
                .expect("held-out difference serializes"),
        ),
        witness_digest: String::new(),
    };
    let mut absence_witness = absence_witness;
    absence_witness.witness_digest = digest(
        &serde_json::to_vec(&(
            absence_witness.source_closure_identity.clone(),
            absence_witness.overlay_topology_absent,
            absence_witness.absent_overlay_operation_ids.clone(),
            absence_witness.absent_factor_populations.clone(),
            absence_witness.held_out_difference_digest.clone(),
        ))
        .expect("absence serializes"),
    );
    let cause_ablations = vec![
        CauseAblation {
            cause_id: causes[0].clone(),
            intervention_row_id: manifest[1].id.clone(),
            input_lineage_digest: structural_material.clone(),
            control_kind: AblationControlKind::CausalPrefix,
            before: recombined.clone(),
            ablated: ple_ablation.returned.clone(),
            restored: ple_restore.returned.clone(),
            deeds: vec![
                bound_deed(Body::W3Cultivated, &structural_w3),
                bound_deed(Body::W3Cultivated, &ple_ablation),
                bound_deed(Body::W3Cultivated, &ple_restore),
            ],
            control_input_lineage_digest: structural_material.clone(),
            control_cause_id: causes[0].clone(),
            control_intervention_row_id: manifest[1].id.clone(),
            control_before: prefix_return(&structural_w3, 3),
            control_after: prefix_return(&ple_ablation, 3),
            control_deeds: vec![
                bound_deed(Body::W3Cultivated, &structural_w3),
                bound_deed(Body::W3Cultivated, &ple_ablation),
            ],
        },
        CauseAblation {
            cause_id: causes[1].clone(),
            intervention_row_id: manifest[12].id.clone(),
            input_lineage_digest: structural_material.clone(),
            control_kind: AblationControlKind::CausalPrefix,
            before: recombined.clone(),
            ablated: residual_ablation.returned.clone(),
            restored: residual_restore.returned.clone(),
            deeds: vec![
                bound_deed(Body::W3Cultivated, &structural_w3),
                bound_deed(Body::W3Cultivated, &residual_ablation),
                bound_deed(Body::W3Cultivated, &residual_restore),
            ],
            control_input_lineage_digest: structural_material.clone(),
            control_cause_id: causes[1].clone(),
            control_intervention_row_id: manifest[12].id.clone(),
            control_before: prefix_return(&structural_w3, 3),
            control_after: prefix_return(&residual_ablation, 3),
            control_deeds: vec![
                bound_deed(Body::W3Cultivated, &structural_w3),
                bound_deed(Body::W3Cultivated, &residual_ablation),
            ],
        },
    ];
    let delta_ablation = CauseAblation {
        cause_id: cultivation_delta_id.clone(),
        intervention_row_id: "cultivation-delta".to_owned(),
        input_lineage_digest: structural_material.clone(),
        control_kind: AblationControlKind::SubjectDisjoint,
        before: recombined.clone(),
        ablated: structural_w2.returned.clone(),
        restored: ple_restore.returned.clone(),
        deeds: vec![
            bound_deed(Body::W3Cultivated, &structural_w3),
            bound_deed(Body::W2Predecessor, &structural_w2),
            bound_deed(Body::W3Cultivated, &ple_restore),
        ],
        control_input_lineage_digest: subject_material.clone(),
        control_cause_id: cultivation_delta_id.clone(),
        control_intervention_row_id: "cultivation-delta".to_owned(),
        control_before: subject_w3_control.returned.clone(),
        control_after: subject_w2_control.returned.clone(),
        control_deeds: vec![
            subject_w3_control.deed.clone(),
            subject_w2_control.deed.clone(),
        ],
    };
    let recombination = NativeRecombinationReceipt {
        held_out_lineage_digest: structural_lineage,
        lifted_cause_ids: causes,
        cultivation_delta_id,
        source_closure_identity: session.source_closure_identity().digest,
        source_closure_absence: absence_witness,
        baseline: baseline.clone(),
        recombined: recombined.clone(),
        recombined_deed: bound_deed(Body::W3Cultivated, &structural_w3),
        cause_ablations,
        cultivation_delta: delta_ablation,
    };
    let input = FourBodyInput {
        correspondence,
        component_ledger: components,
        intervention_manifest: manifest,
        condensation,
        held_out,
        recombination,
        bodies: vec![foreign_observation, w2_observation, w3_observation, arm],
    };
    let (grade, evidence_bytes) =
        w5::grade_with_evidence_bytes(input).map_err(|e| e.to_string())?;
    if !grade.passed {
        return Err("W5 grade returned unsuccessful".to_owned());
    }
    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    let evidence_path = args
        .output
        .parent()
        .ok_or("grade output has no parent")?
        .join("evidence.json");
    let evidence_tmp = evidence_path.with_extension("json.tmp");
    fs::write(&evidence_tmp, evidence_bytes).map_err(|e| e.to_string())?;
    fs::rename(&evidence_tmp, &evidence_path).map_err(|e| e.to_string())?;
    let grade_tmp = args.output.with_extension("json.tmp");
    fs::write(
        &grade_tmp,
        serde_json::to_vec_pretty(&grade).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    fs::rename(&grade_tmp, &args.output).map_err(|e| e.to_string())?;
    println!("W5 passed: {}", args.output.display());
    Ok(())
}
