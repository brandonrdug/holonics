use super::*;

fn test_material() -> String {
    digest(b"test-material")
}
fn face(name: &str, value: u8, material: &str) -> Face {
    Face {
        name: name.to_owned(),
        material_digest: material.to_owned(),
        intervals: vec![(i64::from(value), i64::from(value) + 1)],
    }
}
fn returned_for(value: u8, material: &str) -> ReceiverReturn {
    let faces: Vec<Face> = (0..128)
        .map(|index| {
            face(
                &format!("face-{index}"),
                value.wrapping_add(index as u8),
                material,
            )
        })
        .collect();
    let digest = canonical_return_digest(&faces).unwrap();
    ReceiverReturn { faces, digest }
}
fn returned(value: u8) -> ReceiverReturn {
    returned_for(value, &test_material())
}
fn intervened(base: &ReceiverReturn, row: usize) -> ReceiverReturn {
    let mut returned = base.clone();
    if row == 2 {
        let interval = &mut returned.faces[3].intervals[0];
        interval.0 += 1;
        interval.1 += 1;
    } else {
        let control = matches!(row, 4 | 5 | 6 | 7 | 11);
        let mut face = INTERVENTION_PREFIX_FACES[row].min(127);
        if control && face == 5 {
            face = 6;
        }
        returned.faces[face].intervals[0].0 += 8;
        returned.faces[face].intervals[0].1 += 8;
        if row == 5 {
            let interval = &mut returned.faces[5].intervals[0];
            interval.0 += 1;
            interval.1 += 1;
        }
    }
    returned.digest = canonical_return_digest(&returned.faces).unwrap();
    returned
}
fn execution(kind: ExecutionKind, id: &str, returned_artifact_digest: &str) -> ExecutionWitness {
    ExecutionWitness {
        kind,
        deed_identity: digest(id.as_bytes()),
        resident_owner: "owner".to_owned(),
        returned_artifact_digest: returned_artifact_digest.to_owned(),
        source_access: SourceAccessWitness {
            audit_identity: digest(format!("audit-{id}").as_bytes()),
            forbidden: Vec::new(),
        },
    }
}
fn work(return_digest: &str) -> WorkReceipt {
    let mut exact = ExactWork::nothing();
    exact.added(1);
    let admission_digest = "admission".to_owned();
    let admission_evidence = serde_json::to_string(&admission_digest).unwrap();
    let admission_digest = digest(admission_evidence.as_bytes());
    let owner_receipt_digest = digest(
        &serde_json::to_vec(&(
            exact.clone(),
            admission_digest.clone(),
            return_digest.to_owned(),
        ))
        .unwrap(),
    );
    WorkReceipt {
        work: exact,
        admission_digest,
        admission_evidence,
        returned_artifact_digest: return_digest.to_owned(),
        owner_receipt_digest,
    }
}
fn apparatus(return_digest: &str) -> ApparatusUtility {
    let known = |v: u32| Calibrated::Known(BigUint::from(v));
    ApparatusUtility {
        device_name: "card".to_owned(),
        mode: "mode".to_owned(),
        kernel_identity: "kernel".to_owned(),
        launches: known(1),
        synchronizations: known(1),
        transfer_octets: known(1),
        active_warps: Calibrated::Unknown {
            reason: "not calibrated".to_owned(),
        },
        energy: Calibrated::Unknown {
            reason: "not calibrated".to_owned(),
        },
        calibration: [
            ("launches", "device counter"),
            ("synchronizations", "device counter"),
            ("transfer_octets", "transfer calibration"),
        ]
        .into_iter()
        .map(|(key, value)| (key.to_owned(), value.to_owned()))
        .collect(),
        apparatus_evidence: serde_json::to_string(&("apparatus", return_digest)).unwrap(),
        apparatus_digest: digest(
            serde_json::to_string(&("apparatus", return_digest))
                .unwrap()
                .as_bytes(),
        ),
        returned_artifact_digest: return_digest.to_owned(),
    }
}
fn inferred_body(id: &str) -> Body {
    if id.starts_with("held-") {
        match id
            .rsplit('-')
            .next()
            .and_then(|value| value.parse::<u8>().ok())
        {
            Some(0) => return Body::ForeignSource,
            Some(1) => return Body::W2Predecessor,
            _ => {}
        }
    }
    if id.contains("ForeignSource") || id.contains("foreign") {
        Body::ForeignSource
    } else if id.contains("W2") || id.contains("w2") {
        Body::W2Predecessor
    } else if id.contains("Arm") || id.contains("arm") {
        Body::ArmN
    } else {
        Body::W3Cultivated
    }
}
fn bound_for(body: Body, kind: ExecutionKind, id: &str, return_digest: &str) -> BoundDeed {
    BoundDeed {
        body,
        execution: execution(kind, id, return_digest),
        work: work(return_digest),
        apparatus: apparatus(return_digest),
    }
}
fn bound(kind: ExecutionKind, id: &str, return_digest: &str) -> BoundDeed {
    bound_for(inferred_body(id), kind, id, return_digest)
}
fn manifest() -> Vec<InterventionManifestRow> {
    (0..16)
        .map(|i| InterventionManifestRow {
            id: INTERVENTION_ROW_IDS[i].to_owned(),
            site: INTERVENTION_SITES[i].to_owned(),
            law_digest: format!("law-{i}"),
            pre_intervention_prefix: INTERVENTION_PREFIX_FACES[i],
            requires_separation: i != 2,
            order_face_control: i == 2,
            exact_control_span: matches!(i, 4 | 6 | 7 | 11).then_some(ControlSpan {
                face_index: 5,
                start: 0,
                extent: 1,
            }),
            unseparated_control_span: (i == 5).then_some(ControlSpan {
                face_index: 5,
                start: 0,
                extent: 1,
            }),
        })
        .collect()
}
fn body(body: Body, codebook: &str, extent: u32, value: u8) -> BodyObservation {
    let current = returned(value);
    let return_digest = current.digest.clone();
    let base = current.clone();
    let interventions = manifest()
        .into_iter()
        .enumerate()
        .map(|(i, row)| {
            let after = intervened(&base, i);
            MatchedIntervention {
                body,
                row_id: row.id,
                site: row.site,
                law_digest: row.law_digest,
                pre_intervention_prefix: row.pre_intervention_prefix,
                before: base.clone(),
                after: after.clone(),
                deed: bound(
                    if body == Body::W3Cultivated {
                        ExecutionKind::NativeRuntime
                    } else {
                        ExecutionKind::ResidentGpu
                    },
                    &format!("{body:?}-intervention-{i}"),
                    &after.digest,
                ),
                intervention_occurrence_digest: format!("occ-{i}"),
                order_face_before_digest: "order".to_owned(),
                order_face_after_digest: "order".to_owned(),
            }
        })
        .collect();
    BodyObservation {
        body,
        body_digest: digest(format!("{body:?}-body").as_bytes()),
        base_material_digest: test_material(),
        deed_closure_digest: digest(format!("{body:?}-deed-closure").as_bytes()),
        source_closure_identity: digest(b"shared-source-closure"),
        codebook_digest: codebook.to_owned(),
        codebook_extent: extent,
        receiver_family_digest: receiver_family_digest(&ordered_face_names(&current.faces)),
        base_return_digest: base.digest.clone(),
        faces: current.faces,
        return_digest: return_digest.clone(),
        deed: bound(
            if body == Body::ArmN {
                ExecutionKind::NativeRuntime
            } else if body == Body::W3Cultivated {
                ExecutionKind::NativeRuntime
            } else {
                ExecutionKind::ResidentGpu
            },
            &format!("{body:?}-current"),
            &return_digest,
        ),
        base_replay_return_digest: return_digest.clone(),
        base_replay_deed: bound(
            if body == Body::W3Cultivated {
                ExecutionKind::NativeRuntime
            } else {
                ExecutionKind::ResidentGpu
            },
            &format!("{body:?}-replay"),
            &return_digest,
        ),
        interventions,
        cultivation_delta_id: if body == Body::W3Cultivated {
            "cultivation-delta".to_owned()
        } else {
            String::new()
        },
        prior_return: None,
        prior_deed: None,
    }
}
fn held_out() -> Vec<HeldOutCase> {
    [
        HeldOutKind::StructuralChanged,
        HeldOutKind::SubjectDisjointUnchanged,
        HeldOutKind::MatchedFoil,
        HeldOutKind::NoOp,
        HeldOutKind::CodecVariant,
    ]
    .into_iter()
    .enumerate()
    .map(|(case_i, kind)| {
        let case_material = if case_i == 0 {
            test_material()
        } else {
            digest(format!("case-material-{case_i}").as_bytes())
        };
        let changed = matches!(
            kind,
            HeldOutKind::StructuralChanged | HeldOutKind::MatchedFoil
        );
        let returns = [Body::ForeignSource, Body::W2Predecessor, Body::W3Cultivated]
            .into_iter()
            .enumerate()
            .map(|(body_i, body)| {
                let before = returned_for(20 + case_i as u8, &case_material);
                let after = if changed && body == Body::W3Cultivated {
                    returned_for(30 + case_i as u8, &case_material)
                } else if changed {
                    returned_for(21 + case_i as u8, &case_material)
                } else {
                    before.clone()
                };
                HeldOutBodyReturn {
                    body,
                    input_lineage_digest: digest(format!("lineage-{case_i}-{body_i}").as_bytes()),
                    returned: after.clone(),
                    deed: bound(
                        if kind == HeldOutKind::NoOp && body == Body::W3Cultivated {
                            ExecutionKind::NoMorphologyControl
                        } else if body == Body::W3Cultivated {
                            ExecutionKind::NativeRuntime
                        } else {
                            ExecutionKind::ResidentGpu
                        },
                        &format!("held-{case_i}-{body_i}"),
                        &after.digest,
                    ),
                }
            })
            .collect();
        HeldOutCase {
            kind,
            lineage_digest: case_material.clone(),
            input_baseline_digest: returned_for(20 + case_i as u8, &case_material).digest,
            returns,
            codec_paths: if kind == HeldOutKind::CodecVariant {
                vec![
                    CodecVariantPath {
                        path_identity: "codec-a".to_owned(),
                        token_word_digest: "word".to_owned(),
                    },
                    CodecVariantPath {
                        path_identity: "codec-b".to_owned(),
                        token_word_digest: "word".to_owned(),
                    },
                ]
            } else {
                Vec::new()
            },
        }
    })
    .collect()
}
fn ablation(
    cause: &str,
    row: &str,
    material: &str,
    before: &ReceiverReturn,
    altered: &ReceiverReturn,
    restored: &ReceiverReturn,
    id: &str,
) -> CauseAblation {
    let control_kind = if row == "cultivation-delta" {
        AblationControlKind::SubjectDisjoint
    } else {
        AblationControlKind::CausalPrefix
    };
    let (control_lineage, control_before, control_after, ablated) =
        if control_kind == AblationControlKind::CausalPrefix {
            let mut causal_ablated = altered.clone();
            causal_ablated.faces[0] = before.faces[0].clone();
            causal_ablated.digest = canonical_return_digest(&causal_ablated.faces).unwrap();
            let control = ReceiverReturn {
                faces: vec![before.faces[0].clone()],
                digest: canonical_return_digest(&[before.faces[0].clone()]).unwrap(),
            };
            (
                material.to_owned(),
                control.clone(),
                control,
                causal_ablated,
            )
        } else {
            let lineage = digest(b"control-lineage");
            let control = returned_for(90, &lineage);
            (lineage, control.clone(), control, altered.clone())
        };
    let ablated_digest = ablated.digest.clone();
    let bodies = if row == "cultivation-delta" {
        [Body::W3Cultivated, Body::W2Predecessor, Body::W3Cultivated]
    } else {
        [Body::W3Cultivated; 3]
    };
    let control_bodies = if row == "cultivation-delta" {
        [Body::W3Cultivated, Body::W2Predecessor]
    } else {
        [Body::W3Cultivated; 2]
    };
    let control_ids = if control_kind == AblationControlKind::CausalPrefix {
        [format!("{id}-before"), format!("{id}-ablated")]
    } else {
        [
            format!("{id}-control-before"),
            format!("{id}-control-after"),
        ]
    };
    let control_return_digests = if control_kind == AblationControlKind::CausalPrefix {
        [before.digest.clone(), ablated_digest.clone()]
    } else {
        [control_before.digest.clone(), control_after.digest.clone()]
    };
    CauseAblation {
        cause_id: cause.to_owned(),
        intervention_row_id: row.to_owned(),
        input_lineage_digest: material.to_owned(),
        control_kind,
        before: before.clone(),
        ablated,
        restored: restored.clone(),
        deeds: vec![
            bound_for(
                bodies[0],
                if bodies[0] == Body::W3Cultivated {
                    ExecutionKind::NativeRuntime
                } else {
                    ExecutionKind::ResidentGpu
                },
                &format!("{id}-before"),
                &before.digest,
            ),
            bound_for(
                bodies[1],
                if bodies[1] == Body::W3Cultivated {
                    ExecutionKind::NativeRuntime
                } else {
                    ExecutionKind::ResidentGpu
                },
                &format!("{id}-ablated"),
                &ablated_digest,
            ),
            bound_for(
                bodies[2],
                if bodies[2] == Body::W3Cultivated {
                    ExecutionKind::NativeRuntime
                } else {
                    ExecutionKind::ResidentGpu
                },
                &format!("{id}-restored"),
                &restored.digest,
            ),
        ],
        control_input_lineage_digest: control_lineage,
        control_cause_id: cause.to_owned(),
        control_intervention_row_id: row.to_owned(),
        control_before: control_before.clone(),
        control_after: control_after.clone(),
        control_deeds: vec![
            bound_for(
                control_bodies[0],
                if control_bodies[0] == Body::W3Cultivated {
                    ExecutionKind::NativeRuntime
                } else {
                    ExecutionKind::ResidentGpu
                },
                &control_ids[0],
                &control_return_digests[0],
            ),
            bound_for(
                control_bodies[1],
                if control_bodies[1] == Body::W3Cultivated {
                    ExecutionKind::NativeRuntime
                } else {
                    ExecutionKind::ResidentGpu
                },
                &control_ids[1],
                &control_return_digests[1],
            ),
        ],
    }
}
fn valid() -> FourBodyInput {
    let manifest = manifest();
    let foreign = body(Body::ForeignSource, "source-codebook", 2, 1);
    let predecessor = body(Body::W2Predecessor, "native-codebook", 2, 1);
    let cultivated = body(Body::W3Cultivated, "native-codebook", 2, 5);
    let arm_current = returned(7);
    let arm_prior = returned(6);
    let arm = BodyObservation {
        body: Body::ArmN,
        body_digest: digest(b"arm-body"),
        base_material_digest: test_material(),
        deed_closure_digest: digest(b"arm-deed-closure"),
        source_closure_identity: digest(b"arm-source-closure"),
        codebook_digest: "arm-codebook".to_owned(),
        codebook_extent: 2,
        receiver_family_digest: receiver_family_digest(&ordered_face_names(&arm_current.faces)),
        base_return_digest: arm_current.digest.clone(),
        faces: arm_current.faces.clone(),
        return_digest: arm_current.digest.clone(),
        deed: bound(
            ExecutionKind::NativeRuntime,
            "arm-current",
            &arm_current.digest,
        ),
        base_replay_return_digest: arm_current.digest.clone(),
        base_replay_deed: bound(
            ExecutionKind::NativeRuntime,
            "arm-replay",
            &arm_current.digest,
        ),
        interventions: Vec::new(),
        cultivation_delta_id: String::new(),
        prior_return: Some(arm_prior.clone()),
        prior_deed: Some(bound(
            ExecutionKind::NativeRuntime,
            "arm-prior",
            &arm_prior.digest,
        )),
    };
    let prior_family = vec!["ple".to_owned()];
    let enlarged_family = vec!["ple".to_owned(), "potential".to_owned()];
    let retained = vec![vec![1]];
    let open = vec!["fibre".to_owned()];
    let prior_population = BigUint::from(2u32);
    let enlarged_population = BigUint::from(1u32);
    let refinement_digest = digest(
        &serde_json::to_vec(&(
            predecessor.source_closure_identity.clone(),
            prior_family.clone(),
            enlarged_family.clone(),
            prior_population.clone(),
            enlarged_population.clone(),
            retained.clone(),
            open.clone(),
        ))
        .unwrap(),
    );
    let condensation = CondensationRemainder {
        prior_artifact_digest: predecessor.source_closure_identity.clone(),
        prior_receiver_family: prior_family,
        enlarged_receiver_family: enlarged_family,
        prior_collapsed_population: prior_population,
        enlarged_collapsed_population: enlarged_population,
        retained_separators: retained,
        open_fibres: open,
        refinement_digest,
    };
    let baseline = returned(21);
    let recombined = returned(30);
    let lifted = vec!["law-0".to_owned(), "law-1".to_owned()];
    let cultivation_delta_id = "cultivation-delta".to_owned();
    let absent_overlay_operation_ids = vec!["overlay-op-u".to_owned(), "overlay-op-v".to_owned()];
    let absent_factor_populations = vec!["factor-u".to_owned(), "factor-v".to_owned()];
    let held_out_difference_digest =
        digest(&serde_json::to_vec(&(baseline.digest.clone(), recombined.digest.clone())).unwrap());
    let absence_digest = digest(
        &serde_json::to_vec(&(
            predecessor.source_closure_identity.clone(),
            true,
            absent_overlay_operation_ids.clone(),
            absent_factor_populations.clone(),
            held_out_difference_digest.clone(),
        ))
        .unwrap(),
    );
    let mut cause_ablations = Vec::new();
    for (i, cause) in lifted.iter().enumerate() {
        cause_ablations.push(ablation(
            cause,
            INTERVENTION_ROW_IDS[i],
            &test_material(),
            &recombined,
            &returned(80 + i as u8),
            &recombined,
            &format!("cause-{i}"),
        ));
    }
    let cultivation = ablation(
        &cultivation_delta_id,
        "cultivation-delta",
        &test_material(),
        &recombined,
        &baseline,
        &recombined,
        "cultivation",
    );
    let recombination = NativeRecombinationReceipt {
        held_out_lineage_digest: test_material(),
        lifted_cause_ids: lifted.clone(),
        cultivation_delta_id,
        source_closure_identity: predecessor.source_closure_identity.clone(),
        source_closure_absence: SourceClosureAbsenceWitness {
            source_closure_identity: predecessor.source_closure_identity.clone(),
            overlay_topology_absent: true,
            absent_overlay_operation_ids,
            absent_factor_populations,
            held_out_difference_digest,
            witness_digest: absence_digest,
        },
        baseline: baseline.clone(),
        recombined: recombined.clone(),
        recombined_deed: bound(
            ExecutionKind::NativeRuntime,
            "recombined",
            &recombined.digest,
        ),
        cause_ablations,
        cultivation_delta: cultivation,
    };
    let source_to_native = vec![(0, 0), (1, 1)];
    let unresolved_source = Vec::new();
    let receiver_names = ordered_face_names(&foreign.faces);
    let receiver_digest = receiver_family_digest(&receiver_names);
    let relation_digest = digest(
        &serde_json::to_vec(&(
            "source-codebook".to_owned(),
            "native-codebook".to_owned(),
            2u32,
            2u32,
            source_to_native.clone(),
            unresolved_source.clone(),
            receiver_names.clone(),
            receiver_digest.clone(),
        ))
        .unwrap(),
    );
    let correspondence = SourceNativeCorrespondence {
        source_codebook_digest: "source-codebook".to_owned(),
        native_codebook_digest: "native-codebook".to_owned(),
        source_extent: 2,
        native_extent: 2,
        source_to_native,
        unresolved_source,
        receiver_names,
        receiver_family_digest: receiver_digest,
        relation_digest,
    };
    let component_ledger = COMPONENT_ROW_IDS
        .into_iter()
        .enumerate()
        .map(|(index, row_id)| ComponentEvidence {
            row_id: row_id.to_owned(),
            artifact_identity: digest(format!("artifact-{index}").as_bytes()),
            extent: 1,
            schema: COMPONENT_SCHEMAS[index].to_owned(),
        })
        .collect();
    FourBodyInput {
        correspondence,
        component_ledger,
        intervention_manifest: manifest,
        condensation,
        held_out: held_out(),
        recombination,
        bodies: vec![foreign, predecessor, cultivated, arm],
    }
}

#[test]
fn valid_fixture_passes_v2() {
    assert!(grade(valid()).is_ok());
}
#[test]
fn mutated_face_is_rejected() {
    let mut input = valid();
    input.bodies[0].faces[0].intervals[0].0 += 1;
    assert!(grade(input).is_err());
}
#[test]
fn random_execution_strings_are_rejected() {
    let mut input = valid();
    input.bodies[0].deed.execution.returned_artifact_digest = "random".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn deed_body_identity_cannot_be_relabelled() {
    let mut input = valid();
    input.bodies[0].deed.body = Body::W3Cultivated;
    assert!(grade(input).is_err());
}
#[test]
fn resident_body_cannot_claim_native_runtime() {
    let mut input = valid();
    input.bodies[0].deed.execution.kind = ExecutionKind::NativeRuntime;
    assert!(grade(input).is_err());
}
#[test]
fn mount_only_is_rejected_for_every_body() {
    let mut input = valid();
    input.bodies[1].deed.execution.kind = ExecutionKind::RestMount;
    assert!(grade(input).is_err());
}
#[test]
fn swapped_receiver_or_codebook_is_rejected() {
    let mut input = valid();
    input.bodies[1].codebook_digest = "source-codebook".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn first_three_bodies_must_share_the_admitted_source_closure() {
    let mut input = valid();
    input.bodies[2].source_closure_identity = digest(b"another-source-closure");
    assert!(grade(input).is_err());
}
#[test]
fn duplicate_native_id_is_rejected() {
    let mut input = valid();
    input.correspondence.source_to_native[1].1 = 0;
    assert!(grade(input).is_err());
}
#[test]
fn panel_omission_is_rejected() {
    let mut input = valid();
    input.bodies[0].interventions.pop();
    assert!(grade(input).is_err());
}
#[test]
fn panel_reorder_is_rejected() {
    let mut input = valid();
    input.bodies[0].interventions.swap(0, 1);
    assert!(grade(input).is_err());
}
#[test]
fn copied_held_out_is_rejected() {
    let mut input = valid();
    input.held_out[1].returns[1].input_lineage_digest =
        input.held_out[1].returns[0].input_lineage_digest.clone();
    assert!(grade(input).is_err());
}
#[test]
fn prose_condensation_is_rejected() {
    let mut input = valid();
    input.condensation.open_fibres[0] = "prose claim".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn non_monotonic_condensation_is_rejected() {
    let mut input = valid();
    input.condensation.enlarged_collapsed_population = BigUint::from(3u32);
    assert!(grade(input).is_err());
}
#[test]
fn fake_ablation_is_rejected() {
    let mut input = valid();
    input.recombination.cause_ablations[0].restored = returned(99);
    assert!(grade(input).is_err());
}
#[test]
fn mount_only_arm_n_is_rejected() {
    let mut input = valid();
    input.bodies[3].deed.execution.kind = ExecutionKind::RestMount;
    assert!(grade(input).is_err());
}
#[test]
fn fake_work_is_rejected() {
    let mut input = valid();
    input.bodies[0].deed.work.work.added(1);
    assert!(grade(input).is_err());
}
#[test]
fn uncalibrated_known_utility_is_rejected() {
    let mut input = valid();
    input.bodies[0].deed.apparatus.calibration.clear();
    assert!(grade(input).is_err());
}
#[test]
fn apparatus_evidence_bytes_are_bound() {
    let mut input = valid();
    input.bodies[0].deed.apparatus.apparatus_evidence.push('x');
    assert!(grade(input).is_err());
}
#[test]
fn missing_required_held_out_row_is_rejected() {
    let mut input = valid();
    input
        .held_out
        .retain(|case| case.kind != HeldOutKind::SubjectDisjointUnchanged);
    assert!(grade(input).is_err());
}
#[test]
fn intervention_work_cannot_be_relabelled_for_a_sibling() {
    let mut input = valid();
    input.bodies[0].interventions[0].deed.work.work.added(1);
    assert!(grade(input).is_err());
}
#[test]
fn face_material_must_be_the_body_material() {
    let mut input = valid();
    input.bodies[0].faces[0].material_digest = digest(b"another-material");
    assert!(grade(input).is_err());
}
#[test]
fn component_schema_is_not_an_arbitrary_label() {
    let mut input = valid();
    input.component_ledger[0].schema = "looks-plausible".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn ablation_cause_must_name_its_actual_row_and_material() {
    let mut input = valid();
    input.recombination.cause_ablations[0].intervention_row_id = "residual-reentry".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn subject_control_must_name_the_same_cause_and_row() {
    let mut input = valid();
    input.recombination.cause_ablations[0].control_intervention_row_id =
        "residual-reentry".to_owned();
    assert!(grade(input).is_err());
}
#[test]
fn causal_prefix_control_kind_cannot_be_swapped() {
    let mut input = valid();
    input.recombination.cause_ablations[0].control_kind = AblationControlKind::SubjectDisjoint;
    assert!(grade(input).is_err());
}
#[test]
fn causal_prefix_control_must_remain_a_prefix() {
    let mut input = valid();
    let control = &mut input.recombination.cause_ablations[0].control_before;
    control.faces[0].intervals[0].0 += 1;
    control.digest = canonical_return_digest(&control.faces).unwrap();
    input.recombination.cause_ablations[0].control_after = control.clone();
    assert!(grade(input).is_err());
}
#[test]
fn subject_control_cannot_copy_a_causal_deed() {
    let mut input = valid();
    input.recombination.cultivation_delta.control_deeds[0] =
        input.recombination.cause_ablations[0].deeds[0].clone();
    assert!(grade(input).is_err());
}
#[test]
fn no_op_must_be_a_typed_no_morphology_deed() {
    let mut input = valid();
    let no_op = input
        .held_out
        .iter_mut()
        .find(|case| case.kind == HeldOutKind::NoOp)
        .unwrap();
    no_op.returns[2].deed.execution.kind = ExecutionKind::ResidentGpu;
    assert!(grade(input).is_err());
}
#[test]
fn evidence_sidecar_binds_the_complete_input() {
    let input = valid();
    let (grade, sidecar) = grade_with_evidence(input).unwrap();
    assert_eq!(grade.evidence, sidecar.binding().unwrap());
    sidecar.verify().unwrap();
    let mut drifted = sidecar;
    drifted.input.bodies[0].body_digest = digest(b"drift");
    assert!(drifted.verify().is_err());
    let (_, fresh) = grade_with_evidence(valid()).unwrap();
    assert!(!fresh.into_bytes().unwrap().is_empty());
}
#[test]
fn admission_evidence_bytes_are_part_of_the_work_binding() {
    let mut input = valid();
    input.bodies[0].deed.work.admission_evidence.push('x');
    assert!(grade(input).is_err());
}
