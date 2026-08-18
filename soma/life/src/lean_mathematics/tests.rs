use super::syntax::*;
use super::*;

fn corpus() -> Vec<LeanSourceDocument> {
    vec![LeanSourceDocument::new(
        "Soma/Finite.lean",
        r#"
namespace Soma
variable {Old New : Type*}
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop)

theorem column_sum (m : New) : incoming demand capacity incident m =
    capacity m * congestion demand capacity incident m := by
  rw [congestion]
  ring

theorem congestion_over
    (hd : Good demand) (S : Finset Old) (m : New) (hover : 1 < load demand S) :
    1 < congestion demand capacity incident m := by
  exact hover.trans_le (subset_load demand capacity incident hd S m)
end Soma
"#,
    )]
}

fn problem() -> LeanProofProblem {
    LeanProofProblem {
        identity: "overload".to_owned(),
        source_scope: BTreeSet::from(["Soma/Finite.lean".to_owned()]),
        prefix: r#"import Soma.Finite
namespace Soma
variable {Old New : Type*}
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop)"#
            .to_owned(),
        theorem_header: r#"theorem overload
    (hd : Good demand) (S : Finset Old) (m : New)
    (hcap : 0 < capacity m) (hover : 1 < load demand S) :
    capacity m < incoming demand capacity incident m"#
            .to_owned(),
        suffix: "end Soma".to_owned(),
    }
}

fn target_face(problem: LeanProofProblem) -> LeanTheoremTargetFace {
    LeanTheoremTargetFace {
        problem,
        diagnosis_requirement: LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent,
    }
}

fn diagnosis() -> LeanDiagnosisCurrentFace {
    let region = LocalSet::from(["exact-chart".to_owned()]);
    LeanDiagnosisCurrentFace::from_closed_current(
        "episode-0/answer".to_owned(),
        "Which theorem carries the exact chart?".to_owned(),
        LocalSequence::from_iter(["diagnosis-clause".to_owned()]),
        LocalSet::from(["diagnosis-source".to_owned()]),
        LocalSet::from(["diagnosis-passage".to_owned()]),
        LocalSequence::from_iter([region.to_owned()]),
        LocalSet::from([region]),
        LocalSet::from(["diagnosis-passage".to_owned()]),
        LocalSet::from(["episode-0/answer".to_owned()]),
    )
    .unwrap()
}

fn target_request(
    identity: &str,
    declared_theorem_faces: LocalSet<String>,
    alternatives: LocalSequence<LeanTheoremTargetFace>,
) -> LeanTheoremTargetRequest {
    LeanTheoremTargetRequest {
        identity: identity.to_owned(),
        target_episode: "episode-0/answer".to_owned(),
        declared_theorem_faces,
        alternatives,
        diagnosis: diagnosis(),
    }
}

fn return_family(
    problem: &LeanProofProblem,
    candidates: &[LeanProofCandidate],
) -> LeanKernelReturnFamily {
    let members = candidates
        .iter()
        .enumerate()
        .map(|(at, candidate)| {
            let source = problem.render(&candidate.proof).unwrap();
            LeanKernelReturn {
                candidate: candidate.to_owned(),
                outcome: if at < 2 {
                    LeanKernelOutcome::KernelAdmitted
                } else {
                    LeanKernelOutcome::Obstructed
                },
                source_sha256: sha256(source.as_bytes()),
                diagnostic_sha256: sha256(b""),
                diagnostic: String::new(),
                observed_millis: 0,
            }
        })
        .collect::<LocalSequence<_>>();
    LeanKernelReturnFamily::from_members(members).unwrap()
}

fn kernel_returns(deed: &LeanKernelDeed) -> LeanKernelReturnFamily {
    return_family(deed.problem(), deed.candidates())
}

fn exact_target_request(identity: &str) -> LeanTheoremTargetRequest {
    target_request(
        identity,
        LocalSet::from(["overload".to_owned()]),
        LocalSequence::from_iter([target_face(problem())]),
    )
}

#[test]
fn source_surfaces_depart_but_declaration_and_tactic_morphology_remain() {
    let ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    assert_eq!(ecology.receipt().retained_source_surfaces, 0);
    assert!(ecology
        .declarations()
        .any(|organ| organ.name == "column_sum" && !organ.binders.is_empty()));
    assert!(ecology
        .declarations()
        .any(|organ| organ.name == "congestion_over"));
    assert!(ecology.receipt().tactic_species.contains("rw"));
    assert!(ecology.receipt().tactic_species.contains("ring"));
    let native = ecology.to_native_bytes().unwrap();
    let remounted = LeanMathematicsEcology::from_native_bytes(&native).unwrap();
    assert_eq!(remounted.to_native_bytes().unwrap(), native);
    assert!(!String::from_utf8(native)
        .unwrap()
        .contains("hover.trans_le"));
}

#[test]
fn returned_training_changes_the_mounted_body_and_survives_source_departure() {
    let mut ecology = LeanMathematicsEcology::mount();
    assert_eq!(
        ecology.generate_proof_candidates(&problem()),
        Err(LeanMathematicsError::NoLocalDeclarations)
    );

    ecology.train(&corpus()).unwrap();
    let (_, trained_candidates) = ecology.generate_proof_candidates(&problem()).unwrap();
    assert!(!trained_candidates.is_empty());

    let native = ecology.to_native_bytes().unwrap();
    let remounted = LeanMathematicsEcology::from_native_bytes(&native).unwrap();
    let (_, remounted_candidates) = remounted.generate_proof_candidates(&problem()).unwrap();
    assert_eq!(remounted_candidates, trained_candidates);
    assert!(!String::from_utf8(native)
        .unwrap()
        .contains("hover.trans_le"));
}

#[test]
fn a_new_theorem_recruits_plural_local_proof_paths_without_a_supplied_proof() {
    let ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let (reached, candidates) = ecology.generate_proof_candidates(&problem()).unwrap();
    assert_eq!(
        reached,
        LocalSet::from(["column_sum".to_owned(), "congestion_over".to_owned()])
    );
    assert!(candidates.iter().any(|candidate| {
        candidate
            .declaration_lineage
            .iter()
            .any(|name| name.as_ref() == "column_sum")
            && candidate
                .declaration_lineage
                .iter()
                .any(|name| name.as_ref() == "congestion_over")
    }));
    assert!(candidates
        .iter()
        .all(|candidate| !candidate.proof.contains("sorry")));
}

#[test]
fn contraposition_rebinds_the_transformed_target_hypothesis() {
    let documents = vec![LeanSourceDocument::new(
        "Soma/Finite.lean",
        r#"
namespace Soma
variable {Old New : Type*}
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop)

theorem total_demand_le_total_capacity
    (hc : ∀ m, 0 ≤ capacity m)
    (hz : Good incident)
    (hcong : ∀ m, congestion demand capacity incident m ≤ 1) :
    (∑ n : Old, demand n) ≤ ∑ m : New, capacity m := by
  exact conserved demand capacity incident hc hz hcong
end Soma
"#,
    )];
    let ecology = LeanMathematicsEcology::condition(&documents).unwrap();
    let organ = ecology
        .declarations()
        .find(|organ| organ.name == "total_demand_le_total_capacity")
        .unwrap();
    let target_names = BTreeSet::from([
        "Old".to_owned(),
        "New".to_owned(),
        "demand".to_owned(),
        "capacity".to_owned(),
        "incident".to_owned(),
        "hc".to_owned(),
        "hz".to_owned(),
        "hover".to_owned(),
    ]);
    assert_eq!(
        declaration_application_with_substitute(organ, &target_names, "hover"),
        "total_demand_le_total_capacity demand capacity incident hc hz hover",
        "binder charts: {:?}",
        organ.binders
    );
}

#[test]
fn a_conditioned_conjunction_induces_plural_projection_paths_without_source_proof_text() {
    let documents = vec![LeanSourceDocument::new(
        "Erdos/Result.lean",
        r#"
namespace Erdos
def bound (k : ℕ) : Prop := 2 ≤ k
def limitClaim : Prop := True

theorem explicit_and_limit :
    (∀ k : ℕ, 2 ≤ k → bound k) ∧ limitClaim := by
  constructor
  · intro k hk
    exact hk
  · trivial
end Erdos
"#,
    )];
    let ecology = LeanMathematicsEcology::condition(&documents).unwrap();
    let problem = LeanProofProblem {
        identity: "projected_bound".to_owned(),
        source_scope: BTreeSet::from(["Erdos/Result.lean".to_owned()]),
        prefix: "import Erdos.Result\nnamespace Erdos".to_owned(),
        theorem_header: "theorem projected_bound (k : ℕ) (hk : 2 ≤ k) : bound k".to_owned(),
        suffix: "end Erdos".to_owned(),
    };
    let (_, candidates) = ecology.generate_proof_candidates(&problem).unwrap();
    assert!(candidates.iter().any(|candidate| {
        candidate.motions.iter().any(|motion| {
            motion
                == &LeanProofMotion::Project {
                    declaration: Arc::<str>::from("explicit_and_limit"),
                    projection: 1,
                }
        })
    }));
    let native = ecology.to_native_bytes().unwrap();
    assert!(!String::from_utf8_lossy(&native).contains("intro k hk"));
    assert_eq!(
        LeanMathematicsEcology::from_native_bytes(&native)
            .unwrap()
            .to_native_bytes()
            .unwrap(),
        native
    );
}

#[test]
fn plural_kernel_admitted_family_mounts_one_reusable_theorem_organ() {
    let mut ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let mut follow = problem();
    follow.identity = "overload_again".to_owned();
    follow.theorem_header =
        follow
            .theorem_header
            .replacen("theorem overload", "theorem overload_again", 1);
    follow.source_scope.clear();
    follow
        .source_scope
        .insert("self-emanated/overload.lean".to_owned());
    assert_eq!(
        ecology.generate_proof_candidates(&follow),
        Err(LeanMathematicsError::NoLocalDeclarations)
    );

    let selection = ecology
        .select_and_open_kernel_deed(exact_target_request("plural-return-family"))
        .unwrap();
    assert!(matches!(selection, LeanTargetSelectionReceipt::Selected(_)));
    let deed = ecology.open_kernel_deed().unwrap();
    let deed_identity = deed.identity().to_owned();
    let returns = kernel_returns(deed);
    let completion = ecology
        .receive_kernel_deed_returns(&deed_identity, returns)
        .unwrap();
    let receipt = completion.cultivation();
    assert!(receipt.declaration_admitted);
    assert!(receipt.kernel_admitted_path_population > 1);
    assert_eq!(
        receipt.kernel_admitted_path_population,
        receipt.retained_source_surfaces
    );
    let LeanDeclarationConduct::KernelAdmittedFamily { proofs } = &receipt.declaration_conduct
    else {
        panic!("the complete admitted family must found the theorem organ");
    };
    assert_eq!(
        proofs.len(),
        ecology.returned_theorems()[0].kernel_admitted.len()
    );
    let (reached, later) = ecology.generate_proof_candidates(&follow).unwrap();
    assert!(reached.iter().any(|declaration| declaration == "overload"));
    assert!(later
        .iter()
        .any(|candidate| candidate.proof.contains("overload")));
    let native = ecology.to_native_bytes().unwrap();
    let remounted = LeanMathematicsEcology::from_native_bytes(&native).unwrap();
    assert_eq!(remounted.to_native_bytes().unwrap(), native);
    assert_eq!(remounted.returned_theorems().len(), 1);
}

#[test]
fn target_selection_requires_complete_declared_faces_and_keeps_diagnosis_lineage() {
    let mut partial_ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let partial = target_request(
        "partial-target-family",
        LocalSet::from(["overload".to_owned(), "unreceived".to_owned()]),
        LocalSequence::from_iter([target_face(problem())]),
    );
    let LeanTargetSelectionReceipt::Open(partial) = partial_ecology
        .select_and_open_kernel_deed(partial)
        .unwrap()
    else {
        panic!("an omitted declared face cannot select a theorem");
    };
    assert_eq!(
        partial.declared_theorem_faces,
        LocalSet::from(["overload".to_owned(), "unreceived".to_owned()])
    );
    assert_eq!(
        partial.received_theorem_faces,
        LocalSet::from(["overload".to_owned()])
    );
    assert!(partial_ecology.open_kernel_deed().is_none());
    assert_eq!(
        partial_ecology.select_and_open_kernel_deed(exact_target_request("replacement-target")),
        Err(LeanMathematicsError::TargetSelectionAlreadyOpen)
    );

    let mut ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let selected = ecology
        .select_and_open_kernel_deed(exact_target_request("exact-target-family"))
        .unwrap();
    let LeanTargetSelectionReceipt::Selected(selected) = selected else {
        panic!("the exact witnessed family must select its unique reachable face");
    };
    assert_eq!(selected.theorem, "overload");
    assert_eq!(selected.diagnosis, diagnosis());
    assert_eq!(
        selected.deed,
        ecology.open_kernel_deed().unwrap().identity()
    );
}

#[test]
fn open_kernel_deed_rests_remounts_and_completes_identically() {
    let mut direct = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let mut rested = LeanMathematicsEcology::condition(&corpus()).unwrap();
    assert_eq!(
        direct
            .select_and_open_kernel_deed(exact_target_request("rested-target"))
            .unwrap(),
        rested
            .select_and_open_kernel_deed(exact_target_request("rested-target"))
            .unwrap()
    );
    let rested = rested.into_native_rest().unwrap().remount().unwrap();
    assert_eq!(direct.open_kernel_deed(), rested.open_kernel_deed());
    let mut rested = rested;
    let deed_identity = direct.open_kernel_deed().unwrap().identity().to_owned();
    let direct_returns = kernel_returns(direct.open_kernel_deed().unwrap());
    let rested_returns = kernel_returns(rested.open_kernel_deed().unwrap());
    let direct_completion = direct
        .receive_kernel_deed_returns(&deed_identity, direct_returns)
        .unwrap();
    let rested_completion = rested
        .receive_kernel_deed_returns(&deed_identity, rested_returns)
        .unwrap();
    assert_eq!(direct_completion, rested_completion);
    assert!(direct.open_kernel_deed().is_none());
    assert!(rested.open_kernel_deed().is_none());
    assert_eq!(
        direct.to_native_bytes().unwrap(),
        rested.to_native_bytes().unwrap()
    );
}

#[test]
fn plural_return_permutation_forms_the_same_successor_and_rest() {
    let mut direct = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let mut permuted = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let request = exact_target_request("permuted-kernel-family");
    assert_eq!(
        direct
            .select_and_open_kernel_deed(request.to_owned())
            .unwrap(),
        permuted.select_and_open_kernel_deed(request).unwrap()
    );
    let deed_identity = direct.open_kernel_deed().unwrap().identity().to_owned();
    let returns = kernel_returns(direct.open_kernel_deed().unwrap());
    assert_eq!(returns.kernel_admitted_extent(), 2);
    let reversed =
        LeanKernelReturnFamily::from_members(returns.members().iter().rev().cloned()).unwrap();
    let direct_completion = direct
        .receive_kernel_deed_returns(&deed_identity, returns)
        .unwrap();
    let permuted_completion = permuted
        .receive_kernel_deed_returns(&deed_identity, reversed)
        .unwrap();
    assert_eq!(direct_completion, permuted_completion);
    assert_eq!(
        direct.to_native_bytes().unwrap(),
        permuted.to_native_bytes().unwrap()
    );
    let rest = direct.into_native_rest().unwrap();
    let remounted = rest.remount().unwrap();
    assert_eq!(remounted.returned_theorems()[0].kernel_admitted.len(), 2);
    assert_eq!(
        remounted.to_native_bytes().unwrap(),
        permuted.to_native_bytes().unwrap()
    );
}

#[test]
fn malformed_kernel_populations_and_open_training_leave_the_front_unchanged() {
    let mut ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    ecology
        .select_and_open_kernel_deed(exact_target_request("atomic-target"))
        .unwrap();
    let deed_identity = ecology.open_kernel_deed().unwrap().identity().to_owned();
    let returns = kernel_returns(ecology.open_kernel_deed().unwrap());
    let standing = ecology.to_native_bytes().unwrap();

    assert_eq!(
        ecology.receive_kernel_deed_returns("wrong-deed", returns.to_owned()),
        Err(LeanMathematicsError::WrongKernelDeed)
    );
    assert_eq!(ecology.to_native_bytes().unwrap(), standing);
    assert_eq!(
        ecology.receive_kernel_deed_returns(
            &deed_identity,
            LeanKernelReturnFamily::from_members(
                returns.members()[..returns.members().len().saturating_sub(1)]
                    .iter()
                    .cloned(),
            )
            .unwrap(),
        ),
        Err(LeanMathematicsError::IncompleteKernelReturn)
    );
    assert_eq!(ecology.to_native_bytes().unwrap(), standing);

    let mut duplicate = LocalSequence::from_slice(returns.members());
    if duplicate.len() > 1 {
        duplicate[1].candidate = duplicate[0].candidate.to_owned();
        assert_eq!(
            LeanKernelReturnFamily::from_members(duplicate),
            Err(LeanMathematicsError::IncompleteKernelReturn)
        );
        assert_eq!(ecology.to_native_bytes().unwrap(), standing);
    }
    let mut substituted = returns.to_owned();
    substituted.members_mut()[0]
        .candidate
        .proof
        .push_str("\n  exact True.intro");
    assert_eq!(
        ecology.receive_kernel_deed_returns(&deed_identity, substituted),
        Err(LeanMathematicsError::IncompleteKernelReturn)
    );
    assert_eq!(ecology.to_native_bytes().unwrap(), standing);
    assert_eq!(
        ecology.train(&corpus()),
        Err(LeanMathematicsError::KernelDeedAlreadyOpen)
    );
    assert_eq!(ecology.to_native_bytes().unwrap(), standing);

    ecology
        .receive_kernel_deed_returns(&deed_identity, returns)
        .unwrap();
    assert!(ecology.open_kernel_deed().is_none());
}

#[test]
fn lean_rest_rejects_prior_missing_unknown_and_corrupted_nested_faces() {
    let ecology = LeanMathematicsEcology::condition(&corpus()).unwrap();
    let standing = ecology.to_native_bytes().unwrap();
    for schema in [
        "life.lean-mathematics-ecology.v1",
        "life.lean-mathematics-ecology.v2",
        "life.lean-mathematics-ecology.v3",
    ] {
        let mut value: serde_json::Value = serde_json::from_slice(&standing).unwrap();
        value["schema"] = serde_json::Value::String(schema.to_owned());
        assert_eq!(
            LeanMathematicsEcology::from_native_bytes(&serde_json::to_vec(&value).unwrap()),
            Err(LeanMathematicsError::InvalidRest)
        );
    }
    let mut missing: serde_json::Value = serde_json::from_slice(&standing).unwrap();
    missing.as_object_mut().unwrap().remove("generation");
    assert_eq!(
        LeanMathematicsEcology::from_native_bytes(&serde_json::to_vec(&missing).unwrap()),
        Err(LeanMathematicsError::InvalidRest)
    );
    let mut unknown: serde_json::Value = serde_json::from_slice(&standing).unwrap();
    unknown["receipt"]["foreign"] = serde_json::Value::Bool(true);
    assert_eq!(
        LeanMathematicsEcology::from_native_bytes(&serde_json::to_vec(&unknown).unwrap()),
        Err(LeanMathematicsError::InvalidRest)
    );

    let mut open = LeanMathematicsEcology::condition(&corpus()).unwrap();
    open.select_and_open_kernel_deed(exact_target_request("corrupt-open"))
        .unwrap();
    let mut nested: serde_json::Value =
        serde_json::from_slice(&open.to_native_bytes().unwrap()).unwrap();
    nested["open_kernel_deed"]["candidates"][0]["foreign"] = serde_json::Value::Bool(true);
    assert_eq!(
        LeanMathematicsEcology::from_native_bytes(&serde_json::to_vec(&nested).unwrap()),
        Err(LeanMathematicsError::InvalidRest)
    );
}

/// **The admission law over mathematics, and all four verdicts on one family.**
///
/// The kernel supplies both sides natively: an admitted submission confirms every motion it
/// carried, an obstructed one refutes them. A motion in both is CONFLICTED — it closes some goals
/// and not others, so its own name does not determine whether it carries.
#[test]
fn a_motion_in_both_an_admitted_and_an_obstructed_proof_is_conflicted() {
    use crate::holonic_training::FiberAdmission;
    use crate::lean_mathematics::kernel_returns::{motion_admissions, motion_key, motion_standing};
    use std::sync::Arc;

    let always = LeanProofMotion::Close {
        tactic: Arc::from("rfl"),
    };
    let never = LeanProofMotion::Rewrite {
        declaration: Arc::from("absent_lemma"),
    };
    let both = LeanProofMotion::Direct {
        declaration: Arc::from("shared_lemma"),
    };

    let member = |ordinal: u64, motions: Vec<LeanProofMotion>, admitted: bool| LeanKernelReturn {
        candidate: LeanProofCandidate {
            ordinal,
            proof: format!("proof {ordinal}"),
            motions,
            declaration_lineage: LocalSet::default(),
        },
        outcome: if admitted {
            LeanKernelOutcome::KernelAdmitted
        } else {
            LeanKernelOutcome::Obstructed
        },
        source_sha256: sha256(format!("{ordinal}").as_bytes()),
        diagnostic_sha256: sha256(b""),
        diagnostic: String::new(),
        observed_millis: 0,
    };

    let family = LeanKernelReturnFamily::from_members(LocalSequence::from_iter([
        member(0, vec![always.clone(), both.clone()], true),
        member(1, vec![always.clone()], true),
        member(2, vec![never.clone(), both.clone()], false),
    ]))
    .unwrap();

    let standing = motion_standing(&family);
    assert_eq!(standing[&motion_key(&always)].confirmations, 2);
    assert_eq!(standing[&motion_key(&always)].refutations, 0);
    assert_eq!(standing[&motion_key(&both)].confirmations, 1);
    assert_eq!(standing[&motion_key(&both)].refutations, 1);
    assert_eq!(standing[&motion_key(&never)].confirmations, 0);
    assert_eq!(standing[&motion_key(&never)].refutations, 1);

    let sorted = motion_admissions(&family);
    let named = |verdict: FiberAdmission| -> Vec<String> {
        sorted
            .get(&verdict)
            .map(|members| members.iter().map(|(key, _)| key.clone()).collect())
            .unwrap_or_default()
    };
    assert_eq!(named(FiberAdmission::Admitted), vec![motion_key(&always)]);
    assert_eq!(named(FiberAdmission::Conflicted), vec![motion_key(&both)]);
    assert_eq!(named(FiberAdmission::Refuted), vec![motion_key(&never)]);
    assert!(
        named(FiberAdmission::Open).is_empty(),
        "every motion here was submitted"
    );
}

/// A motion repeated inside ONE proof is one piece of evidence about that proof, not several.
/// Without this the counts would rank by how often a tactic appears in a single term.
#[test]
fn a_motion_repeated_inside_one_proof_counts_once() {
    use crate::lean_mathematics::kernel_returns::{motion_key, motion_standing};
    use std::sync::Arc;

    let motion = LeanProofMotion::Close {
        tactic: Arc::from("simp"),
    };
    let family = LeanKernelReturnFamily::from_members(LocalSequence::from_iter([
        LeanKernelReturn {
            candidate: LeanProofCandidate {
                ordinal: 0,
                proof: "proof".to_owned(),
                motions: vec![motion.clone(), motion.clone(), motion.clone()],
                declaration_lineage: LocalSet::default(),
            },
            outcome: LeanKernelOutcome::KernelAdmitted,
            source_sha256: sha256(b"0"),
            diagnostic_sha256: sha256(b""),
            diagnostic: String::new(),
            observed_millis: 0,
        },
    ]))
    .unwrap();
    let standing = motion_standing(&family);
    assert_eq!(standing[&motion_key(&motion)].confirmations, 1);
}
