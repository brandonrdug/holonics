//! Candidate render.
//!
//! One target header and one declaration family return one candidate family through the
//! standing render: application, projection, rewrite, introduced fact, recurrence, and
//! contraposition shapes, each carrying its declaration lineage.  The render owns no selection:
//! every candidate is graded by the exterior kernel, and nothing here consults a score.
//!
//! Two entries supply the family.  `generate_proof_candidates_at` reaches declarations through
//! the target's own identifiers, the inherited entry.  `generate_proof_candidates_for` renders
//! over an explicitly supplied family: the organs one conducted native route reached, read back
//! through the cold witness.  The route decides the family; the render only projects it.

use super::syntax::*;
use super::*;

impl LeanMathematicsEcology {
    pub fn generate_proof_candidates(
        &self,
        problem: &LeanProofProblem,
    ) -> Result<(LeanDeclarationNames, Vec<LeanProofCandidate>), LeanMathematicsError> {
        self.generate_proof_candidates_at(problem, EmissionGrain::Inherited)
    }

    /// Generate at a declared emission grain over the declarations the target's identifiers
    /// reach. See [`EmissionGrain`].
    pub fn generate_proof_candidates_at(
        &self,
        problem: &LeanProofProblem,
        grain: EmissionGrain,
    ) -> Result<(LeanDeclarationNames, Vec<LeanProofCandidate>), LeanMathematicsError> {
        let reached = self.reached_declarations(problem)?;
        self.render_candidates(problem, &reached, grain)
    }

    /// Generate over an explicitly supplied declaration family: the organs one conducted route
    /// reached. Names outside the conditioned body are ignored; an empty admitted family refuses.
    pub fn generate_proof_candidates_for(
        &self,
        problem: &LeanProofProblem,
        declarations: &BTreeSet<String>,
        grain: EmissionGrain,
    ) -> Result<(LeanDeclarationNames, Vec<LeanProofCandidate>), LeanMathematicsError> {
        problem.validate()?;
        let mut reached = BTreeSet::new();
        for (identity, organ) in self.declarations.iter() {
            if declarations.contains(&organ.name) {
                reached.insert(identity.clone());
            }
        }
        if reached.is_empty() {
            return Err(LeanMathematicsError::NoLocalDeclarations);
        }
        self.render_candidates(problem, &reached, grain)
    }

    /// The declaration identities the target header reaches through its own identifiers.
    fn reached_declarations(
        &self,
        problem: &LeanProofProblem,
    ) -> Result<BTreeSet<String>, LeanMathematicsError> {
        problem.validate()?;
        let target_binders =
            parse_binder_charts(&format!("{}\n{}", problem.prefix, problem.theorem_header));
        let target_names = target_binders
            .iter()
            .map(|binder| binder.name.clone())
            .collect::<BTreeSet<_>>();
        let target_identifiers = lean_identifiers(&problem.theorem_header)
            .difference(&target_names)
            .filter(|identifier| !lean_keyword(identifier))
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut reached = BTreeSet::new();
        for identifier in &target_identifiers {
            if let Some(declarations) = self.identifier_incidence.get(identifier) {
                for identity in declarations {
                    let Some(organ) = self.declarations.get(identity) else {
                        return Err(LeanMathematicsError::InvalidRest);
                    };
                    if problem.source_scope.is_empty()
                        || problem
                            .source_scope
                            .iter()
                            .any(|scope| organ.source.ends_with(scope))
                    {
                        reached.insert(identity.clone());
                    }
                }
            }
        }
        if reached.is_empty() {
            return Err(LeanMathematicsError::NoLocalDeclarations);
        }
        Ok(reached)
    }

    fn render_candidates(
        &self,
        problem: &LeanProofProblem,
        reached: &BTreeSet<String>,
        grain: EmissionGrain,
    ) -> Result<(LeanDeclarationNames, Vec<LeanProofCandidate>), LeanMathematicsError> {
        let target_binders =
            parse_binder_charts(&format!("{}\n{}", problem.prefix, problem.theorem_header));
        let target_names = target_binders
            .iter()
            .map(|binder| binder.name.clone())
            .collect::<BTreeSet<_>>();

        // `assumption` is a genuine inherited closing morphology. It is essential after a
        // returned equivalence has rewritten the target onto an already caused hypothesis; using
        // only arithmetic or automation closers needlessly leaves that exact local path open.
        let mut closers = LocalSequence::new();
        for tactic in ["assumption", "nlinarith", "linarith", "ring", "aesop"] {
            if self.receipt.tactic_species.contains(tactic) {
                closers.push(Arc::<str>::from(tactic));
            }
        }
        let mut organs = LocalSequence::with_capacity(reached.len());
        let mut organ_names = LocalSequence::with_capacity(reached.len());
        for identity in reached {
            let organ = self
                .declarations
                .get(identity)
                .ok_or(LeanMathematicsError::InvalidRest)?;
            organ_names.push(Arc::<str>::from(organ.name.as_str()));
            organs.push(organ);
        }
        let mut candidates = Vec::new();
        for closer in &closers {
            push_candidate(
                &mut candidates,
                format!("by\n  {closer}"),
                vec![LeanProofMotion::Close {
                    tactic: Arc::clone(closer),
                }],
                LocalSet::new(),
            )?;
        }
        for (organ, organ_name) in organs.iter().zip(&organ_names) {
            let application = match grain {
                EmissionGrain::Inherited => declaration_application(organ, &target_names),
                EmissionGrain::Typed => declaration_application_in_frame(organ, &target_names),
            };
            for (prefix, motion) in [
                (
                    "exact",
                    LeanProofMotion::Direct {
                        declaration: Arc::clone(organ_name),
                    },
                ),
                (
                    "simpa using",
                    LeanProofMotion::Direct {
                        declaration: Arc::clone(organ_name),
                    },
                ),
            ] {
                push_candidate(
                    &mut candidates,
                    format!("by\n  {prefix} {application}"),
                    vec![motion],
                    LocalSet::from([Arc::clone(organ_name)]),
                )?;
            }
            if organ
                .result_constructors
                .contains(&LeanResultConstructor::Conjunction)
            {
                let target_arguments = target_binders
                    .iter()
                    .filter(|binder| binder.explicit)
                    .map(|binder| binder.name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ");
                for projection in [1_u8, 2_u8] {
                    let projected = if target_arguments.is_empty() {
                        format!("{}.{}", organ.name, projection)
                    } else {
                        format!("{}.{} {}", organ.name, projection, target_arguments)
                    };
                    for prefix in ["exact", "simpa using"] {
                        push_candidate(
                            &mut candidates,
                            format!("by\n  {prefix} {projected}"),
                            vec![LeanProofMotion::Project {
                                declaration: Arc::clone(organ_name),
                                projection,
                            }],
                            LocalSet::from([Arc::clone(organ_name)]),
                        )?;
                    }
                }
            }
            for closer in &closers {
                // **`rw` demands an equality or an iff.** At the typed grain the node's `v` decides
                // this before the kernel is asked; at the inherited grain it was offered to every
                // organ, which is the whole of the 105 structural refusals a seven-declaration
                // corpus returned.
                if grain == EmissionGrain::Inherited || organ.rewritable() {
                    push_candidate(
                        &mut candidates,
                        format!("by\n  rw [{}]\n  {closer}", organ.name),
                        vec![
                            LeanProofMotion::Rewrite {
                                declaration: Arc::clone(organ_name),
                            },
                            LeanProofMotion::Close {
                                tactic: Arc::clone(closer),
                            },
                        ],
                        LocalSet::from([Arc::clone(organ_name)]),
                    )?;
                }
                push_candidate(
                    &mut candidates,
                    format!("by\n  have generated := {application}\n  {closer}"),
                    vec![
                        LeanProofMotion::IntroduceFact {
                            declaration: Arc::clone(organ_name),
                        },
                        LeanProofMotion::Close {
                            tactic: Arc::clone(closer),
                        },
                    ],
                    LocalSet::from([Arc::clone(organ_name)]),
                )?;
            }
            if let Some(assumption) = closers
                .iter()
                .find(|closer| closer.as_ref() == "assumption")
            {
                for depth in [2_u8, 3_u8] {
                    let mut proof = String::from("by");
                    for _ in 0..depth {
                        proof.push_str("\n  apply ");
                        proof.push_str(&organ.name);
                    }
                    proof.push_str("\n  assumption");
                    push_candidate(
                        &mut candidates,
                        proof,
                        vec![
                            LeanProofMotion::RecurApply {
                                declaration: Arc::clone(organ_name),
                                depth,
                            },
                            LeanProofMotion::Close {
                                tactic: Arc::clone(assumption),
                            },
                        ],
                        LocalSet::from([Arc::clone(organ_name)]),
                    )?;
                }
            }
        }
        for hypothesis in target_binders
            .iter()
            .filter(|binder| binder.explicit && binder.name.starts_with('h'))
        {
            // **`contrapose!` changes the TYPE of the hypothesis it names**, and the node does not
            // model that. `ℋ` — `H.0362`'s hypotheses-and-branch-data — is the component, and it is
            // not tracked across a tactic that rewrites a hypothesis in place: the emission feeds
            // the post-contrapose `hc` into a slot typed for the pre-contrapose one, which is an
            // `Application type mismatch` however correct the arity.
            //
            // The recognition arm found this rather than assuming it: with `rw` gated on `v` and
            // every application built in frame, **every surviving structural refusal came from this
            // family**. A typed emission may not offer an edge it cannot type, so the family is
            // inadmissible at this grain — a declared **coverage** bound, like an unclassified
            // conclusion, and not a correctness one.
            if grain == EmissionGrain::Typed {
                continue;
            }
            let hypothesis_name = Arc::<str>::from(hypothesis.name.as_str());
            for (organ, organ_name) in organs.iter().zip(&organ_names) {
                let application = match grain {
                    EmissionGrain::Inherited => declaration_application_with_substitute(
                        organ,
                        &target_names,
                        &hypothesis.name,
                    ),
                    EmissionGrain::Typed => declaration_application_in_frame_with_substitute(
                        organ,
                        &target_names,
                        &hypothesis.name,
                    ),
                };
                push_candidate(
                    &mut candidates,
                    format!(
                        "by\n  contrapose! {}\n  exact {application}",
                        hypothesis.name
                    ),
                    vec![LeanProofMotion::Contrapose {
                        hypothesis: Arc::clone(&hypothesis_name),
                        declaration: Arc::clone(organ_name),
                    }],
                    LocalSet::from([Arc::clone(organ_name)]),
                )?;
            }
        }
        for (rewrite, rewrite_name) in organs.iter().zip(&organ_names) {
            // The composed family rewrites by one organ and introduces another. Its rewrite half is
            // governed by the same `v`, and at the inherited grain it is the larger source of the
            // structural refusals: `D(D-1)C` of them against the single family's `DC`.
            if grain == EmissionGrain::Typed && !rewrite.rewritable() {
                continue;
            }
            for (fact, fact_name) in organs.iter().zip(&organ_names) {
                if rewrite.name == fact.name {
                    continue;
                }
                let application = match grain {
                    EmissionGrain::Inherited => declaration_application(fact, &target_names),
                    EmissionGrain::Typed => declaration_application_in_frame(fact, &target_names),
                };
                for closer in &closers {
                    push_candidate(
                        &mut candidates,
                        format!(
                            "by\n  rw [{}]\n  have generated := {}\n  {closer}",
                            rewrite.name, application
                        ),
                        vec![
                            LeanProofMotion::Rewrite {
                                declaration: Arc::clone(rewrite_name),
                            },
                            LeanProofMotion::IntroduceFact {
                                declaration: Arc::clone(fact_name),
                            },
                            LeanProofMotion::Close {
                                tactic: Arc::clone(closer),
                            },
                        ],
                        LocalSet::from([Arc::clone(rewrite_name), Arc::clone(fact_name)]),
                    )?;
                }
            }
        }
        if candidates.is_empty() {
            return Err(LeanMathematicsError::NoProofCandidates);
        }
        let reached_names = organs
            .iter()
            .map(|organ| organ.name.clone())
            .collect::<LeanDeclarationNames>();
        Ok((reached_names, candidates))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CORPUS: &str = "theorem alpha (n : Nat) : n + 0 = n := by\n  simp\n\n\
theorem beta (n : Nat) : 0 + n = n := by\n  rw [Nat.zero_add]\n\n\
theorem gamma (n : Nat) : n + 0 = 0 + n := by\n  rw [alpha, beta]\n";

    fn problem() -> LeanProofProblem {
        LeanProofProblem {
            identity: "delta".to_owned(),
            source_scope: BTreeSet::new(),
            prefix: "import Mathlib".to_owned(),
            theorem_header: "theorem delta (n : Nat) : 0 + n = n + 0".to_owned(),
            suffix: String::new(),
        }
    }

    #[test]
    fn the_candidate_family_is_a_function_of_the_supplied_route() {
        let documents = vec![LeanSourceDocument::new("Test/Route.lean", CORPUS)];
        let ecology = LeanMathematicsEcology::condition(&documents).expect("conditions");
        let alpha = ecology
            .generate_proof_candidates_for(
                &problem(),
                &BTreeSet::from(["alpha".to_owned()]),
                EmissionGrain::Inherited,
            )
            .expect("alpha family");
        let beta = ecology
            .generate_proof_candidates_for(
                &problem(),
                &BTreeSet::from(["beta".to_owned()]),
                EmissionGrain::Inherited,
            )
            .expect("beta family");
        let again = ecology
            .generate_proof_candidates_for(
                &problem(),
                &BTreeSet::from(["alpha".to_owned()]),
                EmissionGrain::Inherited,
            )
            .expect("alpha family again");
        assert_eq!(alpha.1, again.1, "the same route renders the same family");
        assert_ne!(alpha.1, beta.1, "different routes render different families");
        assert!(alpha.1.iter().all(|candidate| !candidate.proof.contains("beta")));
        assert!(alpha.1.iter().any(|candidate| candidate.proof.contains("alpha")));
        assert!(ecology
            .generate_proof_candidates_for(
                &problem(),
                &BTreeSet::from(["omega".to_owned()]),
                EmissionGrain::Inherited,
            )
            .is_err());
    }
}
