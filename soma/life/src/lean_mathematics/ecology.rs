use super::syntax::*;
use super::*;

impl LeanMathematicsEcology {
    /// Mount the inherited Lean-facing organs without any developmental mathematics.
    pub fn mount() -> Self {
        let mut ecology = Self {
            schema: REST_SCHEMA.to_owned(),
            generation: 1,
            declarations: LocalRelations::new(),
            identifier_incidence: LocalRelations::new(),
            receipt: LeanConditioningReceipt {
                retained_source_surfaces: 0,
                mounted_codecs: BTreeSet::from([
                    "contrapose-hypothesis".to_owned(),
                    "direct-application".to_owned(),
                    "introduce-local-fact".to_owned(),
                    "recur-local-declaration".to_owned(),
                    "rewrite-goal".to_owned(),
                ]),
                tactic_species: Default::default(),
                ..LeanConditioningReceipt::default()
            },
            returned_theorems: LocalSequence::new(),
            returned_declaration_sources: LocalSequence::new(),
            returned_generated_sources: LocalSequence::new(),
            target_selections: LocalSequence::new(),
            open_kernel_deed: None,
        };
        ecology
            .receipt
            .tactic_species
            .insert("assumption".to_owned());
        ecology
    }

    /// Let Lean documents cross developmentally and retain only the changed declaration
    /// morphology. The source faces do not become part of native standing.
    pub fn train(
        &mut self,
        documents: &[LeanSourceDocument],
    ) -> Result<LeanConditioningReceipt, LeanMathematicsError> {
        if self.open_kernel_deed.is_some() {
            return Err(LeanMathematicsError::KernelDeedAlreadyOpen);
        }
        if documents.is_empty() {
            return Err(LeanMathematicsError::Parse(
                "no Lean developmental material crossed".to_owned(),
            ));
        }
        let mut parsed = Vec::new();
        let mut source_bytes_exposed = 0u64;
        for document in documents {
            source_bytes_exposed = source_bytes_exposed
                .checked_add(
                    u64::try_from(document.text.len())
                        .map_err(|_| LeanMathematicsError::CarrierExtent)?,
                )
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            parsed.extend(parse_declarations(document)?);
        }
        for declaration_at in 0..parsed.len() {
            let identifiers = lean_identifiers(&parsed[declaration_at].proof);
            let mut referenced = BTreeSet::new();
            for identifier in identifiers {
                let known = self
                    .declarations
                    .iter()
                    .any(|(_, declaration)| declaration.name == identifier)
                    || parsed
                        .iter()
                        .any(|declaration| declaration.organ.name == identifier);
                if known {
                    referenced.insert(identifier);
                }
            }
            parsed[declaration_at].organ.referenced_declarations = referenced;
        }

        // Derive the complete delta and every fallible extent before touching the continuing
        // body. The prior implementation cloned the complete mathematical ecology for rollback;
        // training now commits only this caused declaration population.
        let generation = self
            .generation
            .checked_add(1)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let source_documents_exposed = self
            .receipt
            .source_documents_exposed
            .checked_add(
                u64::try_from(documents.len()).map_err(|_| LeanMathematicsError::CarrierExtent)?,
            )
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let source_bytes_exposed = self
            .receipt
            .source_bytes_exposed
            .checked_add(source_bytes_exposed)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let mut binder_charts = self.receipt.binder_charts;
        let mut declaration_relations = self.receipt.declaration_relations;
        for (at, declaration) in parsed.iter().enumerate() {
            binder_charts = binder_charts
                .checked_add(
                    u64::try_from(declaration.organ.binders.len())
                        .map_err(|_| LeanMathematicsError::CarrierExtent)?,
                )
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            declaration_relations = declaration_relations
                .checked_add(
                    u64::try_from(declaration.organ.referenced_declarations.len())
                        .map_err(|_| LeanMathematicsError::CarrierExtent)?,
                )
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            let identity = declaration_identity(&declaration.organ);
            if self.declarations.contains(&identity)
                || parsed[..at]
                    .iter()
                    .any(|prior| declaration_identity(&prior.organ) == identity)
            {
                return Err(LeanMathematicsError::Parse(
                    "one source declares the same theorem identity twice".to_owned(),
                ));
            }
        }
        let declaration_organs = u64::try_from(
            self.declarations
                .len()
                .checked_add(parsed.len())
                .ok_or(LeanMathematicsError::CarrierExtent)?,
        )
        .map_err(|_| LeanMathematicsError::CarrierExtent)?;

        self.generation = generation;
        self.receipt.source_documents_exposed = source_documents_exposed;
        self.receipt.source_bytes_exposed = source_bytes_exposed;
        self.receipt.binder_charts = binder_charts;
        self.receipt.declaration_relations = declaration_relations;
        self.receipt.declaration_organs = declaration_organs;
        for declaration in parsed {
            self.receipt
                .tactic_species
                .extend(declaration.organ.tactic_species.iter().cloned());
            self.receipt
                .result_constructors
                .extend(declaration.organ.result_constructors.iter().copied());
            let identity = declaration_identity(&declaration.organ);
            self.declarations
                .insert(identity.to_owned(), declaration.organ);
            let organ = self
                .declarations
                .get(&identity)
                .expect("the preflighted declaration delta has just committed");
            for identifier in &organ.statement_identifiers {
                insert_declaration_incidence(
                    &mut self.identifier_incidence,
                    identifier.to_owned(),
                    identity.to_owned(),
                );
            }
        }
        debug_assert!(self.validate().is_ok());
        Ok(self.receipt.to_owned())
    }

    pub fn condition(documents: &[LeanSourceDocument]) -> Result<Self, LeanMathematicsError> {
        let mut ecology = Self::mount();
        ecology.train(documents)?;
        Ok(ecology)
    }

    pub fn receipt(&self) -> &LeanConditioningReceipt {
        &self.receipt
    }

    pub const fn generation(&self) -> u64 {
        self.generation
    }

    pub fn returned_theorems(&self) -> &[LeanReturnedTheoremFiber] {
        &self.returned_theorems
    }

    pub fn declarations(&self) -> impl Iterator<Item = &LeanDeclarationOrgan> {
        self.declarations.iter().map(|(_, declaration)| declaration)
    }

    /// Mount every self-emanated declaration named by the target's source scope into the exact
    /// kernel environment. The application supplies only the scope; this continuing owner carries
    /// the returned declaration surface and its lineage across source-detached remount.
    pub fn materialize_kernel_problem(
        &self,
        problem: &LeanProofProblem,
    ) -> Result<LeanProofProblem, LeanMathematicsError> {
        problem.validate()?;
        let mut mounted = problem.to_owned();
        for source in &self.returned_declaration_sources {
            let admitted = problem.source_scope.iter().any(|scope| {
                source.generated_source_identity == *scope
                    || source.generated_source_identity.ends_with(scope)
            });
            if admitted && !mounted.prefix.contains(&source.declaration) {
                mounted.prefix.push_str("\n\n");
                mounted.prefix.push_str(&source.declaration);
            }
        }
        Ok(mounted)
    }

    pub fn to_native_bytes(&self) -> Result<Vec<u8>, LeanMathematicsError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| LeanMathematicsError::Parse(error.to_string()))
    }

    pub fn into_native_rest(
        self,
    ) -> Result<LeanMathematicsNativeRest, LeanMathematicsNativeRestRefusal> {
        if let Err(error) = self.validate() {
            return Err(LeanMathematicsNativeRestRefusal {
                error,
                body: Some(self),
                rest: None,
            });
        }
        match serde_json::to_vec(&self) {
            Ok(bytes) => Ok(LeanMathematicsNativeRest {
                bytes: bytes.into_boxed_slice(),
            }),
            Err(error) => Err(LeanMathematicsNativeRestRefusal {
                error: LeanMathematicsError::Parse(error.to_string()),
                body: Some(self),
                rest: None,
            }),
        }
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, LeanMathematicsError> {
        let ecology: Self =
            serde_json::from_slice(bytes).map_err(|_| LeanMathematicsError::InvalidRest)?;
        ecology.validate()?;
        Ok(ecology)
    }

    fn validate(&self) -> Result<(), LeanMathematicsError> {
        if self.schema != REST_SCHEMA
            || self.generation == 0
            || self.receipt.declaration_organs as usize != self.declarations.len()
            || self.receipt.retained_source_surfaces as usize
                != self.returned_generated_sources.len()
        {
            return Err(LeanMathematicsError::InvalidRest);
        }
        for (identity, organ) in self.declarations.iter() {
            if identity != &declaration_identity(organ)
                || organ.name.is_empty()
                || organ.source.is_empty()
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            for identifier in &organ.statement_identifiers {
                if !self
                    .identifier_incidence
                    .get(identifier)
                    .is_some_and(|names| names.contains(identity))
                {
                    return Err(LeanMathematicsError::InvalidRest);
                }
            }
        }
        let retained_result_constructors: BTreeSet<_> = self
            .declarations
            .iter()
            .map(|(_, organ)| organ)
            .flat_map(|organ| organ.result_constructors.iter().copied())
            .collect();
        if retained_result_constructors != self.receipt.result_constructors {
            return Err(LeanMathematicsError::InvalidRest);
        }
        let mut kernel_admitted_paths = 0u64;
        let mut obstructed_paths = 0u64;
        let mut admitted_declarations = 0u64;
        for (at, fiber) in self.returned_theorems.iter().enumerate() {
            if fiber.theorem.is_empty()
                || fiber.theorem_face_sha256.is_empty()
                || fiber.generated_source_identity.is_empty()
                || fiber.generation == 0
                || fiber.generation > self.generation
                || self.returned_theorems[..at]
                    .iter()
                    .any(|prior| prior.generated_source_identity == fiber.generated_source_identity)
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            kernel_admitted_paths = kernel_admitted_paths
                .checked_add(
                    u64::try_from(fiber.kernel_admitted.len())
                        .map_err(|_| LeanMathematicsError::InvalidRest)?,
                )
                .ok_or(LeanMathematicsError::InvalidRest)?;
            obstructed_paths = obstructed_paths
                .checked_add(
                    u64::try_from(fiber.obstructed.len())
                        .map_err(|_| LeanMathematicsError::InvalidRest)?,
                )
                .ok_or(LeanMathematicsError::InvalidRest)?;
            for path in fiber.kernel_admitted.iter().chain(fiber.obstructed.iter()) {
                if path.proof_sha256.is_empty()
                    || path.source_sha256.is_empty()
                    || path.diagnostic_sha256.is_empty()
                {
                    return Err(LeanMathematicsError::InvalidRest);
                }
            }
            if fiber.declaration_admitted {
                admitted_declarations = admitted_declarations
                    .checked_add(1)
                    .ok_or(LeanMathematicsError::InvalidRest)?;
                let identity = format!("{}#{}", fiber.generated_source_identity, fiber.theorem);
                if fiber.kernel_admitted.is_empty() || !self.declarations.contains(&identity) {
                    return Err(LeanMathematicsError::InvalidRest);
                }
                let Some(mounted) = self.returned_declaration_sources.iter().find(|source| {
                    source.generated_source_identity == fiber.generated_source_identity
                        && source.theorem == fiber.theorem
                        && !source.declaration.trim().is_empty()
                }) else {
                    return Err(LeanMathematicsError::InvalidRest);
                };
                if !proof_family_matches_paths(&mounted.proof_family, &fiber.kernel_admitted) {
                    return Err(LeanMathematicsError::InvalidRest);
                }
            } else if !fiber.kernel_admitted.is_empty() {
                return Err(LeanMathematicsError::InvalidRest);
            }
            for path in &fiber.kernel_admitted {
                let mut matched = false;
                for source in &self.returned_generated_sources {
                    if source.theorem == fiber.theorem
                        && source.candidate_ordinal == path.candidate_ordinal
                        && source.source_sha256 == path.source_sha256
                        && source.proof_sha256 == path.proof_sha256
                        && source
                            .identity
                            .starts_with(&fiber.generated_source_identity)
                    {
                        if matched || sha256(source.source.as_bytes()) != source.source_sha256 {
                            return Err(LeanMathematicsError::InvalidRest);
                        }
                        matched = true;
                    }
                }
                if !matched {
                    return Err(LeanMathematicsError::InvalidRest);
                }
            }
        }
        for (at, source) in self.returned_declaration_sources.iter().enumerate() {
            if source.generated_source_identity.trim().is_empty()
                || source.theorem.trim().is_empty()
                || source.declaration.trim().is_empty()
                || self.returned_declaration_sources[..at].iter().any(|prior| {
                    prior.generated_source_identity == source.generated_source_identity
                })
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }
        for (at, source) in self.returned_generated_sources.iter().enumerate() {
            if source.identity.trim().is_empty()
                || source.theorem.trim().is_empty()
                || source.source.trim().is_empty()
                || source.source_sha256 != sha256(source.source.as_bytes())
                || source.proof_sha256.trim().is_empty()
                || self.returned_generated_sources[..at]
                    .iter()
                    .any(|prior| prior.identity == source.identity)
                || !self.returned_theorems.iter().any(|fiber| {
                    fiber.theorem == source.theorem
                        && fiber.kernel_admitted.iter().any(|path| {
                            path.candidate_ordinal == source.candidate_ordinal
                                && path.source_sha256 == source.source_sha256
                                && path.proof_sha256 == source.proof_sha256
                        })
                })
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }
        if self.receipt.kernel_return_events as usize != self.returned_theorems.len()
            || self.receipt.kernel_admitted_paths != kernel_admitted_paths
            || self.receipt.kernel_obstructed_paths != obstructed_paths
            || self.receipt.self_emanated_declarations != admitted_declarations
        {
            return Err(LeanMathematicsError::InvalidRest);
        }
        for (standing_at, standing) in self.target_selections.iter().enumerate() {
            let request = &standing.request;
            if standing.generation == 0
                || standing.generation > self.generation
                || request.identity.trim().is_empty()
                || request.target_episode.trim().is_empty()
                || request.declared_theorem_faces.is_empty()
                || request.diagnosis.target_episode() != request.target_episode
                || !request
                    .diagnosis
                    .conducts(LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent)
                || self.target_selections[..standing_at]
                    .iter()
                    .any(|prior| prior.request.identity == request.identity)
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            let mut received = LocalSet::new();
            for face in &request.alternatives {
                if !received.insert(face.problem.identity.clone()) {
                    return Err(LeanMathematicsError::InvalidRest);
                }
                face.problem
                    .validate()
                    .map_err(|_| LeanMathematicsError::InvalidRest)?;
            }
            let mut alternative_faces = LocalRelations::<String, ()>::new();
            let alternatives = match &standing.receipt {
                LeanTargetSelectionReceipt::Open(open) => {
                    if open.request != request.identity
                        || open.target_episode != request.target_episode
                        || open.declared_theorem_faces != request.declared_theorem_faces
                        || open.received_theorem_faces != received
                    {
                        return Err(LeanMathematicsError::InvalidRest);
                    }
                    &open.alternatives
                }
                LeanTargetSelectionReceipt::Selected(selected) => {
                    let selected_face = request
                        .alternatives
                        .iter()
                        .find(|face| face.problem.identity == selected.theorem)
                        .ok_or(LeanMathematicsError::InvalidRest)?;
                    if received != request.declared_theorem_faces
                        || selected.deed
                            != format!("{}/kernel-deed/{}", request.identity, standing.generation)
                        || selected.target_episode != request.target_episode
                        || selected.diagnosis != request.diagnosis
                        || !request
                            .diagnosis
                            .conducts(selected_face.diagnosis_requirement)
                        || selected.candidate_ordinals.is_empty()
                        || selected
                            .candidate_ordinals
                            .iter()
                            .enumerate()
                            .any(|(at, ordinal)| *ordinal != u64::try_from(at).unwrap_or(u64::MAX))
                        || (self
                            .open_kernel_deed
                            .as_ref()
                            .is_none_or(|deed| deed.identity != selected.deed)
                            && !self.returned_theorems.iter().any(|fiber| {
                                fiber.theorem == selected.theorem
                                    && fiber.generation
                                        == standing.generation.checked_add(1).unwrap_or(u64::MAX)
                            }))
                    {
                        return Err(LeanMathematicsError::InvalidRest);
                    }
                    if let Some(deed) = self
                        .open_kernel_deed
                        .as_ref()
                        .filter(|deed| deed.identity == selected.deed)
                    {
                        if deed.reached_declarations != selected.reached_declarations
                            || !deed
                                .candidates
                                .iter()
                                .map(|candidate| candidate.ordinal)
                                .eq(selected.candidate_ordinals.iter().copied())
                        {
                            return Err(LeanMathematicsError::InvalidRest);
                        }
                    }
                    &selected.alternatives
                }
            };
            for alternative in alternatives {
                if alternative_faces.contains(&alternative.theorem) {
                    return Err(LeanMathematicsError::InvalidRest);
                }
                alternative_faces.insert(alternative.theorem.clone(), ());
            }
            let mut expected = request.declared_theorem_faces.to_owned();
            expected.extend(received.iter().cloned());
            if !expected
                .iter()
                .all(|identity| alternative_faces.contains(identity))
                || alternative_faces
                    .iter()
                    .any(|(identity, _)| !expected.contains(identity))
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }
        if let Some(deed) = &self.open_kernel_deed {
            if deed.identity != format!("{}/kernel-deed/{}", deed.target_request, self.generation)
                || deed.target_request.trim().is_empty()
                || deed.target_episode.trim().is_empty()
                || deed.diagnosis.target_episode() != deed.target_episode
                || !deed
                    .diagnosis
                    .conducts(LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent)
                || deed.candidates.is_empty()
                || self
                    .returned_theorems
                    .iter()
                    .any(|fiber| fiber.theorem == deed.problem.identity)
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            deed.problem
                .validate()
                .map_err(|_| LeanMathematicsError::InvalidRest)?;
            let kernel_problem = self
                .materialize_kernel_problem(&deed.problem)
                .map_err(|_| LeanMathematicsError::InvalidRest)?;
            let (reached, candidates) = self
                .generate_proof_candidates(&kernel_problem)
                .map_err(|_| LeanMathematicsError::InvalidRest)?;
            if deed.kernel_problem != kernel_problem
                || deed.reached_declarations != reached
                || deed.candidates.as_ref() != candidates.as_slice()
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            for (at, candidate) in deed.candidates.iter().enumerate() {
                if candidate.ordinal
                    != u64::try_from(at).map_err(|_| LeanMathematicsError::InvalidRest)?
                    || deed.candidates[..at]
                        .iter()
                        .any(|prior| prior.ordinal == candidate.ordinal)
                {
                    return Err(LeanMathematicsError::InvalidRest);
                }
            }
        }
        Ok(())
    }

    pub const fn open_kernel_deed(&self) -> Option<&LeanKernelDeed> {
        self.open_kernel_deed.as_ref()
    }

    /// Let the contemporary declaration morphology select one theorem face and open exactly one
    /// immutable kernel-return frontier. The caller supplies alternatives and caused witnesses;
    /// it cannot select the surviving target or manufacture candidate membership.
    /// **Made `pub` 2026-08-14.** This is the entry point of the three-step deed
    /// protocol, and it was `pub(crate)` — which is why
    /// [`LeanMathematicsEcology::receive_kernel_deed_returns`] had eleven test
    /// sites and zero drivers: no driver could open a deed to hand back. The
    /// selection discipline is unchanged and is what makes widening safe — the
    /// caller supplies alternatives and caused witnesses and **cannot select the
    /// surviving target or manufacture candidate membership**.
    pub fn select_and_open_kernel_deed(
        &mut self,
        request: LeanTheoremTargetRequest,
    ) -> Result<LeanTargetSelectionReceipt, LeanMathematicsError> {
        if self.open_kernel_deed.is_some() {
            return Err(LeanMathematicsError::KernelDeedAlreadyOpen);
        }
        if self.target_selections.last().is_some_and(|standing| {
            standing.generation == self.generation
                && matches!(&standing.receipt, LeanTargetSelectionReceipt::Open(_))
        }) {
            return Err(LeanMathematicsError::TargetSelectionAlreadyOpen);
        }
        if self
            .target_selections
            .iter()
            .any(|standing| standing.request.identity == request.identity)
        {
            return Err(LeanMathematicsError::Parse(
                "the target-selection occurrence already crossed".to_owned(),
            ));
        }
        if request.identity.trim().is_empty()
            || request.target_episode.trim().is_empty()
            || request.declared_theorem_faces.is_empty()
            || request.diagnosis.target_episode() != request.target_episode
            || !request
                .diagnosis
                .conducts(LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent)
            || request
                .declared_theorem_faces
                .iter()
                .any(|identity| identity.trim().is_empty())
        {
            return Err(LeanMathematicsError::EmptyProblem);
        }
        let mut received_faces = LocalRelations::<String, usize>::new();
        let mut duplicate_face = false;
        for (face_at, face) in request.alternatives.iter().enumerate() {
            face.problem.validate()?;
            if received_faces.contains(&face.problem.identity) {
                duplicate_face = true;
            } else {
                received_faces.insert(face.problem.identity.clone(), face_at);
            }
        }
        let received_theorem_faces = LocalSet::from_iter(
            received_faces
                .iter()
                .map(|(identity, _)| identity.to_owned()),
        );
        let complete_face_family =
            !duplicate_face && received_theorem_faces == request.declared_theorem_faces;
        let mut alternatives = LocalSequence::with_capacity(
            request
                .declared_theorem_faces
                .len()
                .saturating_add(received_theorem_faces.len()),
        );
        let mut conduct = LeanTargetSelectionConduct::NoCausedFace;
        for declared in &request.declared_theorem_faces {
            let Some(face_at) = received_faces.get(declared) else {
                alternatives.push(LeanTargetAlternativeReceipt {
                    theorem: declared.to_owned(),
                    face_received: false,
                    diagnosis_reached: false,
                    already_returned: false,
                    reached_declarations: 0,
                    candidate_population: 0,
                    obstruction: Some("the declared theorem face did not cross".to_owned()),
                });
                continue;
            };
            let face = request
                .alternatives
                .get(*face_at)
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            let problem = &face.problem;
            let diagnosis_reached = request.diagnosis.conducts(face.diagnosis_requirement);
            let already_returned = self
                .returned_theorems
                .iter()
                .any(|fiber| fiber.theorem == problem.identity);
            if !diagnosis_reached || already_returned {
                alternatives.push(LeanTargetAlternativeReceipt {
                    theorem: problem.identity.clone(),
                    face_received: true,
                    diagnosis_reached,
                    already_returned,
                    reached_declarations: 0,
                    candidate_population: 0,
                    obstruction: Some(if already_returned {
                        "the theorem face has already returned".to_owned()
                    } else {
                        "the closed diagnosis did not reach this theorem face".to_owned()
                    }),
                });
                continue;
            }
            let kernel_problem = self.materialize_kernel_problem(problem)?;
            match self.generate_proof_candidates(&kernel_problem) {
                Ok((reached, candidates)) => {
                    alternatives.push(LeanTargetAlternativeReceipt {
                        theorem: problem.identity.clone(),
                        face_received: true,
                        diagnosis_reached: true,
                        already_returned: false,
                        reached_declarations: reached.len(),
                        candidate_population: candidates.len(),
                        obstruction: None,
                    });
                    conduct.receive(LeanViableTarget {
                        problem: problem.clone(),
                        kernel_problem,
                        reached_declarations: reached,
                        candidates: LocalSequence::from_iter(candidates),
                        diagnosis: request.diagnosis.to_owned(),
                    });
                }
                Err(LeanMathematicsError::NoLocalDeclarations) => {
                    alternatives.push(LeanTargetAlternativeReceipt {
                        theorem: problem.identity.clone(),
                        face_received: true,
                        diagnosis_reached: true,
                        already_returned: false,
                        reached_declarations: 0,
                        candidate_population: 0,
                        obstruction: Some(
                            "no returned declaration reaches this theorem".to_owned(),
                        ),
                    });
                }
                Err(LeanMathematicsError::NoProofCandidates) => {
                    alternatives.push(LeanTargetAlternativeReceipt {
                        theorem: problem.identity.clone(),
                        face_received: true,
                        diagnosis_reached: true,
                        already_returned: false,
                        reached_declarations: 0,
                        candidate_population: 0,
                        obstruction: Some("the reached declarations emit no proof path".to_owned()),
                    });
                }
                Err(error) => return Err(error),
            }
        }
        for unknown in received_theorem_faces
            .iter()
            .filter(|identity| !request.declared_theorem_faces.contains(*identity))
        {
            alternatives.push(LeanTargetAlternativeReceipt {
                theorem: unknown.to_owned(),
                face_received: true,
                diagnosis_reached: false,
                already_returned: false,
                reached_declarations: 0,
                candidate_population: 0,
                obstruction: Some("the theorem face was not declared by this family".to_owned()),
            });
        }
        if let Some(LeanViableTarget {
            problem,
            kernel_problem,
            reached_declarations,
            candidates,
            diagnosis,
        }) = conduct.close(complete_face_family)
        {
            let deed_identity = format!("{}/kernel-deed/{}", request.identity, self.generation);
            let selected_face = LeanKernelDeedFace {
                deed: deed_identity.clone(),
                theorem: problem.identity.clone(),
                target_episode: request.target_episode.clone(),
                diagnosis: diagnosis.to_owned(),
                reached_declarations: reached_declarations.to_owned(),
                candidate_ordinals: LocalSequence::from_iter(
                    candidates.iter().map(|candidate| candidate.ordinal),
                ),
                alternatives,
            };
            self.open_kernel_deed = Some(LeanKernelDeed {
                identity: deed_identity,
                target_request: request.identity.clone(),
                target_episode: request.target_episode.clone(),
                diagnosis,
                problem,
                kernel_problem,
                reached_declarations,
                candidates,
            });
            let receipt = LeanTargetSelectionReceipt::Selected(selected_face);
            self.target_selections.push(LeanTargetSelectionStanding {
                generation: self.generation,
                request,
                receipt: receipt.to_owned(),
            });
            Ok(receipt)
        } else {
            let receipt = LeanTargetSelectionReceipt::Open(OpenTargetSelection {
                request: request.identity,
                target_episode: request.target_episode,
                declared_theorem_faces: request.declared_theorem_faces,
                received_theorem_faces,
                alternatives,
            });
            let request = match &receipt {
                LeanTargetSelectionReceipt::Open(open) => LeanTheoremTargetRequest {
                    identity: open.request.clone(),
                    target_episode: open.target_episode.clone(),
                    declared_theorem_faces: open.declared_theorem_faces.to_owned(),
                    alternatives: request.alternatives,
                    diagnosis: request.diagnosis,
                },
                LeanTargetSelectionReceipt::Selected(_) => unreachable!(),
            };
            self.target_selections.push(LeanTargetSelectionStanding {
                generation: self.generation,
                request,
                receipt: receipt.to_owned(),
            });
            Ok(receipt)
        }
    }

    /// Receive exactly one kernel verdict for every immutable candidate member, cultivate the
    /// returned theorem fiber atomically, and close this owner's formal frontier.
    pub fn receive_kernel_deed_returns(
        &mut self,
        deed_identity: &str,
        returns: LeanKernelReturnFamily,
    ) -> Result<LeanKernelDeedCompletion, LeanMathematicsError> {
        let deed = self
            .open_kernel_deed
            .as_ref()
            .ok_or(LeanMathematicsError::WrongKernelDeed)?;
        if deed.identity != deed_identity {
            return Err(LeanMathematicsError::WrongKernelDeed);
        }
        let ordered_returns = returns.align_to(&deed.candidates)?;
        let round = proof_round(
            0,
            "the complete Lean-owned kernel deed returned",
            &ordered_returns,
        )?;
        let run = LeanProofRun {
            problem: deed.problem.identity.clone(),
            kernel_problem: deed.kernel_problem.clone(),
            reached_declarations: deed.reached_declarations.clone(),
            candidates: deed.candidates.to_owned(),
            returns: ordered_returns,
            rounds: LocalSequence::from([round]),
        };
        let problem = deed.problem.clone();
        let target_episode = deed.target_episode.to_owned();
        let diagnosis = deed.diagnosis.to_owned();
        let cultivation = self.receive_kernel_run(&problem, &run)?;
        let returned = self
            .returned_theorems
            .last()
            .cloned()
            .expect("successful cultivation atomically appends its returned theorem fiber");
        let kernel_admitted_sources = LocalSequence::from_iter(
            self.returned_generated_sources
                .iter()
                .filter(|source| {
                    source.theorem == returned.theorem
                        && source
                            .identity
                            .starts_with(&returned.generated_source_identity)
                })
                .cloned(),
        );
        self.open_kernel_deed = None;
        debug_assert!(self.validate().is_ok());
        Ok(LeanKernelDeedCompletion {
            deed: deed_identity.to_owned(),
            target_episode,
            diagnosis,
            returned,
            cultivation,
            kernel_admitted_sources,
        })
    }

    fn validate_kernel_run(
        &self,
        problem: &LeanProofProblem,
        run: &LeanProofRun,
    ) -> Result<(), LeanMathematicsError> {
        problem.validate()?;
        let kernel_problem = self.materialize_kernel_problem(problem)?;
        let (expected_reached, expected_candidates) =
            self.generate_proof_candidates(&kernel_problem)?;
        if run.problem != problem.identity
            || run.kernel_problem != kernel_problem
            || run.reached_declarations != expected_reached
            || run.candidates.as_ref() != expected_candidates.as_slice()
            || run.returns.members().len() != run.candidates.len()
        {
            return Err(LeanMathematicsError::InvalidRest);
        }

        for (at, candidate) in run.candidates.iter().enumerate() {
            if run.candidates[..at]
                .iter()
                .any(|prior| prior.ordinal == candidate.ordinal)
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }

        for (at, returned) in run.returns.members().iter().enumerate() {
            let candidate = run
                .candidates
                .iter()
                .find(|candidate| candidate.ordinal == returned.candidate.ordinal)
                .ok_or(LeanMathematicsError::InvalidRest)?;
            let source = kernel_problem.render(&candidate.proof)?;
            if candidate != &returned.candidate
                || run.returns.members()[..at]
                    .iter()
                    .any(|prior| prior.candidate.ordinal == returned.candidate.ordinal)
                || returned.source_sha256 != sha256(source.as_bytes())
                || returned.diagnostic_sha256 != sha256(returned.diagnostic.as_bytes())
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }

        let mut returned_at = 0usize;
        for (round_at, round) in run.rounds.iter().enumerate() {
            if round.ordinal
                != u64::try_from(round_at).map_err(|_| LeanMathematicsError::CarrierExtent)?
            {
                return Err(LeanMathematicsError::InvalidRest);
            }
            let mut kernel_admitted = 0u64;
            let mut obstructed = 0u64;
            for candidate_ordinal in &round.candidate_ordinals {
                let returned = run
                    .returns
                    .members()
                    .get(returned_at)
                    .ok_or(LeanMathematicsError::InvalidRest)?;
                if returned.candidate.ordinal != *candidate_ordinal {
                    return Err(LeanMathematicsError::InvalidRest);
                }
                if returned.kernel_admitted() {
                    kernel_admitted = kernel_admitted
                        .checked_add(1)
                        .ok_or(LeanMathematicsError::CarrierExtent)?;
                } else {
                    obstructed = obstructed
                        .checked_add(1)
                        .ok_or(LeanMathematicsError::CarrierExtent)?;
                }
                returned_at = returned_at
                    .checked_add(1)
                    .ok_or(LeanMathematicsError::CarrierExtent)?;
            }
            if round.kernel_admitted != kernel_admitted || round.obstructed != obstructed {
                return Err(LeanMathematicsError::InvalidRest);
            }
        }
        if returned_at != run.returns.members().len() || (returned_at > 0 && run.rounds.is_empty())
        {
            return Err(LeanMathematicsError::InvalidRest);
        }
        Ok(())
    }

    /// Let the complete kernel return family change this same mathematical body. Every admitted
    /// path founds one proof section of the same theorem organ; no path is ranked or promoted into
    /// the admission law. Obstructed paths remain exact obstruction fibers. The family-composite
    /// declaration remains mounted so later conduct can use it after source-detached remount.
    fn receive_kernel_run(
        &mut self,
        problem: &LeanProofProblem,
        run: &LeanProofRun,
    ) -> Result<LeanKernelCultivationReceipt, LeanMathematicsError> {
        self.validate_kernel_run(problem, run)?;
        let generated_source_identity = format!(
            "self-emanated/{}.lean",
            safe_identity(problem.identity.as_str())
        );
        if self
            .returned_theorems
            .iter()
            .any(|fiber| fiber.generated_source_identity == generated_source_identity)
        {
            return Err(LeanMathematicsError::Parse(
                "the same theorem return already inhabits this mathematical body".to_owned(),
            ));
        }

        let generation_before = self.generation;
        let generation_after = generation_before
            .checked_add(1)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let kernel_admitted_path_population = u64::try_from(run.returns.kernel_admitted_extent())
            .map_err(|_| LeanMathematicsError::CarrierExtent)?;
        let crossed_candidate_population = u64::try_from(run.returns.members().len())
            .map_err(|_| LeanMathematicsError::CarrierExtent)?;
        let complete_candidate_population =
            u64::try_from(run.candidates.len()).map_err(|_| LeanMathematicsError::CarrierExtent)?;
        let obstructed_path_population = crossed_candidate_population
            .checked_sub(kernel_admitted_path_population)
            .ok_or(LeanMathematicsError::InvalidRest)?;
        let unmaterialized_path_population = complete_candidate_population
            .checked_sub(crossed_candidate_population)
            .ok_or(LeanMathematicsError::InvalidRest)?;
        let kernel_return_events = self
            .receipt
            .kernel_return_events
            .checked_add(1)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let kernel_admitted_paths = self
            .receipt
            .kernel_admitted_paths
            .checked_add(kernel_admitted_path_population)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let kernel_obstructed_paths = self
            .receipt
            .kernel_obstructed_paths
            .checked_add(obstructed_path_population)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
        let declaration_organs_before = self.receipt.declaration_organs;

        let mut generated_declaration_source = None;
        let mut binder_charts = self.receipt.binder_charts;
        let mut declaration_relations = self.receipt.declaration_relations;
        let mut declaration_organs_after = declaration_organs_before;
        let mut self_emanated_declarations = self.receipt.self_emanated_declarations;
        let mut generated_organ: Option<LeanDeclarationOrgan> = None;
        let mut proof_family = LocalSequence::new();
        let mut kernel_admitted_sources = LocalSequence::new();
        for returned in run.returns.kernel_admitted() {
            let generated_source = problem.render(&returned.candidate.proof)?;
            let mut parsed = parse_declarations(&LeanSourceDocument::new(
                generated_source_identity.to_owned(),
                generated_source.to_owned(),
            ))?;
            if parsed.len() != 1 {
                return Err(LeanMathematicsError::Parse(
                    "one kernel-admitted theorem path did not form exactly one declaration organ"
                        .to_owned(),
                ));
            }
            let mut declaration = parsed.pop().ok_or(LeanMathematicsError::InvalidRest)?;
            if declaration.organ.name != problem.identity || !parsed.is_empty() {
                return Err(LeanMathematicsError::InvalidRest);
            }
            for lineage in &returned.candidate.declaration_lineage {
                declaration
                    .organ
                    .referenced_declarations
                    .insert(lineage.as_ref().to_owned());
            }
            if let Some(organ) = &mut generated_organ {
                merge_kernel_admitted_organ(organ, declaration.organ)?;
            } else {
                generated_organ = Some(declaration.organ);
            }
            let proof = declaration_proof_face(returned);
            proof_family.push(proof);
            kernel_admitted_sources.push(LeanGeneratedTheoremSourceFace {
                identity: format!(
                    "{generated_source_identity}/candidate-{}",
                    returned.candidate.ordinal
                ),
                theorem: problem.identity.clone(),
                candidate_ordinal: returned.candidate.ordinal,
                source: generated_source,
                source_sha256: returned.source_sha256.clone(),
                proof_sha256: sha256(returned.candidate.proof.as_bytes()),
            });
        }
        if let Some(organ) = &generated_organ {
            let identity = declaration_identity(organ);
            if self.declarations.contains(&identity) {
                return Err(LeanMathematicsError::Parse(
                    "the kernel-admitted theorem organ already exists".to_owned(),
                ));
            }
            binder_charts = binder_charts
                .checked_add(
                    u64::try_from(organ.binders.len())
                        .map_err(|_| LeanMathematicsError::CarrierExtent)?,
                )
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            declaration_relations = declaration_relations
                .checked_add(
                    u64::try_from(organ.referenced_declarations.len())
                        .map_err(|_| LeanMathematicsError::CarrierExtent)?,
                )
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            declaration_organs_after = declaration_organs_after
                .checked_add(1)
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            self_emanated_declarations = self_emanated_declarations
                .checked_add(1)
                .ok_or(LeanMathematicsError::CarrierExtent)?;
            generated_declaration_source = Some(LeanReturnedDeclarationSource {
                generated_source_identity: generated_source_identity.to_owned(),
                theorem: problem.identity.to_owned(),
                proof_family: proof_family.to_owned(),
                declaration: family_composite_declaration(problem, &run.returns)?,
            });
        }
        let declaration_conduct = if proof_family.is_empty() {
            LeanDeclarationConduct::NoKernelAdmittedProof
        } else {
            LeanDeclarationConduct::KernelAdmittedFamily {
                proofs: proof_family.to_owned(),
            }
        };
        let retained_source_surfaces = self
            .receipt
            .retained_source_surfaces
            .checked_add(
                u64::try_from(kernel_admitted_sources.len())
                    .map_err(|_| LeanMathematicsError::CarrierExtent)?,
            )
            .ok_or(LeanMathematicsError::CarrierExtent)?;

        let mut kernel_admitted = LocalSequence::new();
        let mut obstructed = LocalSequence::new();
        for returned in run.returns.members() {
            let path = returned_proof_path(returned);
            if returned.kernel_admitted() {
                kernel_admitted.push(path);
            } else {
                obstructed.push(path);
            }
        }
        let fiber = LeanReturnedTheoremFiber {
            theorem: problem.identity.to_owned(),
            theorem_face_sha256: sha256(problem.theorem_header.as_bytes()),
            generated_source_identity: generated_source_identity.to_owned(),
            generation: generation_after,
            declaration_admitted: generated_organ.is_some(),
            kernel_admitted,
            obstructed,
        };

        if let Some(organ) = generated_organ {
            self.receipt
                .tactic_species
                .extend(organ.tactic_species.iter().cloned());
            self.receipt
                .result_constructors
                .extend(organ.result_constructors.iter().copied());
            let identity = declaration_identity(&organ);
            self.declarations.insert(identity.to_owned(), organ);
            let organ = self
                .declarations
                .get(&identity)
                .expect("the preflighted returned theorem organ has just committed");
            for identifier in &organ.statement_identifiers {
                insert_declaration_incidence(
                    &mut self.identifier_incidence,
                    identifier.to_owned(),
                    identity.to_owned(),
                );
            }
        }
        self.generation = generation_after;
        self.receipt.kernel_return_events = kernel_return_events;
        self.receipt.kernel_admitted_paths = kernel_admitted_paths;
        self.receipt.kernel_obstructed_paths = kernel_obstructed_paths;
        self.receipt.self_emanated_declarations = self_emanated_declarations;
        self.receipt.binder_charts = binder_charts;
        self.receipt.declaration_relations = declaration_relations;
        self.receipt.declaration_organs = declaration_organs_after;
        self.receipt.retained_source_surfaces = retained_source_surfaces;
        self.returned_theorems.push(fiber);
        let declaration_admitted = generated_declaration_source.is_some();
        if let Some(source) = generated_declaration_source {
            self.returned_declaration_sources.push(source);
        }
        self.returned_generated_sources
            .extend(kernel_admitted_sources.iter().cloned());
        if self.open_kernel_deed.is_none() {
            debug_assert!(self.validate().is_ok());
        }

        Ok(LeanKernelCultivationReceipt {
            theorem: problem.identity.to_owned(),
            generated_source_identity,
            generation_before,
            generation_after,
            declaration_organs_before,
            declaration_organs_after,
            complete_candidate_population,
            crossed_candidate_population,
            kernel_admitted_path_population,
            obstructed_path_population,
            unmaterialized_path_population,
            declaration_admitted,
            declaration_conduct,
            retained_source_surfaces: self.receipt.retained_source_surfaces,
        })
    }
}
