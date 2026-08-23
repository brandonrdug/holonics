//! Cross-owner validation for one proposed mathematical particle.

pub(super) mod typing;
use super::admission::ProposalOwnerAttempt;
use super::*;
use holonic_engine::exact_owner_testimony::ExactOwnerKind;
use holonic_engine::source_occurrence::OccurrenceWitness;
use typing::*;

impl MathematicalParticle {
    pub fn found(input: MathematicalParticleInput) -> Result<Self, MathematicalParticleError> {
        if input.occurrence.is_empty()
            || input.source_testimonies.len() < 2
            || input.presentation_fibres.is_empty()
        {
            return Err(MathematicalParticleError::EmptyParticle);
        }
        input
            .operation
            .shape
            .validate()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        let closure = input
            .operation
            .closure()
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        if !closure.open_questions.is_empty() {
            return Err(MathematicalParticleError::OperationShapeOpen);
        }
        let source_addresses = source_addresses(&input.source_testimonies);
        let ports = input
            .operation
            .shape
            .boundaries
            .objects
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let laws = input
            .operation
            .shape
            .laws
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let artifacts = input
            .source_testimonies
            .iter()
            .map(|testimony| testimony.artifact.occurrence.clone())
            .chain(
                input
                    .exterior_artifacts
                    .iter()
                    .map(|artifact| artifact.occurrence.clone()),
            )
            .collect::<BTreeSet<_>>();
        if artifacts.len() != input.source_testimonies.len() + input.exterior_artifacts.len()
            || input
                .exterior_artifacts
                .iter()
                .any(|artifact| artifact.occurrence.is_empty() || artifact.sha256.is_empty())
        {
            return Err(MathematicalParticleError::MalformedRenderingReceiver);
        }

        if input.linear_returns.is_empty() || input.quantity_returns.is_empty() {
            return Err(MathematicalParticleError::MissingExactOwnerReturn);
        }
        if !input.linear_returns.iter().any(|linear| {
            input.quantity_returns.iter().any(|quantity| {
                linear.passage.passage == quantity.passage.passage
                    && linear.passage.branch != quantity.passage.branch
            })
        }) {
            return Err(MathematicalParticleError::OwnersDoNotSharePassage);
        }
        if input.value_receivers.is_empty()
            || input.rendering_receivers.is_empty()
            || input.sameness.is_empty()
        {
            return Err(MathematicalParticleError::MissingReceiverOrSameness);
        }

        require_unique(
            input.carriers.iter().map(|carrier| carrier.id),
            MathematicalParticleError::DuplicateCarrier,
        )?;
        require_unique(
            input.binders.iter().map(|binder| binder.id),
            MathematicalParticleError::DuplicateBinder,
        )?;
        require_unique(
            input.hypotheses.iter().map(|hypothesis| hypothesis.id),
            MathematicalParticleError::DuplicateHypothesis,
        )?;
        require_unique(
            input.branches.iter().map(|branch| branch.id),
            MathematicalParticleError::DuplicateBranch,
        )?;
        require_unique(
            input
                .passages
                .iter()
                .map(|passage| passage.occurrence.as_str()),
            MathematicalParticleError::DuplicatePassage,
        )?;

        let carrier_ids = input
            .carriers
            .iter()
            .map(|carrier| carrier.id)
            .collect::<BTreeSet<_>>();
        let hypothesis_ids = input
            .hypotheses
            .iter()
            .map(|value| value.id)
            .collect::<BTreeSet<_>>();
        let branch_ids = input
            .branches
            .iter()
            .map(|value| value.id)
            .collect::<BTreeSet<_>>();
        for carrier in &input.carriers {
            require_sources(&carrier.source_occurrences, &source_addresses)?;
            if carrier.owner_carrier.is_empty() || carrier.equality_law_lineage.is_empty() {
                return Err(MathematicalParticleError::EmptyCarrierLaw(carrier.id));
            }
        }
        for binder in &input.binders {
            require_sources(&binder.source_occurrences, &source_addresses)?;
            require_subset(
                &binder.ports,
                &ports,
                MathematicalParticleError::UnknownPort,
            )?;
            require_subset(&binder.laws, &laws, MathematicalParticleError::UnknownLaw)?;
        }
        validate_ports(
            &input.ports,
            &ports,
            &input.carriers,
            &input.binders,
            &input.operation,
        )?;
        for hypothesis in &input.hypotheses {
            require_sources(&hypothesis.source_occurrences, &source_addresses)?;
            require_subset(
                &hypothesis.licenses,
                &laws,
                MathematicalParticleError::UnknownLaw,
            )?;
            require_subset(
                &hypothesis.branches,
                &branch_ids,
                MathematicalParticleError::UnknownBranch,
            )?;
        }
        for passage in &input.passages {
            // Constructor already proved this. Reconstructing is the anti-forgery check after the
            // passage crossed an ownership boundary.
            let rebuilt = TypedPassage::found(
                passage.occurrence.clone(),
                passage.staging_sources.clone(),
                passage.staging.clone(),
                passage.branches.clone(),
                &input.operation,
                &source_addresses,
            )?;
            if rebuilt.addressed != passage.addressed
                || rebuilt.source_occurrences != passage.source_occurrences
            {
                return Err(MathematicalParticleError::AddressedOccurrenceKeyDisagrees);
            }
        }
        let used_events = input
            .passages
            .iter()
            .flat_map(|passage| {
                passage.staging.values().map(|step| step.event).chain(
                    passage
                        .branches
                        .values()
                        .flat_map(|word| word.steps.iter().map(|step| step.event)),
                )
            })
            .collect::<BTreeSet<_>>();
        if used_events != input.operation.shape.occurrences.keys().copied().collect() {
            return Err(MathematicalParticleError::LicensedOccurrencesNotTotal);
        }
        for branch in &input.branches {
            resolve_selection(&branch.passage, &input.passages)?;
            require_subset(
                &branch.hypotheses,
                &hypothesis_ids,
                MathematicalParticleError::UnknownHypothesis,
            )?;
        }
        validate_operation_typing(
            &input.operations,
            &input.operation,
            &hypothesis_ids,
            &branch_ids,
        )?;

        let mut evidence = source_addresses.clone();
        evidence.insert(input.occurrence.clone());
        evidence.extend(
            input
                .passages
                .iter()
                .map(|passage| passage.occurrence.clone()),
        );
        evidence.extend(
            input
                .passages
                .iter()
                .flat_map(|passage| passage.branches.values())
                .map(|word| word.occurrence.clone()),
        );
        evidence.extend(
            input
                .value_receivers
                .iter()
                .map(|returned| returned.occurrence.clone()),
        );
        evidence.extend(
            input
                .rendering_receivers
                .iter()
                .map(|returned| returned.occurrence.clone()),
        );
        evidence.extend(
            input
                .classification_receivers
                .iter()
                .map(|returned| returned.occurrence().to_owned()),
        );
        evidence.extend(
            input
                .similarity_receivers
                .iter()
                .map(|returned| returned.occurrence().to_owned()),
        );
        evidence.extend(
            input
                .receiver_history_returns
                .iter()
                .map(|returned| returned.occurrence().to_owned()),
        );
        evidence.extend(
            input
                .presentation_fibres
                .iter()
                .map(|fibre| fibre.occurrence.clone()),
        );
        evidence.extend(
            input
                .open_fibres
                .iter()
                .map(|fibre| fibre.occurrence.clone()),
        );
        for returned in input
            .linear_returns
            .iter()
            .map(|value| &value.passage)
            .chain(input.quantity_returns.iter().map(|value| &value.passage))
        {
            resolve_reference(returned, &input.passages)?;
        }
        for receiver in &input.value_receivers {
            if receiver.occurrence.is_empty()
                || receiver.values.is_empty()
                || !ports.contains(&receiver.port)
            {
                return Err(MathematicalParticleError::MalformedValueReceiver);
            }
            require_sources(&receiver.source_occurrences, &source_addresses)?;
        }
        for receiver in &input.rendering_receivers {
            if receiver.occurrence.is_empty()
                || !ports.contains(&receiver.port)
                || !artifacts.contains(&receiver.artifact_occurrence)
            {
                return Err(MathematicalParticleError::MalformedRenderingReceiver);
            }
            require_sources(&receiver.source_occurrences, &source_addresses)?;
        }
        let fibre_occurrences = input
            .presentation_fibres
            .iter()
            .map(|fibre| fibre.occurrence.clone())
            .chain(
                input
                    .open_fibres
                    .iter()
                    .map(|fibre| fibre.occurrence.clone()),
            )
            .collect::<BTreeSet<_>>();
        for relation in &input.sameness {
            relation.validate(
                &evidence,
                &carrier_ids,
                &source_addresses,
                &input.operation,
                &input.passages,
                &input.presentation_fibres,
                &input.open_fibres,
                &input.value_receivers,
                &input.classification_receivers,
                &input.similarity_receivers,
                &input.receiver_history_returns,
            )?;
        }
        let proposal_ids = input
            .proposals
            .iter()
            .map(|proposal| proposal.occurrence.as_str())
            .collect::<BTreeSet<_>>();
        if input
            .proposals
            .iter()
            .any(|proposal| proposal.occurrence.is_empty())
            || proposal_ids.len() != input.proposals.len()
        {
            return Err(MathematicalParticleError::EmptyProposal);
        }
        for proposal in &input.proposals {
            let inspection = inspect_selection(&proposal.passage, &input.passages);
            match &proposal.owner_attempt {
                ProposalOwnerAttempt::Licensed { licenses }
                    if !licenses.is_empty()
                        && inspection.as_ref().is_ok_and(|laws| {
                            licenses.keys().copied().collect::<BTreeSet<_>>() == *laws
                        })
                        && licenses.values().all(|identity| !identity.is_empty()) => {}
                ProposalOwnerAttempt::ExactOwnerRefused(_) if inspection.is_ok() => {}
                ProposalOwnerAttempt::TypingRefused(expected)
                    if inspection == Err(expected.clone()) => {}
                ProposalOwnerAttempt::Open { fibre_occurrence }
                    if fibre_occurrences.contains(fibre_occurrence) && inspection.is_ok() => {}
                _ => return Err(MathematicalParticleError::MalformedProposalAttempt),
            }
        }
        let Some(accepted_proposal) = input
            .proposals
            .iter()
            .find(|proposal| proposal.occurrence == input.admission.proposal)
        else {
            return Err(MathematicalParticleError::AdmissionNotCausallyLinked);
        };
        let accepted_laws = inspect_selection(&accepted_proposal.passage, &input.passages)?;
        let mut returned_branches = BTreeMap::<TypedPassageRef, usize>::new();
        for reference in input
            .linear_returns
            .iter()
            .map(|returned| &returned.passage)
            .chain(
                input
                    .quantity_returns
                    .iter()
                    .map(|returned| &returned.passage),
            )
        {
            *returned_branches.entry(reference.clone()).or_default() += 1;
        }
        let selected_references = accepted_proposal
            .passage
            .branches
            .iter()
            .map(|branch| TypedPassageRef {
                passage: accepted_proposal.passage.passage.clone(),
                branch: *branch,
            })
            .collect::<BTreeSet<_>>();
        if accepted_proposal.passage.passage != input.admission.typing_occurrence
            || returned_branches.keys().cloned().collect::<BTreeSet<_>>() != selected_references
            || returned_branches
                .values()
                .any(|population| *population != 1)
        {
            return Err(MathematicalParticleError::AdmissionNotCausallyLinked);
        }
        let bindings = input
            .admission
            .exact_owner
            .validate(&input.operation)
            .map_err(|error| MathematicalParticleError::Method(error.to_string()))?;
        validate_owner_typing(&bindings, &input.ports)?;
        let licensed = bindings
            .iter()
            .flat_map(|binding| &binding.exact_owner_licenses)
            .map(|license| {
                (
                    license.constraint().law(),
                    license.evidence_sha256().to_owned(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let passage_receipt = input
            .admission
            .passage_receipt
            .as_ref()
            .ok_or(MathematicalParticleError::MissingResidentPassageReceipt)?;
        let accepted_passage = passage(&accepted_proposal.passage.passage, &input.passages)?;
        let selected_occurrences = accepted_proposal
            .passage
            .branches
            .iter()
            .flat_map(|branch| {
                std::iter::once((
                    accepted_passage.staging[branch].event,
                    accepted_passage.staging[branch].law,
                ))
                .chain(
                    accepted_passage.branches[branch]
                        .steps
                        .iter()
                        .map(|step| (step.event, step.law)),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let selected_events = selected_occurrences
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        if passage_receipt.licensed_laws() != &licensed
            || passage_receipt.entailed_occurrences() != &selected_occurrences
            || !passage_receipt.matches_complex_and_selection(&input.operation, &selected_events)
        {
            return Err(MathematicalParticleError::AdmissionNotCausallyLinked);
        }
        for branch in &accepted_proposal.passage.branches {
            let terminal = accepted_passage.branches[branch]
                .steps
                .last()
                .expect("selected branch words are nonempty")
                .event;
            let returned = passage_receipt
                .readbacks()
                .get(&terminal)
                .ok_or(MathematicalParticleError::AdmissionNotCausallyLinked)?;
            if returned.iter().any(|word| *word != (0, 0)) {
                return Err(MathematicalParticleError::AdmissionNotCausallyLinked);
            }
        }
        let returned_licenses = input
            .linear_returns
            .iter()
            .flat_map(|returned| {
                returned
                    .steps
                    .iter()
                    .map(|step| (step.law, step.owner_evidence_sha256.clone()))
            })
            .chain(input.quantity_returns.iter().flat_map(|returned| {
                returned
                    .owner_evidence_sha256
                    .iter()
                    .map(|(law, evidence)| (*law, evidence.clone()))
            }))
            .collect::<BTreeMap<_, _>>();
        if !matches!(
            &accepted_proposal.owner_attempt,
            ProposalOwnerAttempt::Licensed { licenses }
                if licenses == &licensed
                    && returned_licenses == licensed
                    && licenses.keys().copied().collect::<BTreeSet<_>>() == accepted_laws
        ) {
            return Err(MathematicalParticleError::AdmissionNotCausallyLinked);
        }
        for refusal in &input.refusals {
            let Some(proposal) = input
                .proposals
                .iter()
                .find(|proposal| proposal.occurrence == refusal.proposal)
            else {
                return Err(MathematicalParticleError::MalformedRefusal(
                    refusal.proposal.clone(),
                ));
            };
            match (&proposal.owner_attempt, &refusal.obstruction) {
                (
                    ProposalOwnerAttempt::ExactOwnerRefused(expected),
                    ProposalRefusal::ExactOwner(returned),
                ) if expected == returned => {}
                (
                    ProposalOwnerAttempt::TypingRefused(expected),
                    ProposalRefusal::Typing(returned),
                ) if expected == returned
                    && inspect_selection(&proposal.passage, &input.passages)
                        == Err(returned.clone()) => {}
                _ => {
                    return Err(MathematicalParticleError::MalformedRefusal(
                        refusal.proposal.clone(),
                    ));
                }
            }
        }
        for fiber in &input.open_fibres {
            let addressed_by_open_proposal = input.proposals.iter().any(|proposal| {
                matches!(
                    &proposal.owner_attempt,
                    ProposalOwnerAttempt::Open { fibre_occurrence }
                        if fibre_occurrence == &fiber.occurrence
                )
            });
            if fiber.occurrence.is_empty()
                || fiber.question.is_empty()
                || fiber.candidates.len() < 2
                || fiber.would_be_decided_by.is_empty()
                || !addressed_by_open_proposal
            {
                return Err(MathematicalParticleError::MalformedOpenFiber(
                    fiber.question.clone(),
                ));
            }
        }
        Ok(Self {
            occurrence: input.occurrence,
            source_testimonies: input.source_testimonies,
            exterior_artifacts: input.exterior_artifacts,
            presentation_fibres: input.presentation_fibres,
            operation: input.operation,
            carriers: input.carriers,
            binders: input.binders,
            ports: input.ports,
            operations: input.operations,
            hypotheses: input.hypotheses,
            passages: input.passages,
            branches: input.branches,
            linear_returns: input.linear_returns,
            quantity_returns: input.quantity_returns,
            value_receivers: input.value_receivers,
            rendering_receivers: input.rendering_receivers,
            classification_receivers: input.classification_receivers,
            similarity_receivers: input.similarity_receivers,
            receiver_history_returns: input.receiver_history_returns,
            sameness: input.sameness,
            proposals: input.proposals,
            refusals: input.refusals,
            open_fibres: input.open_fibres,
            admission: ParticleAdmission {
                proposal: input.admission.proposal,
                typing_occurrence: input.admission.typing_occurrence,
                exact_owner: input.admission.exact_owner,
                passage_receipt: input
                    .admission
                    .passage_receipt
                    .expect("the receipt was required above"),
                bindings,
            },
        })
    }
}

impl ParticleProposal {
    pub fn from_typing_result(
        occurrence: impl Into<String>,
        passage: PassageSelection,
        passages: &[TypedPassage],
    ) -> Result<(Self, ParticleRefusal), MathematicalParticleError> {
        let occurrence = occurrence.into();
        let refusal = inspect_selection(&passage, passages)
            .err()
            .ok_or(MathematicalParticleError::TypingProposalDidNotRefuse)?;
        let proposal = Self {
            occurrence: occurrence.clone(),
            passage,
            owner_attempt: ProposalOwnerAttempt::TypingRefused(refusal.clone()),
        };
        let returned = ParticleRefusal {
            proposal: occurrence,
            obstruction: ProposalRefusal::Typing(refusal),
        };
        Ok((proposal, returned))
    }
}
