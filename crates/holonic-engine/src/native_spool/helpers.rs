use super::refusal::NativeSpoolRefusal;
use super::*;
pub(crate) fn validate_pullback(
    pullback: &NativeSerialPullback,
    threads: &BTreeMap<&str, &NativeThread>,
) -> Result<(), NativeSpoolRefusal> {
    let Some(left) = threads.get(pullback.left_thread.as_str()) else {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    };
    let Some(right) = threads.get(pullback.right_thread.as_str()) else {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    };
    if left.emitting_boundary != pullback.joining_boundary
        || right.entering_boundary != pullback.joining_boundary
    {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    }
    let expected =
        left.occurrences
            .iter()
            .flat_map(|left_occurrence| {
                right
                    .occurrences
                    .iter()
                    .filter_map(move |right_occurrence| {
                        (left_occurrence.emitting_native == right_occurrence.entering_native)
                            .then_some(NativePullbackOccurrence {
                                left: left_occurrence.occurrence,
                                right: right_occurrence.occurrence,
                                joining_native: left_occurrence.emitting_native,
                            })
                    })
            })
            .collect::<BTreeSet<_>>();
    if expected.is_empty() || expected != pullback.occurrences {
        return Err(NativeSpoolRefusal::Pullback(
            pullback.left_thread.clone(),
            pullback.right_thread.clone(),
        ));
    }
    Ok(())
}

pub(crate) fn validate_interchange(
    receipt: &NativeInterchangeReceipt,
    threads: &BTreeMap<&str, &NativeThread>,
) -> Result<(), NativeSpoolRefusal> {
    if receipt.left_then_right.order
        != vec![receipt.left_thread.clone(), receipt.right_thread.clone()]
        || receipt.right_then_left.order
            != vec![receipt.right_thread.clone(), receipt.left_thread.clone()]
    {
        return Err(NativeSpoolRefusal::Interchange(receipt.left_thread.clone()));
    }
    let expected_lineage = threads[receipt.left_thread.as_str()]
        .occurrences
        .iter()
        .chain(threads[receipt.right_thread.as_str()].occurrences.iter())
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    if receipt.left_then_right.successor != receipt.right_then_left.successor
        || receipt.left_then_right.obstructions != receipt.right_then_left.obstructions
        || receipt.left_then_right.lineage_occurrences != expected_lineage
        || receipt.right_then_left.lineage_occurrences != expected_lineage
        || receipt.left_then_right.logical_resources != receipt.right_then_left.logical_resources
    {
        return Err(NativeSpoolRefusal::Interchange(receipt.left_thread.clone()));
    }
    Ok(())
}

pub(crate) fn connected(graph: &BTreeMap<&str, BTreeSet<&str>>) -> bool {
    let Some(start) = graph.keys().next().copied() else {
        return false;
    };
    let mut reached = BTreeSet::from([start]);
    let mut queue = VecDeque::from([start]);
    while let Some(at) = queue.pop_front() {
        for next in &graph[at] {
            if reached.insert(*next) {
                queue.push_back(*next);
            }
        }
    }
    reached.len() == graph.len()
}

pub(crate) fn is_sha256_identity(identity: &str) -> bool {
    identity.len() == 64
        && identity
            .bytes()
            .all(|octet| octet.is_ascii_digit() || (b'a'..=b'f').contains(&octet))
}

pub(crate) fn positions_are_unique(positions: &[usize]) -> bool {
    positions.iter().copied().collect::<BTreeSet<_>>().len() == positions.len()
}

pub(crate) fn sha256_bytes(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

pub(crate) fn native_deposit_identity(
    deposit: &NativeThreadDeposit,
) -> Result<String, NativeSpoolRefusal> {
    deposit.validate()?;
    let bytes =
        serde_json::to_vec(deposit).map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

pub(crate) fn native_deposit_batch_identity(
    deposits: &[NativeThreadDeposit],
) -> Result<String, NativeSpoolRefusal> {
    if deposits.is_empty() {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    for deposit in deposits {
        deposit.validate()?;
    }
    let bytes = serde_json::to_vec(deposits)
        .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

pub(crate) fn symmetric_constitutive_body(
    deposits: &[NativeThreadDeposit],
) -> Result<NativeSymmetricConstitutiveBody, NativeSpoolRefusal> {
    let thread_population = deposits
        .iter()
        .map(|deposit| deposit.thread.address.clone())
        .collect::<BTreeSet<_>>();
    if thread_population.len() != deposits.len() {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    let mut families = deposits
        .iter()
        .flat_map(|deposit| &deposit.mixed_constitutive_families);
    let first = families
        .next()
        .ok_or(NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
    let receiver = first.receiver;
    let dependent_receiver_support = first.dependent_receiver_support.clone();
    let mut terms = Vec::new();
    for deposit in deposits {
        for family in &deposit.mixed_constitutive_families {
            if family.receiver != receiver
                || family.dependent_receiver_support != dependent_receiver_support
                || !thread_population.contains(&family.left_thread)
                || !thread_population.contains(&family.right_thread)
                || (family.left_thread != deposit.thread.address
                    && family.right_thread != deposit.thread.address)
            {
                return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
            }
            let (left_thread, right_thread) = if family.left_thread <= family.right_thread {
                (family.left_thread.clone(), family.right_thread.clone())
            } else {
                (family.right_thread.clone(), family.left_thread.clone())
            };
            terms.push(NativeSymmetricConstitutiveTerm {
                left_thread,
                right_thread,
                family_address: family.address.clone(),
            });
        }
    }
    terms.sort();
    let rank = u64::try_from(thread_population.len())
        .map_err(|_| NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
    let distinct_pair_population = rank
        .checked_mul(rank.saturating_sub(1))
        .and_then(|population| population.checked_div(2))
        .ok_or(NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
    let symmetric_population = rank
        .checked_mul(rank.saturating_add(1))
        .and_then(|population| population.checked_div(2))
        .ok_or(NativeSpoolRefusal::ThreadDepositBatchReceipt)?;
    let body = NativeSymmetricConstitutiveBody {
        thread_population,
        receiver,
        dependent_receiver_support,
        terms,
        diagonal_population: rank,
        distinct_pair_population,
        symmetric_population,
    };
    body.validate()?;
    Ok(body)
}

pub(crate) fn native_situated_identity_parts(
    native: &NativeTransportScaffold,
    mixed: &[NativeMixedConstitutiveFamily],
    exact_fibres: &[NativeExactReconstructionFibre],
) -> Result<String, NativeSpoolRefusal> {
    #[derive(Serialize)]
    struct SituatedRef<'a> {
        schema: &'a str,
        native: &'a NativeTransportScaffold,
        mixed_constitutive_families: &'a [NativeMixedConstitutiveFamily],
        exact_reconstruction_fibres: &'a [NativeExactReconstructionFibre],
    }
    validate_situated_relations(native, mixed, exact_fibres)?;
    let bytes = serde_json::to_vec(&SituatedRef {
        schema: SITUATED_NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
        native,
        mixed_constitutive_families: mixed,
        exact_reconstruction_fibres: exact_fibres,
    })
    .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

pub(crate) fn validate_situated_relations(
    native: &NativeTransportScaffold,
    mixed: &[NativeMixedConstitutiveFamily],
    fibres: &[NativeExactReconstructionFibre],
) -> Result<(), NativeSpoolRefusal> {
    let mut threads = BTreeMap::<&str, (&NativeSpool, &NativeThread)>::new();
    let mut occurrence_owner = BTreeMap::<EventId, (&NativeSpool, &NativeThread)>::new();
    for spool in &native.spools {
        for thread in &spool.threads {
            threads.insert(thread.address.as_str(), (spool, thread));
            for occurrence in &thread.occurrences {
                occurrence_owner.insert(occurrence.occurrence, (spool, thread));
            }
        }
    }
    let mut mixed_addresses = BTreeSet::new();
    for family in mixed {
        family.validate()?;
        let Some((left_spool, _)) = threads.get(family.left_thread.as_str()) else {
            return Err(NativeSpoolRefusal::MixedConstitutiveFamily(
                family.address.clone(),
            ));
        };
        let Some((right_spool, _)) = threads.get(family.right_thread.as_str()) else {
            return Err(NativeSpoolRefusal::MixedConstitutiveFamily(
                family.address.clone(),
            ));
        };
        if !mixed_addresses.insert(family.address.as_str())
            || left_spool.address != right_spool.address
            || !left_spool.receiver_family.contains(&family.receiver)
        {
            return Err(NativeSpoolRefusal::MixedConstitutiveFamily(
                family.address.clone(),
            ));
        }
    }
    let mut fibre_addresses = BTreeSet::new();
    for fibre in fibres {
        fibre.validate()?;
        let Some((spool, thread)) = threads.get(fibre.thread.as_str()) else {
            return Err(NativeSpoolRefusal::ExactReconstructionFibre(
                fibre.address.clone(),
            ));
        };
        if !fibre_addresses.insert(fibre.address.as_str())
            || !fibre.k3_native_support.is_subset(&spool.native_population)
            || !thread.occurrences.iter().any(|occurrence| {
                occurrence.occurrence == fibre.carrying_pullback.right
                    && occurrence.predecessor == Some(fibre.carrying_pullback.left)
                    && occurrence.entering_native == fibre.carrying_pullback.joining_native
            })
            || fibre
                .occurrences
                .iter()
                .filter(|occurrence| **occurrence != fibre.carrying_pullback.left)
                .any(|occurrence| !occurrence_owner.contains_key(occurrence))
        {
            return Err(NativeSpoolRefusal::ExactReconstructionFibre(
                fibre.address.clone(),
            ));
        }
    }
    Ok(())
}

pub(crate) fn validate_thread_deposit_against(
    native: &NativeTransportScaffold,
    existing_mixed: &[NativeMixedConstitutiveFamily],
    existing_fibres: &[NativeExactReconstructionFibre],
    deposit: &NativeThreadDeposit,
) -> Result<(), NativeSpoolRefusal> {
    deposit.validate()?;
    let spool = native
        .spools
        .iter()
        .find(|spool| spool.address == deposit.spool_address)
        .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(deposit.spool_address.clone()))?;
    if native
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .any(|thread| thread.address == deposit.thread.address)
    {
        return Err(NativeSpoolRefusal::DuplicateThread(
            deposit.thread.address.clone(),
        ));
    }
    let deposited_events = deposit
        .thread
        .occurrences
        .iter()
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    if native
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .any(|occurrence| deposited_events.contains(&occurrence.occurrence))
    {
        return Err(NativeSpoolRefusal::ThreadDeposit(
            "a deposited occurrence is already owned by the continuing ecology".to_owned(),
        ));
    }
    let mut threads = spool
        .threads
        .iter()
        .map(|thread| (thread.address.as_str(), thread))
        .collect::<BTreeMap<_, _>>();
    threads.insert(deposit.thread.address.as_str(), &deposit.thread);

    let existing_pullbacks = spool
        .serial_pullbacks
        .iter()
        .map(|pullback| {
            (
                pullback.left_thread.as_str(),
                pullback.right_thread.as_str(),
            )
        })
        .collect::<BTreeSet<_>>();
    let mut deposited_pullbacks = BTreeSet::new();
    for pullback in &deposit.serial_pullbacks {
        let pair = (
            pullback.left_thread.as_str(),
            pullback.right_thread.as_str(),
        );
        if !deposited_pullbacks.insert(pair)
            || existing_pullbacks.contains(&pair)
            || (pair.0 != deposit.thread.address && pair.1 != deposit.thread.address)
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "a serial pullback is repeated or not incident to the deposited thread".to_owned(),
            ));
        }
        validate_pullback(pullback, &threads)?;
    }

    let mut generators = BTreeSet::new();
    for descent in &deposit.generator_descents {
        if spool.generator_family.contains(&descent.generator)
            || !generators.insert(descent.generator)
            || !descent
                .steps
                .iter()
                .any(|step| step.thread == deposit.thread.address)
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "a deposited generator is repeated or does not cross the deposited thread"
                    .to_owned(),
            ));
        }
    }
    let final_generators = spool
        .generator_family
        .iter()
        .copied()
        .chain(generators.iter().copied())
        .collect::<BTreeSet<_>>();
    if deposit
        .thread
        .chronology
        .iter()
        .any(|generator| !final_generators.contains(generator))
    {
        return Err(NativeSpoolRefusal::ThreadDeposit(
            "the deposited thread uses a generator absent from the resulting spool".to_owned(),
        ));
    }

    let factor_keys = spool
        .receiver_factors
        .iter()
        .map(|factor| (factor.native, factor.receiver))
        .collect::<BTreeSet<_>>();
    let mut new_factor_keys = BTreeSet::new();
    for factor in &deposit.receiver_factors {
        if !spool.receiver_family.contains(&factor.receiver)
            || !deposit.thread.native_support.contains(&factor.native)
            || factor_keys.contains(&(factor.native, factor.receiver))
            || !new_factor_keys.insert((factor.native, factor.receiver))
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "a receiver factor is repeated, outside the existing receiver family, or not carried by the deposited thread"
                    .to_owned(),
            ));
        }
    }

    let mut mutual_pairs = spool
        .mutual_constitutive_responses
        .iter()
        .map(|response| (response.left_occurrence, response.right_occurrence))
        .collect::<BTreeSet<_>>();
    for response in &deposit.mutual_constitutive_responses {
        if (!deposited_events.contains(&response.left_occurrence)
            && !deposited_events.contains(&response.right_occurrence))
            || !mutual_pairs.insert((response.left_occurrence, response.right_occurrence))
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "a mutual constitutive term is repeated or not incident".to_owned(),
            ));
        }
    }
    for separator in &deposit.shortest_separators {
        if !deposited_events.contains(&separator.left)
            && !deposited_events.contains(&separator.right)
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "a shortest separator is not incident".to_owned(),
            ));
        }
    }
    for interchange in &deposit.interchanges {
        if interchange.left_thread != deposit.thread.address
            && interchange.right_thread != deposit.thread.address
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "an interchange is not incident".to_owned(),
            ));
        }
        validate_interchange(interchange, &threads)?;
    }

    let existing_mixed_addresses = existing_mixed
        .iter()
        .map(|family| family.address.as_str())
        .collect::<BTreeSet<_>>();
    let mut mixed_addresses = BTreeSet::new();
    for family in &deposit.mixed_constitutive_families {
        if existing_mixed_addresses.contains(family.address.as_str())
            || !mixed_addresses.insert(family.address.as_str())
            || (family.left_thread != deposit.thread.address
                && family.right_thread != deposit.thread.address)
        {
            return Err(NativeSpoolRefusal::MixedConstitutiveFamily(
                family.address.clone(),
            ));
        }
    }
    let existing_fibre_addresses = existing_fibres
        .iter()
        .map(|fibre| fibre.address.as_str())
        .collect::<BTreeSet<_>>();
    let mut fibre_addresses = BTreeSet::new();
    for fibre in &deposit.exact_reconstruction_fibres {
        if existing_fibre_addresses.contains(fibre.address.as_str())
            || !fibre_addresses.insert(fibre.address.as_str())
            || fibre.thread != deposit.thread.address
            || !fibre
                .occurrences
                .iter()
                .any(|occurrence| deposited_events.contains(occurrence))
        {
            return Err(NativeSpoolRefusal::ExactReconstructionFibre(
                fibre.address.clone(),
            ));
        }
    }
    Ok(())
}

pub(crate) fn stage_thread_deposit(
    mut native: NativeTransportScaffold,
    mut mixed: Vec<NativeMixedConstitutiveFamily>,
    mut exact_fibres: Vec<NativeExactReconstructionFibre>,
    deposit: NativeThreadDeposit,
    predecessor_kind: SituatedNativeTransportPredecessorKind,
    admitted_predecessor_identity_sha256: Option<&str>,
) -> Result<(SituatedNativeTransportScaffold, NativeThreadDepositReceipt), NativeSpoolRefusal> {
    if admitted_predecessor_identity_sha256.is_none() {
        native.validate()?;
        validate_situated_relations(&native, &mixed, &exact_fibres)?;
    }
    validate_thread_deposit_against(&native, &mixed, &exact_fibres, &deposit)?;
    let predecessor_identity_sha256 = if let Some(identity) = admitted_predecessor_identity_sha256 {
        if predecessor_kind != SituatedNativeTransportPredecessorKind::SituatedScaffold {
            return Err(NativeSpoolRefusal::ThreadDepositReceipt);
        }
        identity.to_owned()
    } else {
        match predecessor_kind {
            SituatedNativeTransportPredecessorKind::NativeScaffold => {
                if !mixed.is_empty() || !exact_fibres.is_empty() {
                    return Err(NativeSpoolRefusal::ThreadDepositReceipt);
                }
                native_scaffold_identity(&native)?
            }
            SituatedNativeTransportPredecessorKind::SituatedScaffold => {
                native_situated_identity_parts(&native, &mixed, &exact_fibres)?
            }
        }
    };

    let deposit_identity_sha256 = native_deposit_identity(&deposit)?;
    let NativeThreadDeposit {
        schema: _,
        spool_address,
        thread,
        serial_pullbacks,
        generator_descents,
        receiver_factors,
        mutual_constitutive_responses,
        mixed_constitutive_families,
        shortest_separators,
        interchanges,
        reconstruction_fibre_deltas,
        exact_reconstruction_fibres,
    } = deposit;
    let thread_address = thread.address.clone();
    let spool = native
        .spools
        .iter_mut()
        .find(|spool| spool.address == spool_address)
        .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.clone()))?;
    let thread_position = spool.threads.len();
    let serial_pullback_positions =
        appended_positions(spool.serial_pullbacks.len(), serial_pullbacks.len());
    let generator_descent_positions =
        appended_positions(spool.generator_descents.len(), generator_descents.len());
    let receiver_factor_positions =
        appended_positions(spool.receiver_factors.len(), receiver_factors.len());
    let mutual_constitutive_positions = appended_positions(
        spool.mutual_constitutive_responses.len(),
        mutual_constitutive_responses.len(),
    );
    let shortest_separator_positions =
        appended_positions(spool.shortest_separators.len(), shortest_separators.len());
    let interchange_positions = appended_positions(spool.interchanges.len(), interchanges.len());
    let mixed_constitutive_positions =
        appended_positions(mixed.len(), mixed_constitutive_families.len());
    let exact_reconstruction_positions =
        appended_positions(exact_fibres.len(), exact_reconstruction_fibres.len());

    for descent in &generator_descents {
        spool.generator_family.insert(descent.generator);
    }
    spool
        .native_population
        .extend(thread.native_support.iter().copied());
    spool.threads.push(thread);
    spool.serial_pullbacks.extend(serial_pullbacks);
    spool.generator_descents.extend(generator_descents);
    spool.receiver_factors.extend(receiver_factors);
    spool
        .mutual_constitutive_responses
        .extend(mutual_constitutive_responses);
    spool.shortest_separators.extend(shortest_separators);
    spool.interchanges.extend(interchanges);
    let mut fibre_receipts = Vec::with_capacity(reconstruction_fibre_deltas.len());
    for delta in reconstruction_fibre_deltas {
        if let Some((position, fibre)) = spool
            .reconstruction_fibres
            .iter_mut()
            .enumerate()
            .find(|(_, fibre)| fibre.native == delta.native)
        {
            fibre.occurrences.extend(delta.occurrences.iter().copied());
            fibre_receipts.push(NativeDepositFibreReceipt {
                position,
                native: delta.native,
                occurrences: delta.occurrences,
                fibre_was_founded: false,
            });
        } else {
            let position = spool.reconstruction_fibres.len();
            spool.reconstruction_fibres.push(NativeCollapsedFibre {
                native: delta.native,
                occurrences: delta.occurrences.clone(),
            });
            fibre_receipts.push(NativeDepositFibreReceipt {
                position,
                native: delta.native,
                occurrences: delta.occurrences,
                fibre_was_founded: true,
            });
        }
    }
    mixed.extend(mixed_constitutive_families);
    exact_fibres.extend(exact_reconstruction_fibres);
    let situated = SituatedNativeTransportScaffold {
        schema: SITUATED_NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        native,
        mixed_constitutive_families: mixed,
        exact_reconstruction_fibres: exact_fibres,
    };
    situated.validate()?;
    // `situated` has just passed complete validation. Hash its exact wire directly rather than
    // asking `canonical_bytes` to replay the same validation a second time.
    let successor_identity_sha256 = sha256_bytes(
        &serde_json::to_vec(&situated)
            .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?,
    );
    let receipt = NativeThreadDepositReceipt {
        schema: NATIVE_THREAD_DEPOSIT_RECEIPT_SCHEMA.to_owned(),
        predecessor_identity_sha256,
        successor_identity_sha256,
        deposit_identity_sha256,
        spool_address,
        thread_address,
        thread_position,
        serial_pullback_positions,
        generator_descent_positions,
        receiver_factor_positions,
        mutual_constitutive_positions,
        mixed_constitutive_positions,
        shortest_separator_positions,
        interchange_positions,
        fibre_receipts,
        exact_reconstruction_positions,
        predecessor_kind,
    };
    receipt.validate()?;
    Ok((situated, receipt))
}

pub(crate) fn stage_native_deposit_batch(
    mut native: NativeTransportScaffold,
    mut deposits: Vec<NativeThreadDeposit>,
) -> Result<
    (
        SituatedNativeTransportScaffold,
        NativeThreadDepositBatchReceipt,
    ),
    NativeSpoolRefusal,
> {
    native.validate()?;
    if deposits.is_empty() {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    // Canonical address order is solely a presentation of one simultaneous population.  No
    // predecessor prefix or intermediate identity is founded by this ordering.
    deposits.sort_by(|left, right| left.thread.address.cmp(&right.thread.address));
    for deposit in &deposits {
        deposit.validate()?;
    }
    let spool_address = deposits[0].spool_address.clone();
    if deposits
        .iter()
        .any(|deposit| deposit.spool_address != spool_address)
    {
        return Err(NativeSpoolRefusal::ThreadDeposit(
            "one atomic batch must enter one existing spool".to_owned(),
        ));
    }
    let predecessor_identity_sha256 = native_scaffold_identity(&native)?;
    let batch_identity_sha256 = native_deposit_batch_identity(&deposits)?;
    let symmetric_constitutive_body = symmetric_constitutive_body(&deposits)?;

    let predecessor_threads = native
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .map(|thread| thread.address.as_str())
        .collect::<BTreeSet<_>>();
    let predecessor_occurrences = native
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    let mut batch_threads = BTreeSet::new();
    let mut batch_occurrences = BTreeSet::new();
    let mut batch_generators = BTreeSet::new();
    let predecessor_spool = native
        .spools
        .iter()
        .find(|spool| spool.address == spool_address)
        .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.clone()))?;
    for deposit in &deposits {
        if predecessor_threads.contains(deposit.thread.address.as_str())
            || !batch_threads.insert(deposit.thread.address.as_str())
            || deposit.thread.occurrences.iter().any(|occurrence| {
                predecessor_occurrences.contains(&occurrence.occurrence)
                    || !batch_occurrences.insert(occurrence.occurrence)
            })
            || deposit.exact_reconstruction_fibres.iter().any(|fibre| {
                fibre.thread != deposit.thread.address
                    || !fibre.occurrences.iter().any(|occurrence| {
                        deposit
                            .thread
                            .occurrences
                            .iter()
                            .any(|thread_occurrence| thread_occurrence.occurrence == *occurrence)
                    })
            })
            || deposit.generator_descents.iter().any(|descent| {
                predecessor_spool
                    .generator_family
                    .contains(&descent.generator)
                    || !batch_generators.insert(descent.generator)
            })
        {
            return Err(NativeSpoolRefusal::ThreadDeposit(
                "the atomic batch repeats a thread, occurrence, generator, or fibre owner"
                    .to_owned(),
            ));
        }
    }
    let final_generators = predecessor_spool
        .generator_family
        .iter()
        .copied()
        .chain(batch_generators.iter().copied())
        .collect::<BTreeSet<_>>();
    if deposits.iter().any(|deposit| {
        deposit
            .thread
            .chronology
            .iter()
            .any(|generator| !final_generators.contains(generator))
    }) {
        return Err(NativeSpoolRefusal::ThreadDeposit(
            "a batch thread uses a generator absent from the complete successor".to_owned(),
        ));
    }

    let spool = native
        .spools
        .iter_mut()
        .find(|spool| spool.address == spool_address)
        .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.clone()))?;
    let mut mixed = Vec::new();
    let mut exact_fibres = Vec::new();
    let mut placements = Vec::with_capacity(deposits.len());
    for deposit in deposits {
        let NativeThreadDeposit {
            schema: _,
            spool_address: deposit_spool,
            thread,
            serial_pullbacks,
            generator_descents,
            receiver_factors,
            mutual_constitutive_responses,
            mixed_constitutive_families,
            shortest_separators,
            interchanges,
            reconstruction_fibre_deltas,
            exact_reconstruction_fibres,
        } = deposit;
        let thread_address = thread.address.clone();
        let placement = NativeThreadDepositPlacement {
            spool_address: deposit_spool,
            thread_address,
            thread_position: spool.threads.len(),
            serial_pullback_positions: appended_positions(
                spool.serial_pullbacks.len(),
                serial_pullbacks.len(),
            ),
            generator_descent_positions: appended_positions(
                spool.generator_descents.len(),
                generator_descents.len(),
            ),
            receiver_factor_positions: appended_positions(
                spool.receiver_factors.len(),
                receiver_factors.len(),
            ),
            mutual_constitutive_positions: appended_positions(
                spool.mutual_constitutive_responses.len(),
                mutual_constitutive_responses.len(),
            ),
            mixed_constitutive_positions: appended_positions(
                mixed.len(),
                mixed_constitutive_families.len(),
            ),
            shortest_separator_positions: appended_positions(
                spool.shortest_separators.len(),
                shortest_separators.len(),
            ),
            interchange_positions: appended_positions(spool.interchanges.len(), interchanges.len()),
            fibre_receipts: Vec::new(),
            exact_reconstruction_positions: appended_positions(
                exact_fibres.len(),
                exact_reconstruction_fibres.len(),
            ),
        };
        for descent in &generator_descents {
            spool.generator_family.insert(descent.generator);
        }
        spool
            .native_population
            .extend(thread.native_support.iter().copied());
        spool.threads.push(thread);
        spool.serial_pullbacks.extend(serial_pullbacks);
        spool.generator_descents.extend(generator_descents);
        spool.receiver_factors.extend(receiver_factors);
        spool
            .mutual_constitutive_responses
            .extend(mutual_constitutive_responses);
        spool.shortest_separators.extend(shortest_separators);
        spool.interchanges.extend(interchanges);
        let mut placement = placement;
        for delta in reconstruction_fibre_deltas {
            if let Some((position, fibre)) = spool
                .reconstruction_fibres
                .iter_mut()
                .enumerate()
                .find(|(_, fibre)| fibre.native == delta.native)
            {
                fibre.occurrences.extend(delta.occurrences.iter().copied());
                placement.fibre_receipts.push(NativeDepositFibreReceipt {
                    position,
                    native: delta.native,
                    occurrences: delta.occurrences,
                    fibre_was_founded: false,
                });
            } else {
                let position = spool.reconstruction_fibres.len();
                spool.reconstruction_fibres.push(NativeCollapsedFibre {
                    native: delta.native,
                    occurrences: delta.occurrences.clone(),
                });
                placement.fibre_receipts.push(NativeDepositFibreReceipt {
                    position,
                    native: delta.native,
                    occurrences: delta.occurrences,
                    fibre_was_founded: true,
                });
            }
        }
        mixed.extend(mixed_constitutive_families);
        exact_fibres.extend(exact_reconstruction_fibres);
        placement.validate()?;
        placements.push(placement);
    }
    let situated = SituatedNativeTransportScaffold {
        schema: SITUATED_NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        native,
        mixed_constitutive_families: mixed,
        exact_reconstruction_fibres: exact_fibres,
    };
    // This is the sole successor-wide validation and serialization boundary.
    let successor_identity_sha256 = situated.identity_sha256()?;
    let receipt = NativeThreadDepositBatchReceipt {
        schema: NATIVE_THREAD_DEPOSIT_BATCH_RECEIPT_SCHEMA.to_owned(),
        predecessor_identity_sha256,
        successor_identity_sha256,
        batch_identity_sha256,
        placements,
        symmetric_constitutive_body,
    };
    receipt.validate()?;
    Ok((situated, receipt))
}

pub(crate) fn withdraw_native_deposit_batch(
    mut situated: SituatedNativeTransportScaffold,
    receipt: NativeThreadDepositBatchReceipt,
) -> Result<(NativeTransportScaffold, Vec<NativeThreadDeposit>), NativeSpoolRefusal> {
    receipt.validate()?;
    if situated.identity_sha256()? != receipt.successor_identity_sha256 {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    let mut recovered = Vec::with_capacity(receipt.placements.len());
    for placement in receipt.placements.iter().rev() {
        let spool = situated
            .native
            .spools
            .iter_mut()
            .find(|spool| spool.address == placement.spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(placement.spool_address.clone()))?;
        if spool
            .threads
            .get(placement.thread_position)
            .is_none_or(|thread| thread.address != placement.thread_address)
        {
            return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
        }
        let thread = spool.threads.remove(placement.thread_position);
        let serial_pullbacks = take_indexed_positions(
            &mut spool.serial_pullbacks,
            &placement.serial_pullback_positions,
        )?;
        let generator_descents = take_indexed_positions(
            &mut spool.generator_descents,
            &placement.generator_descent_positions,
        )?;
        let receiver_factors = take_indexed_positions(
            &mut spool.receiver_factors,
            &placement.receiver_factor_positions,
        )?;
        let mutual_constitutive_responses = take_indexed_positions(
            &mut spool.mutual_constitutive_responses,
            &placement.mutual_constitutive_positions,
        )?;
        let shortest_separators = take_indexed_positions(
            &mut spool.shortest_separators,
            &placement.shortest_separator_positions,
        )?;
        let interchanges =
            take_indexed_positions(&mut spool.interchanges, &placement.interchange_positions)?;
        let mixed_constitutive_families = take_indexed_positions(
            &mut situated.mixed_constitutive_families,
            &placement.mixed_constitutive_positions,
        )?;
        let exact_reconstruction_fibres = take_indexed_positions(
            &mut situated.exact_reconstruction_fibres,
            &placement.exact_reconstruction_positions,
        )?;
        for fibre_receipt in placement.fibre_receipts.iter().rev() {
            let Some(fibre) = spool.reconstruction_fibres.get_mut(fibre_receipt.position) else {
                return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
            };
            if fibre.native != fibre_receipt.native
                || !fibre_receipt.occurrences.is_subset(&fibre.occurrences)
            {
                return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
            }
            fibre.occurrences = fibre
                .occurrences
                .difference(&fibre_receipt.occurrences)
                .copied()
                .collect();
            if fibre_receipt.fibre_was_founded {
                if !fibre.occurrences.is_empty() {
                    return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
                }
                spool.reconstruction_fibres.remove(fibre_receipt.position);
            } else if fibre.occurrences.is_empty() {
                return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
            }
        }
        recovered.push(NativeThreadDeposit {
            schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
            spool_address: placement.spool_address.clone(),
            thread,
            serial_pullbacks: serial_pullbacks,
            generator_descents,
            receiver_factors,
            mutual_constitutive_responses,
            mixed_constitutive_families,
            shortest_separators,
            interchanges,
            reconstruction_fibre_deltas: placement
                .fibre_receipts
                .iter()
                .map(|fibre| NativeDepositFibreDelta {
                    native: fibre.native,
                    occurrences: fibre.occurrences.clone(),
                })
                .collect(),
            exact_reconstruction_fibres,
        });
    }
    recovered.reverse();
    if !situated.mixed_constitutive_families.is_empty()
        || !situated.exact_reconstruction_fibres.is_empty()
    {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    for spool in &mut situated.native.spools {
        spool.native_population = spool
            .threads
            .iter()
            .flat_map(|thread| thread.native_support.iter().copied())
            .collect();
        spool.generator_family = spool
            .generator_descents
            .iter()
            .map(|descent| descent.generator)
            .collect();
    }
    if native_scaffold_identity(&situated.native)? != receipt.predecessor_identity_sha256
        || native_deposit_batch_identity(&recovered)? != receipt.batch_identity_sha256
        || symmetric_constitutive_body(&recovered)? != receipt.symmetric_constitutive_body
    {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    Ok((situated.native, recovered))
}

pub(crate) fn take_indexed_positions<T>(
    values: &mut Vec<T>,
    positions: &[usize],
) -> Result<Vec<T>, NativeSpoolRefusal> {
    if !positions_are_unique(positions) {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    let mut ordered = positions.to_vec();
    ordered.sort_unstable();
    if ordered
        .last()
        .is_some_and(|position| *position >= values.len())
    {
        return Err(NativeSpoolRefusal::ThreadDepositBatchReceipt);
    }
    let mut removed = Vec::with_capacity(ordered.len());
    for position in ordered.into_iter().rev() {
        removed.push((position, values.remove(position)));
    }
    removed.sort_by_key(|(position, _)| *position);
    Ok(removed.into_iter().map(|(_, value)| value).collect())
}

pub(crate) fn appended_positions(start: usize, length: usize) -> Vec<usize> {
    (start..start.saturating_add(length)).collect()
}

pub(crate) fn indexed_positions<T>(values: &[(usize, T)]) -> Vec<usize> {
    values.iter().map(|(position, _)| *position).collect()
}

pub(crate) fn withdraw_situated_deposit(
    situated: SituatedNativeTransportScaffold,
    receipt: NativeThreadDepositReceipt,
) -> Result<(SituatedNativeTransportPredecessor, NativeThreadDeposit), NativeSpoolRefusal> {
    situated.validate()?;
    let admitted_successor_identity_sha256 = situated_scaffold_identity_from_admitted(&situated)?;
    withdraw_situated_deposit_from_admitted(situated, &admitted_successor_identity_sha256, receipt)
}

pub(crate) fn withdraw_situated_deposit_from_admitted(
    situated: SituatedNativeTransportScaffold,
    admitted_successor_identity_sha256: &str,
    receipt: NativeThreadDepositReceipt,
) -> Result<(SituatedNativeTransportPredecessor, NativeThreadDeposit), NativeSpoolRefusal> {
    receipt.validate()?;
    if !is_sha256_identity(admitted_successor_identity_sha256)
        || admitted_successor_identity_sha256 != receipt.successor_identity_sha256
    {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }
    let (
        reduced,
        NativeSituatedThreadWithdrawal {
            original_situated_identity_sha256,
            native,
            mixed_constitutive_families,
            exact_reconstruction_fibres,
        },
    ) = situated.withdraw_thread_from_admitted(
        admitted_successor_identity_sha256,
        &receipt.spool_address,
        &receipt.thread_address,
    )?;
    if original_situated_identity_sha256 != receipt.successor_identity_sha256
        || native.thread_position != receipt.thread_position
        || indexed_positions(&native.serial_pullbacks) != receipt.serial_pullback_positions
        || indexed_positions(&native.generator_descents) != receipt.generator_descent_positions
        || indexed_positions(&native.receiver_factors) != receipt.receiver_factor_positions
        || indexed_positions(&native.mutual_constitutive_responses)
            != receipt.mutual_constitutive_positions
        || indexed_positions(&native.shortest_separators) != receipt.shortest_separator_positions
        || indexed_positions(&native.interchanges) != receipt.interchange_positions
        || indexed_positions(&mixed_constitutive_families) != receipt.mixed_constitutive_positions
        || indexed_positions(&exact_reconstruction_fibres) != receipt.exact_reconstruction_positions
    {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }
    let withdrawal_fibres = native
        .fibre_deltas
        .iter()
        .map(|delta| (delta.native, delta))
        .collect::<BTreeMap<_, _>>();
    if withdrawal_fibres.len() != receipt.fibre_receipts.len()
        || receipt.fibre_receipts.iter().any(|fibre| {
            withdrawal_fibres.get(&fibre.native).is_none_or(|delta| {
                delta.position != fibre.position
                    || delta.occurrences != fibre.occurrences
                    || delta.fibre_departed != fibre.fibre_was_founded
            })
        })
    {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }
    if !native.retained_generator_open_domain_deltas.is_empty() {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }

    let NativeThreadWithdrawal {
        original_identity_sha256: _,
        spool_address,
        thread_position: _,
        thread,
        serial_pullbacks,
        generator_descents,
        retained_generator_open_domain_deltas: _,
        receiver_factors,
        mutual_constitutive_responses,
        shortest_separators,
        interchanges,
        fibre_deltas: _,
    } = native;
    let deposit = NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address,
        thread,
        serial_pullbacks: serial_pullbacks
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        generator_descents: generator_descents
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        receiver_factors: receiver_factors
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        mutual_constitutive_responses: mutual_constitutive_responses
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        mixed_constitutive_families: mixed_constitutive_families
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        shortest_separators: shortest_separators
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
        interchanges: interchanges.into_iter().map(|(_, value)| value).collect(),
        reconstruction_fibre_deltas: receipt
            .fibre_receipts
            .iter()
            .map(|fibre| NativeDepositFibreDelta {
                native: fibre.native,
                occurrences: fibre.occurrences.clone(),
            })
            .collect(),
        exact_reconstruction_fibres: exact_reconstruction_fibres
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
    };
    deposit.validate()?;
    if native_deposit_identity(&deposit)? != receipt.deposit_identity_sha256 {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }
    let predecessor = match receipt.predecessor_kind {
        SituatedNativeTransportPredecessorKind::NativeScaffold => {
            if !reduced.mixed_constitutive_families.is_empty()
                || !reduced.exact_reconstruction_fibres.is_empty()
            {
                return Err(NativeSpoolRefusal::ThreadDepositReceipt);
            }
            SituatedNativeTransportPredecessor::Native(reduced.native)
        }
        SituatedNativeTransportPredecessorKind::SituatedScaffold => {
            SituatedNativeTransportPredecessor::Situated(reduced)
        }
    };
    let predecessor_identity_sha256 = match &predecessor {
        SituatedNativeTransportPredecessor::Native(scaffold) => {
            native_scaffold_identity_from_admitted(scaffold)?
        }
        SituatedNativeTransportPredecessor::Situated(scaffold) => {
            situated_scaffold_identity_from_admitted(scaffold)?
        }
    };
    if predecessor_identity_sha256 != receipt.predecessor_identity_sha256 {
        return Err(NativeSpoolRefusal::ThreadDepositReceipt);
    }
    Ok((predecessor, deposit))
}

pub(crate) fn extract_indexed<T>(
    values: &mut Vec<T>,
    mut withdraw: impl FnMut(&T) -> bool,
) -> Vec<(usize, T)> {
    let mut retained = Vec::with_capacity(values.len());
    let mut removed = Vec::new();
    for (position, value) in values.drain(..).enumerate() {
        if withdraw(&value) {
            removed.push((position, value));
        } else {
            retained.push(value);
        }
    }
    *values = retained;
    removed
}

pub(crate) fn restore_indexed<T>(
    values: &mut Vec<T>,
    mut restored: Vec<(usize, T)>,
) -> Result<(), NativeSpoolRefusal> {
    restored.sort_by_key(|(position, _)| *position);
    for (position, value) in restored {
        if position > values.len() {
            return Err(NativeSpoolRefusal::Restoration);
        }
        values.insert(position, value);
    }
    Ok(())
}

pub(crate) fn native_scaffold_identity(
    scaffold: &NativeTransportScaffold,
) -> Result<String, NativeSpoolRefusal> {
    let bytes = scaffold.canonical_bytes()?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

pub(crate) fn native_scaffold_identity_from_admitted(
    scaffold: &NativeTransportScaffold,
) -> Result<String, NativeSpoolRefusal> {
    let bytes = serde_json::to_vec(scaffold)
        .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

pub(crate) fn situated_scaffold_identity_from_admitted(
    scaffold: &SituatedNativeTransportScaffold,
) -> Result<String, NativeSpoolRefusal> {
    let bytes = serde_json::to_vec(scaffold)
        .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
    Ok(sha256_bytes(&bytes))
}

pub(crate) fn current_observation(
    current: &ExactComplexWaveCurrent,
    stored: &ExactComplexWaveCurrent,
) -> Observation {
    let mut digest = Sha256::new();
    for coordinate in [
        current.real.to_string(),
        current.imaginary.to_string(),
        stored.real.to_string(),
        stored.imaginary.to_string(),
    ] {
        digest.update((coordinate.len() as u64).to_le_bytes());
        digest.update(coordinate.as_bytes());
    }
    Observation(u64::from_le_bytes(
        digest.finalize()[..8]
            .try_into()
            .expect("eight observation octets"),
    ))
}
