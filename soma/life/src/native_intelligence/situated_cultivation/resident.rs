use super::*;

impl ResidentLaboratoryCultivatedEcology {
    pub fn conduct(&mut self) -> Result<SituatedCultivatedConductReturn, SituatedCultivationError> {
        let returned = self
            .resident
            .conduct(&vec![true; self.factors.len()])
            .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        if returned.sections != self.expected
            || returned.sections.len() != self.factors.len()
            || returned.invariant_transport_reuploaded
            || returned.cpu_semantic_replay_after_device
            || returned.binary_receiver_taken
        {
            return Err(SituatedCultivationError::Apparatus(
                "the laboratory resident return diverged from its one coupled ecology".to_owned(),
            ));
        }
        let factors = self
            .factors
            .iter()
            .zip(&returned.sections)
            .map(
                |((address, incident_threads), current)| SituatedCultivatedConductedFactor {
                    address: address.clone(),
                    incident_threads: incident_threads.clone(),
                    current: current.clone(),
                },
            )
            .collect();
        Ok(SituatedCultivatedConductReturn {
            rest_identity_sha256: self.rest.identity_sha256.clone(),
            factors,
            apparatus: returned,
        })
    }

    pub fn into_rest(self) -> LaboratoryCultivatedRest {
        self.rest
    }
}

impl ResidentSituatedCultivatedEcology {
    /// Conduct every factor currently owned by the rested ecology.  The all-active aperture is
    /// derived from that exact population; targeted ablation is performed by move-owned
    /// withdrawal before remount, not by a caller-authored mask.
    pub fn conduct(&mut self) -> Result<SituatedCultivatedConductReturn, SituatedCultivationError> {
        let returned = self
            .resident
            .conduct(&vec![true; self.factors.len()])
            .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
        if returned.sections != self.expected
            || returned.sections.len() != self.factors.len()
            || returned.invariant_transport_reuploaded
            || returned.cpu_semantic_replay_after_device
            || returned.binary_receiver_taken
        {
            return Err(SituatedCultivationError::Apparatus(
                "the resident return diverged from the exact mounted ecology".to_owned(),
            ));
        }
        let factors = self
            .factors
            .iter()
            .zip(&returned.sections)
            .map(
                |((address, incident_threads), current)| SituatedCultivatedConductedFactor {
                    address: address.clone(),
                    incident_threads: incident_threads.clone(),
                    current: current.clone(),
                },
            )
            .collect();
        Ok(SituatedCultivatedConductReturn {
            rest_identity_sha256: self.rest.identity_sha256.clone(),
            factors,
            apparatus: returned,
        })
    }

    pub fn into_rest(self) -> SituatedCultivatedEcologyRest {
        self.rest
    }
}

pub(crate) type ResidentCoupling = (
    CausalAdjointPulledIncidence,
    Vec<ExactComplexWaveCurrent>,
    Vec<CoupledComplexInteraction>,
    Vec<(String, Vec<String>)>,
    Vec<ExactComplexWaveCurrent>,
);

pub(crate) fn derive_resident_coupling(
    rest: &SituatedCultivatedEcologyRest,
) -> Result<ResidentCoupling, SituatedCultivationError> {
    let primaries = rest
        .branches
        .iter()
        .map(|branch| {
            Ok((
                branch.thread_address.clone(),
                integral_i64_covector(&branch.returned_source_covector)?,
            ))
        })
        .collect::<Result<Vec<_>, SituatedCultivationError>>()?;
    derive_resident_coupling_from(&rest.ecology, &primaries)
}

/// Derive the same coupled resident word after two or more returned differences. Every original
/// branch retains its exact integral winding coefficient; each complete returned passage is one
/// additional primary holon whose constitutive contacts carry its rank-four covector.
pub(crate) fn derive_recurrent_resident_coupling(
    rest: &RecurrentLaboratoryCultivatedRest,
) -> Result<ResidentCoupling, SituatedCultivationError> {
    rest.validate()?;
    let mut primaries = rest
        .branches()
        .iter()
        .map(|branch| {
            Ok((
                branch.thread_address.clone(),
                integral_i64_covector(&branch.returned_source_covector)?,
            ))
        })
        .collect::<Result<Vec<_>, SituatedCultivationError>>()?;
    primaries.extend(
        rest.returned_deposits()
            .iter()
            .map(|deposit| (deposit.thread_address.clone(), 1)),
    );
    derive_resident_coupling_from(rest.ecology(), &primaries)
}

pub(super) fn derive_resident_coupling_from(
    ecology: &SituatedNativeTransportScaffold,
    primaries: &[(String, i64)],
) -> Result<ResidentCoupling, SituatedCultivationError> {
    let branch_population = primaries.len();
    let mixed = ecology.mixed_constitutive_families();
    if branch_population == 0 || mixed.is_empty() {
        return Err(SituatedCultivationError::Apparatus(
            "the coupled rest has no primary or mixed population".to_owned(),
        ));
    }
    let branch_positions = primaries
        .iter()
        .enumerate()
        .map(|(at, (thread, _))| (thread.as_str(), at))
        .collect::<BTreeMap<_, _>>();

    let mut rows = Vec::with_capacity(branch_population + mixed.len());
    let mut front = Vec::with_capacity(branch_population);
    let mut factors = Vec::with_capacity(branch_population + mixed.len());
    let mut expected = Vec::with_capacity(branch_population + mixed.len());
    for (at, (thread_address, coefficient)) in primaries.iter().enumerate() {
        let mut row = vec![0i64; branch_population];
        row[at] = *coefficient;
        rows.push(row);
        let thread = ecology
            .native()
            .spools
            .iter()
            .flat_map(|spool| &spool.threads)
            .find(|thread| thread.address == *thread_address)
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(format!(
                    "deposited branch {} has no owned thread",
                    thread_address
                ))
            })?;
        let emitting_native = thread
            .occurrences
            .first()
            .map(|occurrence| occurrence.emitting_native)
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(format!(
                    "deposited branch {} has no occurrence current",
                    thread_address
                ))
            })?;
        let current = thread
            .parametrons
            .iter()
            .find(|cell| cell.native == emitting_native)
            .map(|cell| cell.current.clone())
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(format!(
                    "deposited branch {} has no emitting Complex-Parametron",
                    thread_address
                ))
            })?;
        expected.push(current.scaled(&Rat::from_integer(BigInt::from(*coefficient))));
        front.push(current);
        factors.push((thread_address.clone(), vec![thread_address.clone()]));
    }

    let mut interactions = Vec::with_capacity(mixed.len());
    for (mixed_at, family) in mixed.iter().enumerate() {
        let left = *branch_positions
            .get(family.left_thread.as_str())
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(format!(
                    "mixed family {} lost its left factor",
                    family.address
                ))
            })?;
        let right = *branch_positions
            .get(family.right_thread.as_str())
            .ok_or_else(|| {
                SituatedCultivationError::Ecology(format!(
                    "mixed family {} lost its right factor",
                    family.address
                ))
            })?;
        let output = branch_population + mixed_at;
        rows.push(vec![0i64; branch_population]);
        interactions.push(CoupledComplexInteraction {
            output_factor: u32::try_from(output).map_err(|_| {
                SituatedCultivationError::Apparatus(
                    "the derived factor population exceeds the card address line".to_owned(),
                )
            })?,
            left_factor: u32::try_from(left).map_err(|_| {
                SituatedCultivationError::Apparatus(
                    "the left factor population exceeds the card address line".to_owned(),
                )
            })?,
            right_factor: u32::try_from(right).map_err(|_| {
                SituatedCultivationError::Apparatus(
                    "the right factor population exceeds the card address line".to_owned(),
                )
            })?,
            contribution: family.mixed_remainder.clone(),
        });
        expected.push(family.mixed_remainder.clone());
        factors.push((
            family.address.clone(),
            vec![family.left_thread.clone(), family.right_thread.clone()],
        ));
    }
    let incidence = CausalAdjointPulledIncidence::found(rows)
        .map_err(|error| SituatedCultivationError::Apparatus(error.to_string()))?;
    Ok((incidence, front, interactions, factors, expected))
}

pub(super) fn derive_branch_deposit(
    branch_index: usize,
    spool_address: &str,
    thread_addresses: &[String],
    k3_branches: &[K3PullbackBranch],
    covers: &[NativeStateExchangeCover],
    mixed: &[MixedConstitutiveInteractionFamily],
    receiver: holonic_engine::receiver_exact_compression::ReceiverId,
    dependent_receiver_support: &BTreeSet<NativeStateId>,
) -> Result<(NativeThreadDeposit, SituatedCultivationBranch), SituatedCultivationError> {
    let k3 = k3_branches.get(branch_index).ok_or_else(|| {
        SituatedCultivationError::Descent("branch escaped the K3 population".to_owned())
    })?;
    let thread_address = thread_addresses[branch_index].clone();
    let locals = covers
        .iter()
        .map(|cover| {
            cover
                .locals
                .iter()
                .find(|local| local.address.branch == branch_index)
                .map(|local| (cover, local))
                .ok_or_else(|| {
                    SituatedCultivationError::Descent(format!(
                        "receiver-history fibre {} lacks K3 branch {branch_index}",
                        cover.native.0
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let first = locals.first().ok_or_else(|| {
        SituatedCultivationError::Descent("the branch local family is empty".to_owned())
    })?;
    let returned_source_covector = first
        .1
        .situated
        .causal_adjoint
        .returned_source_covector
        .clone();
    if locals.iter().any(|(_, local)| {
        local.situated.causal_adjoint.returned_source_covector != returned_source_covector
            || local.situated.complex_difference != first.1.situated.complex_difference
    }) {
        return Err(SituatedCultivationError::Descent(
            "a branch family cannot compact because its returned current varies".to_owned(),
        ));
    }
    let coefficient = integral_i64_covector(&returned_source_covector)?;

    // The deposited occurrence is the actual later-return arm of the retained K3 pullback.  Its
    // predecessor retains the candidate event; the exact fibre below owns the complete join.
    // Replacing this with a direct candidate-start → return-end edge would lose a boundary map.
    let mut occurrences = Vec::with_capacity(locals.len());
    let mut incidence = Vec::with_capacity(locals.len());
    let mut reconstruction_fibre = BTreeSet::new();
    let mut native_support = BTreeSet::new();
    let mut parametrons = Vec::with_capacity(locals.len());
    let mut constitutive_responses = Vec::with_capacity(locals.len());
    let mut receiver_consequences = Vec::with_capacity(locals.len());
    let mut reconstruction_fibre_deltas = Vec::with_capacity(locals.len());
    let mut exact_reconstruction_fibres = Vec::with_capacity(locals.len());
    for (ordinal, (cover, local)) in locals.iter().enumerate() {
        let occurrence = local.situated.return_event;
        let native = cover.native;
        if !reconstruction_fibre.insert(occurrence) {
            return Err(SituatedCultivationError::Descent(
                "two situated locals collapsed to one carrying occurrence".to_owned(),
            ));
        }
        occurrences.push(holonic_engine::native_spool::NativeThreadOccurrence {
            occurrence,
            predecessor: Some(local.situated.candidate_event),
            entering_port: OccurrencePort::input(occurrence, ordinal),
            emitting_port: OccurrencePort::output(occurrence, ordinal),
            entering_native: native,
            emitting_native: native,
        });
        incidence.push(NativeIncidenceTerm {
            occurrence,
            from: native,
            to: native,
            coefficient,
        });
        native_support.insert(native);
        let difference = &local.situated.complex_difference;
        parametrons.push(NativeParametronCell {
            native,
            section: difference.emitting_section.clone(),
            current: difference.emitting_current.clone(),
            relative_phase: k3.returned.relative_phase.clone(),
            hand: k3.returned.hand,
        });
        constitutive_responses.push(NativeConstitutiveResponse {
            native,
            receiver,
            presented: difference.emitting_section.clone(),
            stored: difference.emitting_current.clone(),
        });
        let observation = local
            .returned_native
            .members
            .first()
            .and_then(|member| {
                member
                    .receiver_faces
                    .iter()
                    .find(|face| face.receiver == receiver)
            })
            .map(|face| face.observation)
            .ok_or_else(|| {
                SituatedCultivationError::Descent(
                    "one receiver-history factor lost its returned receiver face".to_owned(),
                )
            })?;
        receiver_consequences.push(NativeReceiverConsequence {
            native,
            receiver,
            observation,
        });
        reconstruction_fibre_deltas.push(NativeDepositFibreDelta {
            native,
            occurrences: BTreeSet::from([occurrence]),
        });
        // The hot rest retains the sealed candidate and actual return events, not the source
        // exchange's interior event population.  Their addressed pullback is the complete local
        // lineage needed by later conduct and exact reconstruction.
        let occurrence_fibre =
            BTreeSet::from([local.situated.candidate_event, local.situated.return_event]);
        // The physical K3 kernel is shared across its complete lineage fibre. The hot cultivated
        // support is therefore the receiver-history factor carried by this exact local; raw K3
        // state addresses remain recoverable from `k3.lineage_fibre` and must not masquerade as
        // cultivated factor coordinates.
        let k3_native_support = BTreeSet::from([cover.native]);
        exact_reconstruction_fibres.push(NativeExactReconstructionFibre {
            address: format!(
                "native-situated-fibre/{branch_index}/{}",
                local.situated.identity_sha256
            ),
            thread: thread_address.clone(),
            return_operator: local.situated.causal_adjoint.composite_adjoint.clone(),
            terminal_covector: local.situated.causal_adjoint.terminal_covector.clone(),
            returned_covector: local
                .situated
                .causal_adjoint
                .returned_source_covector
                .clone(),
            particular: local
                .situated
                .causal_adjoint
                .reconstruction_fibre
                .particular
                .clone(),
            radical: local.situated.causal_adjoint.radical.clone(),
            obstruction: local.situated.causal_adjoint.obstruction.clone(),
            carrying_pullback: NativePullbackOccurrence {
                left: local.situated.candidate_event,
                right: local.situated.return_event,
                joining_native: native,
            },
            k3_native_support,
            dependent_receiver_fibre: BTreeSet::from([cover.native]),
            occurrences: occurrence_fibre,
            open_exterior: vec![
                "receiver and successor histories outside the admitted family remain open"
                    .to_owned(),
            ],
        });
    }

    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: thread_address.clone(),
        entering_boundary: k3.returned.entering_boundary,
        emitting_boundary: k3.returned.emitting_boundary,
        entering_carrier: "native-situated-complex-parametron-current".to_owned(),
        emitting_carrier: "native-situated-complex-parametron-current".to_owned(),
        occurrences,
        native_support: native_support.clone(),
        incidence,
        parametrons,
        constitutive_responses,
        chronology: k3.returned.ordered_word.clone(),
        receiver_consequences,
        obstruction: None,
        open_exterior: vec![
            "future receiver histories beyond the cultivated family remain open".to_owned(),
        ],
        reconstruction_fibre: reconstruction_fibre.clone(),
    };

    let mixed_constitutive_families = mixed
        .iter()
        .filter(|family| family.right_branch == branch_index)
        .map(|family| {
            native_mixed_family(
                family,
                thread_addresses,
                receiver,
                dependent_receiver_support,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let deposit = NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address: spool_address.to_owned(),
        thread,
        serial_pullbacks: Vec::new(),
        generator_descents: Vec::new(),
        receiver_factors: Vec::new(),
        mutual_constitutive_responses: Vec::new(),
        mixed_constitutive_families,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        reconstruction_fibre_deltas,
        exact_reconstruction_fibres,
    };
    deposit
        .validate()
        .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;

    let return_operator_identity_sha256 = digest_json(
        &locals
            .iter()
            .map(|(_, local)| {
                (
                    &local.situated.causal_adjoint.composite_adjoint,
                    &local.situated.causal_adjoint.terminal_covector,
                    &local.situated.causal_adjoint.returned_source_covector,
                )
            })
            .collect::<Vec<_>>(),
    )?;
    let occurrence_population_identity_sha256 = digest_json(&reconstruction_fibre)?;
    Ok((
        deposit,
        SituatedCultivationBranch {
            branch: branch_index,
            k3_pullback_address: k3.address.clone(),
            thread_address,
            returned_source_covector,
            local_population: locals.len(),
            exact_fibre_population: locals.len(),
            return_operator_identity_sha256,
            occurrence_population_identity_sha256,
        },
    ))
}

pub(super) fn derive_returned_difference_deposit(
    ecology: &SituatedNativeTransportScaffold,
    branches: &[SituatedCultivationBranch],
    prior_returns: &[SituatedReturnedDifferenceDeposit],
    difference: &SituatedDifferenceSection,
) -> Result<(NativeThreadDeposit, ReturnedDifferenceStaging), SituatedCultivationError> {
    let branch_threads = branches
        .iter()
        .map(|branch| branch.thread_address.clone())
        .collect::<Vec<_>>();
    let prior_returns = prior_returns
        .iter()
        .map(|returned| {
            (
                returned.thread_address.clone(),
                returned.winding_coefficients.clone(),
            )
        })
        .collect::<Vec<_>>();
    derive_returned_difference_deposit_from_history(
        ecology,
        &branch_threads,
        &prior_returns,
        difference,
    )
    .map_err(|error| {
        match error {
        crate::native_intelligence::returned_difference_deposit::ReturnedDifferenceError::Descent(
            message,
        ) => SituatedCultivationError::Descent(message),
        crate::native_intelligence::returned_difference_deposit::ReturnedDifferenceError::Ecology(
            message,
        ) => SituatedCultivationError::Ecology(message),
    }
    })
}

/// Shared native deposit constructor for any source-neutral history view. The active UAR0 body
/// has deliberately different branch/deposit wire types, but the returned native thread and its
/// exact constitutive/reconstruction fibre are the same owned passage.
fn native_mixed_family(
    family: &MixedConstitutiveInteractionFamily,
    thread_addresses: &[String],
    receiver: holonic_engine::receiver_exact_compression::ReceiverId,
    dependent_receiver_support: &BTreeSet<NativeStateId>,
) -> Result<NativeMixedConstitutiveFamily, SituatedCultivationError> {
    let left_thread = thread_addresses.get(family.left_branch).ok_or_else(|| {
        SituatedCultivationError::Descent("mixed left branch escaped K3".to_owned())
    })?;
    let right_thread = thread_addresses.get(family.right_branch).ok_or_else(|| {
        SituatedCultivationError::Descent("mixed right branch escaped K3".to_owned())
    })?;
    let native = NativeMixedConstitutiveFamily {
        address: format!(
            "native-mixed-finite-leibniz/{}/{}",
            family.left_branch, family.right_branch
        ),
        left_thread: left_thread.clone(),
        right_thread: right_thread.clone(),
        receiver,
        storage: family.storage.clone(),
        candidate_left: family.candidate_left.clone(),
        candidate_right: family.candidate_right.clone(),
        returned_left: family.returned_left.clone(),
        returned_right: family.returned_right.clone(),
        left_difference: family.left_difference.clone(),
        right_difference: family.right_difference.clone(),
        candidate_product: family.candidate_product.clone(),
        source_linear_terms: family.source_linear_terms.clone(),
        mixed_remainder: family.mixed_remainder.clone(),
        reconstructed_returned_product: family.reconstructed_returned_product.clone(),
        returned_product: family.returned_product.clone(),
        dependent_receiver_support: dependent_receiver_support.clone(),
        pair_population: family.pair_population,
    };
    native
        .validate()
        .map_err(|error| SituatedCultivationError::Ecology(error.to_string()))?;
    Ok(native)
}

pub(super) fn integral_i64_covector(covector: &[Rat]) -> Result<i64, SituatedCultivationError> {
    let [coefficient] = covector else {
        return Err(SituatedCultivationError::Descent(
            "the compact branch carrier requires the returned one-dimensional quantity line"
                .to_owned(),
        ));
    };
    if coefficient.denom() != &BigInt::from(1) {
        return Err(SituatedCultivationError::Descent(
            "the returned covector is exact but does not enter this integral incidence chart"
                .to_owned(),
        ));
    }
    coefficient.numer().to_string().parse::<i64>().map_err(|_| {
        SituatedCultivationError::Descent(
            "the returned covector exceeds the signed incidence apparatus".to_owned(),
        )
    })
}

pub(super) fn common_k3_spool_address(
    branches: &[K3PullbackBranch],
) -> Result<String, SituatedCultivationError> {
    let first = branches.first().ok_or_else(|| {
        SituatedCultivationError::Descent("the K3 branch population is empty".to_owned())
    })?;
    let spool = first.candidate.address.spool.clone();
    if branches.iter().any(|branch| {
        branch.candidate.address.spool != spool || branch.returned.address.spool != spool
    }) {
        return Err(SituatedCultivationError::Descent(
            "the bounded L2 deposit crosses more than one spool owner".to_owned(),
        ));
    }
    Ok(spool)
}

pub(super) fn digest_json(value: &impl Serialize) -> Result<String, SituatedCultivationError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| SituatedCultivationError::Wire(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}
