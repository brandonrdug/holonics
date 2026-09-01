use super::helpers::{native_scaffold_identity, stage_native_deposit_batch, stage_thread_deposit};
use super::refusal::NativeSpoolRefusal;
use super::*;
use crate::cuda_refine::{CudaRefineExecutor, ResidentComplexIncidence, ResidentNativeWord};

pub const NATIVE_TRANSPORT_SCAFFOLD_SCHEMA: &str = "holonic-engine.native-transport-scaffold.v1";

/// A compatible, source-neutral scaffold of reusable native winding/generator families.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTransportScaffold {
    pub schema: String,
    pub address: String,
    pub spools: Vec<NativeSpool>,
    pub compositions: Vec<NativeSpoolComposition>,
    pub open_exterior: Vec<String>,
}

/// A non-owning, source-neutral view of one occurrence and its exact native carrying section.
///
/// The view can only be founded through [`NativeTransportScaffold::addressed_section`]. Its
/// incidence, Parametron cells, ordered generator word, and reconstruction fibre remain owned by
/// the one mounted scaffold; this type does not copy them into a second topology.
#[derive(Debug)]
pub struct NativeAddressedSection<'a> {
    pub(crate) scaffold: &'a NativeTransportScaffold,
    pub(crate) spool: &'a NativeSpool,
    pub(crate) thread: &'a NativeThread,
    pub(crate) occurrence: &'a NativeThreadOccurrence,
    pub(crate) incidence: &'a NativeIncidenceTerm,
    pub(crate) entering_parametron: &'a NativeParametronCell,
    pub(crate) emitting_parametron: &'a NativeParametronCell,
    pub(crate) reconstruction_fibre: &'a NativeCollapsedFibre,
}

impl<'a> NativeAddressedSection<'a> {
    pub fn scaffold_address(&self) -> &str {
        &self.scaffold.address
    }

    pub fn spool(&self) -> &'a NativeSpool {
        self.spool
    }

    pub fn thread(&self) -> &'a NativeThread {
        self.thread
    }

    pub fn occurrence(&self) -> &'a NativeThreadOccurrence {
        self.occurrence
    }

    pub fn incidence(&self) -> &'a NativeIncidenceTerm {
        self.incidence
    }

    pub fn entering_parametron(&self) -> &'a NativeParametronCell {
        self.entering_parametron
    }

    pub fn emitting_parametron(&self) -> &'a NativeParametronCell {
        self.emitting_parametron
    }

    pub fn reconstruction_fibre(&self) -> &'a NativeCollapsedFibre {
        self.reconstruction_fibre
    }

    pub fn ordered_generator_word(&self) -> &'a [InputId] {
        &self.thread.chronology
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        self.scaffold.validate()?;
        let valid = self
            .scaffold
            .spools
            .iter()
            .any(|candidate| std::ptr::eq(candidate, self.spool))
            && self
                .spool
                .threads
                .iter()
                .any(|candidate| std::ptr::eq(candidate, self.thread))
            && self
                .thread
                .occurrences
                .iter()
                .any(|candidate| std::ptr::eq(candidate, self.occurrence))
            && self.thread.incidence.iter().any(|candidate| {
                std::ptr::eq(candidate, self.incidence)
                    && candidate.occurrence == self.occurrence.occurrence
                    && candidate.from == self.occurrence.entering_native
                    && candidate.to == self.occurrence.emitting_native
            })
            && self.thread.parametrons.iter().any(|candidate| {
                std::ptr::eq(candidate, self.entering_parametron)
                    && candidate.native == self.occurrence.entering_native
            })
            && self.thread.parametrons.iter().any(|candidate| {
                std::ptr::eq(candidate, self.emitting_parametron)
                    && candidate.native == self.occurrence.emitting_native
            })
            && self.spool.reconstruction_fibres.iter().any(|candidate| {
                std::ptr::eq(candidate, self.reconstruction_fibre)
                    && candidate.native == self.occurrence.emitting_native
                    && candidate.occurrences.contains(&self.occurrence.occurrence)
            });
        if !valid {
            return Err(NativeSpoolRefusal::AddressedSection(
                self.occurrence.occurrence,
            ));
        }
        Ok(())
    }
}

impl NativeTransportScaffold {
    pub fn read(bytes: &[u8]) -> Result<Self, NativeSpoolRefusal> {
        let scaffold: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))?;
        scaffold.validate()?;
        Ok(scaffold)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeSpoolRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeSpoolRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeSpoolRefusal> {
        if self.schema != NATIVE_TRANSPORT_SCAFFOLD_SCHEMA {
            return Err(NativeSpoolRefusal::Schema(self.schema.clone()));
        }
        if self.address.is_empty() || self.spools.is_empty() {
            return Err(NativeSpoolRefusal::MalformedScaffold(self.address.clone()));
        }
        let mut spools = BTreeMap::new();
        let mut thread_owner = BTreeMap::new();
        for spool in &self.spools {
            spool.validate()?;
            if spools.insert(spool.address.as_str(), spool).is_some() {
                return Err(NativeSpoolRefusal::DuplicateSpool(spool.address.clone()));
            }
            for thread in &spool.threads {
                if thread_owner
                    .insert(thread.address.as_str(), spool.address.as_str())
                    .is_some()
                {
                    return Err(NativeSpoolRefusal::DuplicateThread(thread.address.clone()));
                }
            }
        }

        let mut graph = BTreeMap::<&str, BTreeSet<&str>>::new();
        for spool in spools.keys() {
            graph.entry(*spool).or_default();
        }
        let mut composition_pairs = BTreeSet::new();
        for composition in &self.compositions {
            let Some(left) = spools.get(composition.left_spool.as_str()) else {
                return Err(NativeSpoolRefusal::ScaffoldComposition);
            };
            let Some(right) = spools.get(composition.right_spool.as_str()) else {
                return Err(NativeSpoolRefusal::ScaffoldComposition);
            };
            if composition.left_spool == composition.right_spool
                || !composition_pairs.insert((
                    composition.left_spool.as_str(),
                    composition.right_spool.as_str(),
                    composition.pullback.left_thread.as_str(),
                    composition.pullback.right_thread.as_str(),
                ))
                || thread_owner.get(composition.pullback.left_thread.as_str())
                    != Some(&left.address.as_str())
                || thread_owner.get(composition.pullback.right_thread.as_str())
                    != Some(&right.address.as_str())
            {
                return Err(NativeSpoolRefusal::ScaffoldComposition);
            }
            let pair = BTreeMap::from([
                (
                    composition.pullback.left_thread.as_str(),
                    left.threads
                        .iter()
                        .find(|thread| thread.address == composition.pullback.left_thread)
                        .ok_or(NativeSpoolRefusal::ScaffoldComposition)?,
                ),
                (
                    composition.pullback.right_thread.as_str(),
                    right
                        .threads
                        .iter()
                        .find(|thread| thread.address == composition.pullback.right_thread)
                        .ok_or(NativeSpoolRefusal::ScaffoldComposition)?,
                ),
            ]);
            validate_pullback(&composition.pullback, &pair)?;
            graph
                .entry(composition.left_spool.as_str())
                .or_default()
                .insert(composition.right_spool.as_str());
            graph
                .entry(composition.right_spool.as_str())
                .or_default()
                .insert(composition.left_spool.as_str());
        }
        if !connected(&graph) {
            return Err(NativeSpoolRefusal::DisconnectedScaffold);
        }
        if self.open_exterior.iter().any(String::is_empty) {
            return Err(NativeSpoolRefusal::OpenExterior(self.address.clone()));
        }
        Ok(())
    }

    /// Atomically found the situated continuation by consuming this admitted native scaffold and
    /// one complete thread deposit.  The predecessor v2 scaffold is not rewritten or aliased.
    pub fn deposit_thread(
        self,
        deposit: NativeThreadDeposit,
    ) -> Result<(SituatedNativeTransportScaffold, NativeThreadDepositReceipt), NativeSpoolRefusal>
    {
        self.validate()?;
        stage_thread_deposit(
            self,
            Vec::new(),
            Vec::new(),
            deposit,
            SituatedNativeTransportPredecessorKind::NativeScaffold,
            None,
        )
    }

    /// Consume a complete cycle population and stage it as one situated constitutive body.
    /// Validation and canonical identity are performed only at the native predecessor and the
    /// complete situated successor, never at chronological-looking intermediate prefixes.
    pub fn deposit_threads(
        self,
        deposits: Vec<NativeThreadDeposit>,
    ) -> Result<
        (
            SituatedNativeTransportScaffold,
            NativeThreadDepositBatchReceipt,
        ),
        NativeSpoolRefusal,
    > {
        stage_native_deposit_batch(self, deposits)
    }

    /// Borrow one admitted occurrence as a complete native section view.  Spool, thread, and
    /// occurrence addresses are all required so equal exterior endpoints can never select a
    /// carrying occurrence by projection.
    pub fn addressed_section(
        &self,
        spool_address: &str,
        thread_address: &str,
        occurrence: EventId,
    ) -> Result<NativeAddressedSection<'_>, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread = spool
            .threads
            .iter()
            .find(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownThread(thread_address.to_owned()))?;
        let occurrence = thread
            .occurrences
            .iter()
            .find(|candidate| candidate.occurrence == occurrence)
            .ok_or(NativeSpoolRefusal::UnknownOccurrence(occurrence))?;
        let incidence = thread
            .incidence
            .iter()
            .find(|term| term.occurrence == occurrence.occurrence)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let entering_parametron = thread
            .parametrons
            .iter()
            .find(|cell| cell.native == occurrence.entering_native)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let emitting_parametron = thread
            .parametrons
            .iter()
            .find(|cell| cell.native == occurrence.emitting_native)
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let reconstruction_fibre = spool
            .reconstruction_fibres
            .iter()
            .find(|fibre| {
                fibre.native == occurrence.emitting_native
                    && fibre.occurrences.contains(&occurrence.occurrence)
            })
            .ok_or(NativeSpoolRefusal::AddressedSection(occurrence.occurrence))?;
        let section = NativeAddressedSection {
            scaffold: self,
            spool,
            thread,
            occurrence,
            incidence,
            entering_parametron,
            emitting_parametron,
            reconstruction_fibre,
        };
        section.validate()?;
        Ok(section)
    }

    /// Mount one declared spool word as continuing resident native transport. The exterior
    /// realization and its witness are neither accepted nor reachable by this owner.
    pub fn mount_word(
        &self,
        spool_address: &str,
        word: &[InputId],
    ) -> Result<ResidentNativeSpoolWord, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        if word.is_empty() {
            return Err(NativeSpoolRefusal::UnknownGenerator(InputId(0)));
        }
        let states = spool.native_population.iter().copied().collect::<Vec<_>>();
        let state_index = states
            .iter()
            .enumerate()
            .map(|(at, native)| (*native, at as u32))
            .collect::<BTreeMap<_, _>>();
        let generators = spool.generator_family.iter().copied().collect::<Vec<_>>();
        let generator_index = generators
            .iter()
            .enumerate()
            .map(|(at, generator)| (*generator, at as u32))
            .collect::<BTreeMap<_, _>>();
        let resident_word = word
            .iter()
            .map(|generator| {
                generator_index
                    .get(generator)
                    .copied()
                    .ok_or(NativeSpoolRefusal::UnknownGenerator(*generator))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let descents = spool
            .generator_descents
            .iter()
            .map(|descent| (descent.generator, descent))
            .collect::<BTreeMap<_, _>>();
        let mut generator_table = Vec::with_capacity(states.len() * generators.len());
        for generator in &generators {
            let descent = descents
                .get(generator)
                .ok_or(NativeSpoolRefusal::UnknownGenerator(*generator))?;
            let steps = descent
                .steps
                .iter()
                .map(|step| (step.from, step.to))
                .collect::<BTreeMap<_, _>>();
            for state in &states {
                let returned = steps
                    .get(state)
                    .ok_or(NativeSpoolRefusal::UnknownNative(*state))?;
                generator_table.push(
                    *state_index
                        .get(returned)
                        .ok_or(NativeSpoolRefusal::UnknownNative(*returned))?,
                );
            }
        }
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let device = card.device_name().to_owned();
        let block_threads = card.block_threads();
        let resident = ResidentNativeWord::mount(
            card,
            states.len(),
            generators.len(),
            &generator_table,
            &resident_word,
        )
        .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let receiver_factors = spool
            .receiver_factors
            .iter()
            .map(|factor| ((factor.native, factor.receiver), factor.observation))
            .collect();
        Ok(ResidentNativeSpoolWord {
            spool_address: spool.address.clone(),
            states,
            state_index,
            receiver_factors,
            device,
            block_threads,
            resident,
        })
    }

    /// Mount one thread's exact incidence/current face on the card. The incidence rows and current
    /// population are derived from the addressed thread itself; no caller width or source chart is
    /// accepted.
    pub fn mount_thread_current(
        &self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<ResidentNativeThreadCurrent, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread = spool
            .threads
            .iter()
            .find(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownThread(thread_address.to_owned()))?;
        let states = thread.native_support.iter().copied().collect::<Vec<_>>();
        let state_index = states
            .iter()
            .enumerate()
            .map(|(at, native)| (*native, at))
            .collect::<BTreeMap<_, _>>();
        let incidence_by_occurrence = thread
            .incidence
            .iter()
            .map(|term| (term.occurrence, term))
            .collect::<BTreeMap<_, _>>();
        let mut incidence = vec![0i64; thread.occurrences.len() * states.len()];
        for (row, occurrence) in thread.occurrences.iter().enumerate() {
            let term = incidence_by_occurrence[&occurrence.occurrence];
            let from = state_index[&term.from];
            let to = state_index[&term.to];
            incidence[row * states.len() + from] -= term.coefficient;
            incidence[row * states.len() + to] += term.coefficient;
        }
        let cells = thread
            .parametrons
            .iter()
            .map(|cell| (cell.native, cell))
            .collect::<BTreeMap<_, _>>();
        let front = states
            .iter()
            .map(|state| cells[state].current.clone())
            .collect::<Vec<_>>();
        let card = CudaRefineExecutor::new()
            .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        let resident = ResidentComplexIncidence::mount(
            card,
            thread.address.clone(),
            0,
            thread.occurrences.len(),
            states.len(),
            &incidence,
        )
        .map_err(|error| NativeSpoolRefusal::Apparatus(error.to_string()))?;
        Ok(ResidentNativeThreadCurrent { front, resident })
    }

    /// Derive the receiver insufficiency exposed by a staged thread withdrawal. Both implicated
    /// occurrences remain in the continuing body plus its reversible delta; the separator is an
    /// actual distinct Complex-Parametron response under the withdrawn generator word.
    pub fn insufficiency_after_withdrawal(
        &self,
        withdrawal: &NativeThreadWithdrawal,
    ) -> Result<ReceiverInsufficiency, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter()
            .find(|spool| spool.address == withdrawal.spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(withdrawal.spool_address.clone()))?;
        let generator = withdrawal
            .generator_descents
            .iter()
            .find(|(_, descent)| {
                descent
                    .steps
                    .iter()
                    .any(|step| step.thread == withdrawal.thread.address)
            })
            .map(|(_, descent)| descent.generator)
            .ok_or(NativeSpoolRefusal::Insufficiency)?;
        let removed_cells = withdrawal
            .thread
            .parametrons
            .iter()
            .map(|cell| (cell.native, cell))
            .collect::<BTreeMap<_, _>>();
        let removed_responses = withdrawal
            .thread
            .constitutive_responses
            .iter()
            .map(|response| ((response.native, response.receiver), response))
            .collect::<BTreeMap<_, _>>();
        for removed in &withdrawal.thread.occurrences {
            for retained_thread in &spool.threads {
                let Some(retained) = retained_thread
                    .occurrences
                    .iter()
                    .find(|candidate| candidate.entering_native == removed.entering_native)
                else {
                    continue;
                };
                let Some(retained_cell) = retained_thread
                    .parametrons
                    .iter()
                    .find(|cell| cell.native == retained.entering_native)
                else {
                    continue;
                };
                let removed_cell = removed_cells[&removed.entering_native];
                for ((native, receiver), removed_response) in &removed_responses {
                    if *native != removed.entering_native {
                        continue;
                    }
                    let Some(retained_response) = retained_thread
                        .constitutive_responses
                        .iter()
                        .find(|response| {
                            response.native == retained.entering_native
                                && response.receiver == *receiver
                        })
                    else {
                        continue;
                    };
                    if removed_cell.current == retained_cell.current
                        && removed_response.stored == retained_response.stored
                    {
                        continue;
                    }
                    let separator = NativeShortestSeparator {
                        left: removed.occurrence,
                        right: retained.occurrence,
                        word: vec![generator],
                        receiver: *receiver,
                        left_observation: current_observation(
                            &removed_cell.current,
                            &removed_response.stored,
                        ),
                        right_observation: current_observation(
                            &retained_cell.current,
                            &retained_response.stored,
                        ),
                    };
                    if separator.left_observation == separator.right_observation {
                        continue;
                    }
                    let insufficiency = ReceiverInsufficiency {
                        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
                        at_occurrence: removed.occurrence,
                        native: removed.entering_native,
                        retained_fibre: BTreeSet::from([removed.occurrence, retained.occurrence]),
                        cause: ReceiverInsufficiencyCause::ReconstructionFibreReopened {
                            separator,
                        },
                        open_exterior: vec![
                            "thread withdrawal separates an admitted Complex-Parametron response"
                                .to_owned(),
                        ],
                    };
                    insufficiency.validate()?;
                    return Ok(insufficiency);
                }
            }
        }
        Err(NativeSpoolRefusal::Insufficiency)
    }

    /// Withdraw one addressed native thread and every dependent receipt as a staged local delta.
    /// The continuing scaffold is consumed, never cloned. Restoration consumes the delta and proves
    /// the original canonical identity.
    pub fn withdraw_thread(
        self,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, NativeThreadWithdrawal), NativeSpoolRefusal> {
        self.validate()?;
        let original_identity_sha256 = native_scaffold_identity(&self)?;
        let (rest, withdrawal) = self.withdraw_thread_from_admitted(
            &original_identity_sha256,
            spool_address,
            thread_address,
        )?;
        rest.validate()?;
        Ok((rest, withdrawal))
    }

    pub(crate) fn withdraw_thread_from_admitted(
        mut self,
        original_identity_sha256: &str,
        spool_address: &str,
        thread_address: &str,
    ) -> Result<(Self, NativeThreadWithdrawal), NativeSpoolRefusal> {
        if !is_sha256_identity(original_identity_sha256) {
            return Err(NativeSpoolRefusal::ThreadDepositReceipt);
        }
        let spool = self
            .spools
            .iter_mut()
            .find(|spool| spool.address == spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(spool_address.to_owned()))?;
        let thread_position = spool
            .threads
            .iter()
            .position(|thread| thread.address == thread_address)
            .ok_or_else(|| NativeSpoolRefusal::DuplicateThread(thread_address.to_owned()))?;
        let thread = spool.threads.remove(thread_position);
        let removed_events = thread
            .occurrences
            .iter()
            .map(|occurrence| occurrence.occurrence)
            .collect::<BTreeSet<_>>();

        let generator_descents = extract_indexed(&mut spool.generator_descents, |descent| {
            descent
                .steps
                .iter()
                .any(|step| step.thread == thread_address)
        });
        for (_, descent) in &generator_descents {
            spool.generator_family.remove(&descent.generator);
        }
        let serial_pullbacks = extract_indexed(&mut spool.serial_pullbacks, |pullback| {
            pullback.left_thread == thread_address || pullback.right_thread == thread_address
        });
        let interchanges = extract_indexed(&mut spool.interchanges, |interchange| {
            interchange.left_thread == thread_address || interchange.right_thread == thread_address
        });
        let shortest_separators = extract_indexed(&mut spool.shortest_separators, |separator| {
            removed_events.contains(&separator.left) || removed_events.contains(&separator.right)
        });
        let mutual_constitutive_responses =
            extract_indexed(&mut spool.mutual_constitutive_responses, |response| {
                removed_events.contains(&response.left_occurrence)
                    || removed_events.contains(&response.right_occurrence)
            });

        let mut fibre_deltas = Vec::new();
        let mut retained_fibres = Vec::new();
        for (position, mut fibre) in spool.reconstruction_fibres.drain(..).enumerate() {
            let withdrawn = fibre
                .occurrences
                .intersection(&removed_events)
                .copied()
                .collect::<BTreeSet<_>>();
            fibre.occurrences = fibre
                .occurrences
                .difference(&removed_events)
                .copied()
                .collect();
            if !withdrawn.is_empty() {
                fibre_deltas.push(NativeWithdrawalFibreDelta {
                    position,
                    native: fibre.native,
                    occurrences: withdrawn,
                    fibre_departed: fibre.occurrences.is_empty(),
                });
            }
            if !fibre.occurrences.is_empty() {
                retained_fibres.push(fibre);
            }
        }
        spool.reconstruction_fibres = retained_fibres;
        spool.native_population = spool
            .threads
            .iter()
            .flat_map(|thread| thread.native_support.iter().copied())
            .collect();
        let retained_native_population = spool.native_population.clone();
        let receiver_factors = extract_indexed(&mut spool.receiver_factors, |factor| {
            !retained_native_population.contains(&factor.native)
        });
        spool.validate()?;
        Ok((
            self,
            NativeThreadWithdrawal {
                original_identity_sha256: original_identity_sha256.to_owned(),
                spool_address: spool_address.to_owned(),
                thread_position,
                thread,
                serial_pullbacks,
                generator_descents,
                receiver_factors,
                mutual_constitutive_responses,
                shortest_separators,
                interchanges,
                fibre_deltas,
            },
        ))
    }

    pub fn restore_thread(
        mut self,
        withdrawal: NativeThreadWithdrawal,
    ) -> Result<Self, NativeSpoolRefusal> {
        self.validate()?;
        let spool = self
            .spools
            .iter_mut()
            .find(|spool| spool.address == withdrawal.spool_address)
            .ok_or_else(|| NativeSpoolRefusal::UnknownSpool(withdrawal.spool_address.clone()))?;
        if spool
            .threads
            .iter()
            .any(|thread| thread.address == withdrawal.thread.address)
            || withdrawal.thread_position > spool.threads.len()
        {
            return Err(NativeSpoolRefusal::Restoration);
        }
        spool
            .threads
            .insert(withdrawal.thread_position, withdrawal.thread);
        restore_indexed(&mut spool.serial_pullbacks, withdrawal.serial_pullbacks)?;
        for (_, descent) in &withdrawal.generator_descents {
            spool.generator_family.insert(descent.generator);
        }
        restore_indexed(&mut spool.generator_descents, withdrawal.generator_descents)?;
        restore_indexed(&mut spool.receiver_factors, withdrawal.receiver_factors)?;
        restore_indexed(
            &mut spool.mutual_constitutive_responses,
            withdrawal.mutual_constitutive_responses,
        )?;
        restore_indexed(
            &mut spool.shortest_separators,
            withdrawal.shortest_separators,
        )?;
        restore_indexed(&mut spool.interchanges, withdrawal.interchanges)?;
        for delta in withdrawal.fibre_deltas {
            if delta.fibre_departed {
                if delta.position > spool.reconstruction_fibres.len() {
                    return Err(NativeSpoolRefusal::Restoration);
                }
                spool.reconstruction_fibres.insert(
                    delta.position,
                    NativeCollapsedFibre {
                        native: delta.native,
                        occurrences: delta.occurrences,
                    },
                );
            } else {
                let fibre = spool
                    .reconstruction_fibres
                    .iter_mut()
                    .find(|fibre| fibre.native == delta.native)
                    .ok_or(NativeSpoolRefusal::Restoration)?;
                fibre.occurrences.extend(delta.occurrences);
            }
        }
        spool.native_population = spool
            .threads
            .iter()
            .flat_map(|thread| thread.native_support.iter().copied())
            .collect();
        self.validate()?;
        if native_scaffold_identity(&self)? != withdrawal.original_identity_sha256 {
            return Err(NativeSpoolRefusal::Restoration);
        }
        Ok(self)
    }
}
