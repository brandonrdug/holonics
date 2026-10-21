//! Exact, transient forward reads for one aperture-one source passage.
//!
//! The source counts have an exact prefix scan, but the field's words are a carried chain: every
//! read opens on the preceding word's reception end. This owner advances that chain once, keeps
//! each word with its own producing operands and faces, and returns the closing source/address
//! state without publishing any part of it into the resident.

use super::*;

/// One forward word and the exact operands its later return consumes. The word is evaluated once
/// by `Reference::refine_view`; its ratio, opening and faces are detached from the local working
/// resident before the next source prefix is read.
#[derive(Debug)]
pub(crate) struct EpochRead {
    pub(crate) source_preparation: Option<crate::hnn::word::action::PortPreparationReceipt>,
    pub(crate) ratio: PendingRatio,
    pub(crate) word: EpochWord,
    pub(crate) opening: WordOpening,
    pub(crate) faces: Faces,
    pub(crate) commit: u64,
    /// The actual producing release's physical balance, at its carried last crossing.
    pub(crate) energy: WordBalance,
    pub(crate) forward_span: Option<crate::hnn::word::scan::ForwardSpanReading>,
    /// The actual preceding word's join inside this batch; no predecessor is fabricated.
    pub(crate) chained: Option<ChainedBalance>,
}

/// The finite candidate comparison consumes these readings, never an adjoint of its words.
/// Every native/selected forward and physical check still executes before this projection.
/// The unused word/opening/join dies at its cell, instead of surviving the whole probe.
#[derive(Debug)]
pub(crate) struct EpochProbeRead {
    pub(crate) ratio: PendingRatio,
    pub(crate) faces: Faces,
}

fn retain_epoch_return(read: EpochRead) -> (EpochRead, WordBalance) {
    let previous = read.energy.clone();
    (read, previous)
}

fn retain_epoch_probe(read: EpochRead) -> (EpochProbeRead, WordBalance) {
    let EpochRead { ratio, faces, energy, .. } = read;
    (EpochProbeRead { ratio, faces }, energy)
}

/// Either the explicitly native kept word or the selected executor's own
/// forward record. This enum never manufactures a native Word for a card read.
#[derive(Debug)]
pub(crate) enum EpochWord {
    Native(KeptWord),
    Executed(Box<dyn observed::ObservedEpochWord>),
}

impl EpochWord {
    pub(crate) fn tube_passages(&self) -> Result<Vec<crate::hnn::ring::TubePassage>, HnnError> {
        match self {
            Self::Native(word) => word.tube_passages(),
            Self::Executed(word) => word.tube_passages(),
        }
    }

    pub(crate) fn charts(&self) -> Vec<ChartReading> {
        match self {
            Self::Native(word) => word.operands().charts(),
            Self::Executed(word) => word.charts(),
        }
    }

    pub(crate) fn return_at(
        self,
        field: &Field,
        execution: &dyn observed::ObservedEpochExecution,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        match self {
            Self::Native(word) => execution.pull_back(word.resume(field), covector, map, phases),
            Self::Executed(word) => word.return_at(field, execution, covector, map, phases),
        }
    }

    #[cfg(test)]
    pub(crate) fn operands(&self) -> &Operands {
        match self {
            Self::Native(word) => word.operands(),
            Self::Executed(_) => panic!("native operand control requested from another executor"),
        }
    }

    #[cfg(test)]
    pub(crate) fn anchor(&self, step: usize, ring: usize) -> Option<&[Rat]> {
        match self {
            Self::Native(word) => word.anchor(step, ring),
            Self::Executed(_) => panic!("native anchor control requested from another executor"),
        }
    }

    #[cfg(test)]
    pub(crate) fn resume(self, field: &Field) -> Word<'_> {
        match self {
            Self::Native(word) => word.resume(field),
            Self::Executed(_) => panic!("native Word requested from another executor"),
        }
    }
}

/// A tape-free epoch forward result. `reads` holds this epoch's full or compact transient readings;
/// `source`, `current` and `address` are the exact closing values after the consumed prefix.
#[derive(Debug)]
pub(crate) struct EpochForward<R = EpochRead> {
    pub(crate) prepared_input: Option<prepared_input::PreparedInputState>,
    /// Every retained reading in this batch belongs to this one material version.
    pub(crate) commit: u64,
    pub(crate) reads: Vec<R>,
    /// Requested transient cuts only, never a per-cell retained state chain.
    pub(crate) prefixes: BTreeMap<usize, Resident>,
    pub(crate) consumed: usize,
    pub(crate) carry_out: bool,
    pub(crate) carried: Option<ReceptionCarry>,
    pub(crate) charts: Charts,
    pub(crate) wall: WallTimes,
    pub(crate) tally: ChartTally,
    pub(crate) current: Current,
    pub(crate) source: SourceMoment,
    pub(crate) address: ActiveAddress,
}

impl Reference {
    /// Read one aperture-one encoded passage through the current constitution. Source moments are
    /// scanned first, then each word is run once in cell order, carrying `A = 0` motion and warm
    /// charts from its predecessor. The input resident is immutable: all forward state lives in a
    /// local clone and is returned only after the entire admitted prefix succeeds.
    pub(crate) fn read_epoch(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
    ) -> Result<EpochForward, HnnError> {
        self.read_epoch_at_cuts(resident, moment, phases, cells, &[])
    }

    pub(crate) fn read_epoch_at_cuts(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
        cuts: &[usize],
    ) -> Result<EpochForward, HnnError> {
        self.read_epoch_at_cuts_for(
            resident, moment, phases, cells, cuts, None, retain_epoch_return,
        )
    }

    pub(crate) fn read_epoch_at_cuts_with_execution(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
        cuts: &[usize],
        execution: &dyn observed::ObservedEpochExecution,
    ) -> Result<EpochForward, HnnError> {
        self.read_epoch_at_cuts_for(
            resident, moment, phases, cells, cuts, Some(execution), retain_epoch_return,
        )
    }

    /// The same actual candidate chain, retaining only what its finite comparison reads.
    /// It performs all original admissions, per-word physical checks and closing joins.
    pub(crate) fn read_epoch_probe_at_cuts(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
        cuts: &[usize],
    ) -> Result<EpochForward<EpochProbeRead>, HnnError> {
        self.read_epoch_at_cuts_for(
            resident, moment, phases, cells, cuts, None, retain_epoch_probe,
        )
    }

    /// The explicitly selected executor still supplies each actual candidate Word. Its
    /// unused return handle is dropped only after authentication and physical checks.
    pub(crate) fn read_epoch_probe_at_cuts_with_execution(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
        cuts: &[usize],
        execution: &dyn observed::ObservedEpochExecution,
    ) -> Result<EpochForward<EpochProbeRead>, HnnError> {
        self.read_epoch_at_cuts_for(
            resident, moment, phases, cells, cuts, Some(execution), retain_epoch_probe,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn read_epoch_at_cuts_for<R>(
        &self,
        resident: &Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
        cells: &Encoded,
        cuts: &[usize],
        execution: Option<&dyn observed::ObservedEpochExecution>,
        mut retain: impl FnMut(EpochRead) -> (R, WordBalance),
    ) -> Result<EpochForward<R>, HnnError> {
        if self.reception != Reception::Carry(Absorption::Nothing) {
            return Err(HnnError::Unadmitted {
                reason: "an epoch's carried forward requires Reception::Carry(Absorption::Nothing)",
            });
        }
        if phases.aperture() != 1 {
            return Err(HnnError::Unadmitted {
                reason: "an epoch forward reads one aperture-one receiving phase per cell",
            });
        }
        resident.admit_exact_current()?;
        if resident.observed_epoch_terminal {
            return Err(HnnError::Unadmitted {
                reason: "a terminal partial epoch cannot open another forward passage",
            });
        }
        if resident.aeon.awaiting {
            return Err(HnnError::AeonAwaitingClose);
        }
        if resident.stop.is_some() {
            return Err(HnnError::Unadmitted {
                reason: "a stopped resident cannot open another epoch forward",
            });
        }
        if !resident.pending.is_empty() || !resident.staged.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "an epoch forward requires no pending or staged reception activity",
            });
        }

        let field = &resident.field;
        field.admit(cells)?;
        cells.check_observed_material(&resident.constitution)?;
        if !cells.is_empty() {
            field.capacity_for(cells)?;
        }
        for open in resident.moments.values() {
            SourceCapacity::checked_of(open, field, &resident.current)?;
        }
        let opening_source = resident
            .moments
            .get(moment)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Moment(*moment),
            })?;
        let scan = opening_source.scan_epoch(field, &resident.current, cells)?;
        let consumed = scan.consumed();
        let carry_out = scan.carry_out();
        if cuts.iter().any(|&cut| cut == 0 || cut > consumed) {
            return Err(HnnError::Unadmitted {
                reason: "an epoch prefix cut lies inside the actually consumed passage",
            });
        }
        let closing_current = scan.post_current(field)?;
        let closing_source = scan.post_moment()?;
        SourceCapacity::checked_of(&closing_source, field, &closing_current)?;

        // An ingest advances the selected source and shared clock, then certifies every sibling
        // source against the actual reached lift. Preserve that refusal before producing reads.
        let external_cells = u64::try_from(consumed).map_err(|_| HnnError::CountOverflow)?;
        let external_ticks = closing_current
            .lift()
            .iter()
            .zip(resident.current.lift())
            .map(|(after, before)| {
                u64::try_from(after - before).map_err(|_| HnnError::CountOverflow)
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (other_id, open) in &resident.moments {
            if other_id != moment && consumed != 0 {
                open.check_clock_synchronization(
                    field,
                    &closing_current,
                    external_cells,
                    &external_ticks,
                )?;
            }
        }

        let commit = resident.constitution.commit();
        let mut working = resident.clone();
        let mut reads = Vec::with_capacity(consumed);
        let mut prefixes = BTreeMap::new();
        let mut previous_energy: Option<WordBalance> = None;
        let mut rings = crate::hnn::propagation::RingScope::new(field, &resident.constitution);
        for at in 0..consumed {
            working.current = scan.current_at(field, at)?;
            working.moments.insert(*moment, scan.moment_at(at)?);
            // Read the same unsplit opening as the existing exposure balance consumer.
            // Material is fixed in this forward batch; source and lift are this prefix's.
            let energy_opening = match (&previous_energy, &working.carried) {
                (Some(previous), Some(carry)) if previous.change == carry.change => {
                    let form = PowerForm::read(field, &resident.constitution, &working.current)?;
                    let source = working.moments.get(moment).ok_or(HnnError::UnknownHandle {
                        handle: Handle::Moment(*moment),
                    })?.open_storage(field, &resident.constitution, &working.current)?;
                    let mut opened = form.opening(field, carry)?;
                    for (wave, injection) in opened.storage.iter_mut().zip(source) {
                        *wave = crate::ratio::linear::vector::add(wave, &injection);
                    }
                    Some((form, carry.clone(), opened))
                }
                (None, _) => None,
                _ => return Err(HnnError::Unadmitted {
                    reason: "an epoch energy join keeps its actual preceding carried crossing",
                }),
            };

            let mut read = if let Some(execution) = execution {
                let (mut ratio, opening, id) = self.prepare_refine(
                    &working,
                    moment,
                    phases,
                    &crate::hnn::ring::modes::ModeView::whole(),
                    field,
                    &resident.constitution,
                )?;
                if ratio.prepared_input().is_some(){execution.admit_prepared_input()?;}
                let start = Instant::now();
                let forward = execution.forward_scoped(
                    &mut observed::ObservedEpochForwardContext::new(&mut rings),
                    &ratio,
                    &mut working.charts,
                    &opening,
                )?;
                ratio.admit_observed_read(field, &forward.anchors, &forward.faces)?;
                if forward.producing_commit != commit
                    || forward.anchors.len() != phases.aperture()
                    || forward.faces.faces.len() != phases.aperture()
                    || forward.faces.logits.len() != phases.aperture()
                    || forward.released.ticks != phases.junction_steps()
                    || !forward.reception_end.fits(field)
                    || forward.released.balances.len() != phases.junction_steps().saturating_sub(1)
                    || forward.released.resonators.len() != (0..field.rings().len())
                        .filter(|&ring| resident.constitution.ring_resonator(ring).is_some()).count()
                {
                    return Err(HnnError::Unadmitted {
                        reason: "an executed epoch word keeps its producing commit and field-shaped reception end",
                    });
                }
                // Preserve the ordinary refine's path admission even though the
                // observed owner does not publish its unused per-word port receipt.
                path_attenuation(
                    field,
                    ratio.anchor(),
                    phases.ring(),
                    phases.last_epoch(),
                    phases.grain(),
                )?;
                let energy = WordBalance::carried(
                    &forward.released, forward.reception_end.change.clone(),
                );
                if !energy.closes() || !forward.released.balances.iter().all(|balance| balance.closes()) {
                    return Err(HnnError::Unadmitted {
                        reason: "an executed epoch word supplies its own closing physical balance",
                    });
                }
                working.tally.read(&forward.released.charts);
                working.wall.refine_read += start.elapsed();
                working.next = id.0;
                working.carried = Some(forward.reception_end.absorbed(Absorption::Nothing));
                working.carried_error = None;
                EpochRead {
                    source_preparation: forward.source_preparation,
                    ratio,
                    word: EpochWord::Executed(forward.word),
                    forward_span: forward.forward_span,
                    opening,
                    faces: forward.faces,
                    commit,
                    energy,
                    chained: None,
                }
            } else {
                let (id, refined) = self.refine_view_scoped(
                    &mut working,
                    moment,
                    phases,
                    &crate::hnn::ring::modes::ModeView::whole(),
                    Some(&mut rings),
                )?;
                let (energy,source_preparation) = match refined.receipt.detail {
                    ReceiptDetail::Refine { word, source_preparation, .. } => (*word,source_preparation),
                    _ => return Err(HnnError::Unadmitted {
                        reason: "a native epoch word retains its actual producing physical receipt",
                    }),
                };
                if !energy.closes() {
                    return Err(HnnError::Unadmitted {
                        reason: "a native epoch word supplies its own closing physical balance",
                    });
                }
                let slot = working
                    .pending
                    .remove(&id)
                    .expect("the refine just inserted its pending slot");
                let kept = slot.kept.ok_or(HnnError::Unadmitted {
                    reason: "an epoch forward retains the word from its own successful read",
                })?;
                if kept.commit != commit || slot.ratio.commit() != commit {
                    return Err(HnnError::Unadmitted {
                        reason: "an epoch forward reads every word through its opening material version",
                    });
                }
                EpochRead {
                    source_preparation,
                    ratio: slot.ratio,
                    word: EpochWord::Native(kept.word),
                    forward_span: None,
                    opening: slot.opening,
                    faces: kept.faces,
                    commit: kept.commit,
                    energy,
                    chained: None,
                }
            };
            if let (Some(previous), Some((form, carry, opened))) =
                (&previous_energy, energy_opening)
            {
                let mut opened=opened;
                if let Some(prep)=&read.source_preparation{
                    if !prep.closes(){return Err(HnnError::Unadmitted{reason:"prepared opening work closes before ticks"});}
                    // Source imposition now includes the actual control exactly once.
                    // No tick/World-return term is fabricated for Wprep.
                    for(x,d)in opened.storage[0].iter_mut().zip(&prep.added){*x+=d;}
                }
                let joined = ChainedBalance::read(field, previous, &form, &carry, &opened, &read.energy)?;
                if !joined.closes() || !joined.lift_emits() {
                    return Err(HnnError::Unadmitted {
                        reason: "an epoch energy join closes at its actual source and reference crossing",
                    });
                }
                read.chained = Some(joined);
            }
            let input_cut=read.ratio.prepared_input().cloned();
            let (retained, energy) = retain(read);
            previous_energy = Some(energy);
            reads.push(retained);

            let class = cells.cells()[at].class();
            if let Some(input)=&mut working.prepared_input{
                match input.mode(){
                    prepared_input::PrefixMode::Training=>input.after_actual(input_cut.ok_or(HnnError::Unadmitted{reason:"actual prepared epoch retains its original producing packet"})?,class)?,
                    prepared_input::PrefixMode::Forecast=>input.after_forecast(class)?,
                }
            }
            working.address.receive_at(class, cells.advance(at))?;
            working.address.refresh(field, &working.constitution)?;
            if cuts.contains(&(at + 1)) {
                let mut prefix = working.clone();
                prefix.current = scan.current_at(field, at + 1)?;
                prefix.moments.insert(*moment, scan.moment_at(at + 1)?);
                prefix.aeon.cells = resident
                    .aeon
                    .cells
                    .checked_add((at + 1) as u64)
                    .ok_or(HnnError::CountOverflow)?;
                prefix.aeon.keys_admitted = false;
                prefix.aeon.awaiting = at + 1 == consumed && carry_out;
                prefixes.insert(at + 1, prefix);
            }
        }

        working.current = closing_current.clone();
        working.moments.insert(*moment, closing_source.clone());
        let opening = if carry_out {
            closing_current.lift()
        } else {
            &resident.aeon.opening
        };
        if !working
            .address
            .reader()
            .agrees(field, &closing_current, opening)
        {
            return Err(HnnError::Shape {
                what: "the address register's clock against the epoch's closing lift",
                expected: field.rings().len(),
                found: 0,
            });
        }

        Ok(EpochForward {
            prepared_input: working.prepared_input,
            commit,
            reads,
            prefixes,
            consumed,
            carry_out,
            carried: working.carried,
            charts: working.charts,
            wall: working.wall,
            tally: working.tally,
            current: closing_current,
            source: closing_source,
            address: working.address,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::field::Field;
    use crate::hnn::tests::learning::chain;
    use crate::holarchy::terrain::KnownTruth;

    fn encoded(field: &Field, classes: &[usize]) -> Encoded {
        Encoded::identity(
            &KnownTruth::declared(field.alphabet(), vec![classes.to_vec()]),
            field,
        )
        .unwrap()
        .remove(0)
    }

    fn single_phase_chain() -> Field {
        let mut declaration = chain().declaration().clone();
        declaration.receivers[0].aperture = 1;
        Field::declare(declaration).unwrap()
    }

    fn empty_moment(reference: &Reference, field: &Field) -> (Resident, MomentId, ReceivingPhases) {
        let mut resident = reference.mount(field, &Current::at_rest(field)).unwrap();
        let phases = resident.admitted()[0].clone();
        let (moment, _) = reference
            .ingest(&mut resident, None, &encoded(field, &[]))
            .unwrap();
        (resident, moment, phases)
    }

    fn assert_compact_probe_parity(
        full: &EpochForward,
        compact: &EpochForward<EpochProbeRead>,
    ) {
        assert_eq!(compact.commit, full.commit);
        assert_eq!(compact.consumed, full.consumed);
        assert_eq!(compact.carry_out, full.carry_out);
        assert_eq!(compact.current, full.current);
        assert_eq!(compact.source, full.source);
        assert_eq!(compact.address, full.address);
        assert_eq!(compact.carried, full.carried);
        assert_eq!(compact.charts, full.charts);
        assert_eq!(compact.tally, full.tally);
        assert_eq!(compact.reads.len(), full.reads.len());
        assert_eq!(compact.prefixes.len(), full.prefixes.len());
        for (got, expected) in compact.reads.iter().zip(&full.reads) {
            assert_eq!(got.ratio, expected.ratio);
            assert_eq!(got.faces, expected.faces);
        }
    }

    #[test]
    fn epoch_probe_compact_reads_match_native_and_selected_changed_source_forward() {
        use crate::hnn::constitution::Sample;
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (mut opening, moment, phases) = empty_moment(&reference, &field);
        // A genuinely carried opening: source counts, pair buffer, warm charts and physical
        // interior motion precede the new material and the candidate passage.
        for class in [0, 1, 2] {
            let (id, _) = reference.refine(&mut opening, &moment, &phases).unwrap();
            opening.pending.remove(&id).unwrap();
            reference
                .ingest(&mut opening, Some(&moment), &encoded(&field, &[class]))
                .unwrap();
        }
        assert!(opening.carried.is_some());
        let source = field.sources()[0];
        let old = opening.constitution.source_port(source).unwrap().clone();
        let unit = |width| {
            (0..width)
                .map(|at| integer(i64::from(at == 0)))
                .collect()
        };
        let sample = Sample {
            weight: Rat::one(),
            feature: unit(old.columns()),
            covector: unit(old.rows()),
            masses: None,
        };
        let (candidate, _) = opening
            .constitution
            .stepped_source(source, &[sample], &Rat::one(), &opening.retention())
            .unwrap()
            .unwrap();
        assert_ne!(candidate.source_port(source).unwrap(), &old);
        opening.constitution = candidate;
        let before = opening.continuing_state(0).unwrap().to_text();
        let cells = encoded(&field, &[0; 64]);
        let full = reference
            .read_epoch_at_cuts(&opening, &moment, &phases, &cells, &[])
            .unwrap();
        let compact = reference
            .read_epoch_probe_at_cuts(&opening, &moment, &phases, &cells, &[])
            .unwrap();
        assert_compact_probe_parity(&full, &compact);
        assert!(compact.carry_out);
        assert!(compact.consumed < cells.len());
        let execution = observed::HostObservedEpochExecution;
        let selected_full = reference
            .read_epoch_at_cuts_with_execution(
                &opening, &moment, &phases, &cells, &[], &execution,
            )
            .unwrap();
        let selected_compact = reference
            .read_epoch_probe_at_cuts_with_execution(
                &opening, &moment, &phases, &cells, &[], &execution,
            )
            .unwrap();
        assert_compact_probe_parity(&selected_full, &selected_compact);
        assert_eq!(selected_compact.current, compact.current);
        assert_eq!(selected_compact.carried, compact.carried);
        for (selected, native) in selected_compact.reads.iter().zip(&compact.reads) {
            assert_eq!(selected.ratio, native.ratio);
            assert_eq!(selected.faces, native.faces);
        }
        assert_eq!(opening.continuing_state(0).unwrap().to_text(), before);
    }

    struct FailSecondProbeForward(std::sync::atomic::AtomicUsize);

    impl observed::ObservedEpochExecution for FailSecondProbeForward {
        fn forward(
            &self,
            field: &Field,
            constitution: &Constitution,
            ratio: &PendingRatio,
            charts: &mut Charts,
            opening: &WordOpening,
        ) -> Result<observed::ObservedEpochForwardWord, HnnError> {
            if self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst) == 1 {
                return Err(HnnError::Realization {
                    what: "the selected candidate's second forward refused",
                });
            }
            observed::ObservedEpochExecution::forward(
                &observed::HostObservedEpochExecution,
                field, constitution, ratio, charts, opening,
            )
        }

        fn pull_back(
            &self,
            _: Word<'_>,
            _: &RatioCovector,
            _: &ExactRatMatrix,
            _: &ReceivingPhases,
        ) -> Result<WordReturn, HnnError> {
            panic!("a candidate forward never executes an unused return")
        }

        fn aggregate_records(
            &self,
            _: crate::hnn::constitution::LinearLocus,
            _: usize,
            _: usize,
            _: u32,
            _: u64,
            _: u64,
            _: u64,
            _: &[crate::hnn::constitution::EpochProducerRecordReading],
        ) -> Result<crate::hnn::constitution::EpochRecordFlowReading, HnnError> {
            panic!("a candidate forward never stages another deposit")
        }
    }

    #[test]
    fn epoch_probe_compact_refusals_match_full_forward_without_mutation_or_retry() {
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (opening, moment, phases) = empty_moment(&reference, &field);
        let cells = encoded(&field, &[0, 1, 2]);
        let before = opening.continuing_state(0).unwrap().to_text();
        for terminal in [false, true] {
            let mut refused = opening.clone();
            refused.observed_epoch_terminal = terminal;
            // A foreign moment reaches the same handle check unless an earlier terminal
            // refusal takes precedence. Compact retention cannot reorder either error.
            let unknown = MomentId(u64::MAX);
            let full = reference
                .read_epoch_at_cuts(&refused, &unknown, &phases, &cells, &[])
                .unwrap_err();
            let compact = reference
                .read_epoch_probe_at_cuts(&refused, &unknown, &phases, &cells, &[])
                .unwrap_err();
            assert_eq!(full.to_string(), compact.to_string());
        }
        let full_execution = FailSecondProbeForward(std::sync::atomic::AtomicUsize::new(0));
        let compact_execution = FailSecondProbeForward(std::sync::atomic::AtomicUsize::new(0));
        let full = reference
            .read_epoch_at_cuts_with_execution(
                &opening, &moment, &phases, &cells, &[], &full_execution,
            )
            .unwrap_err();
        let compact = reference
            .read_epoch_probe_at_cuts_with_execution(
                &opening, &moment, &phases, &cells, &[], &compact_execution,
            )
            .unwrap_err();
        assert!(matches!(full, HnnError::Realization { .. }));
        assert!(matches!(compact, HnnError::Realization { .. }));
        assert_eq!(full.to_string(), compact.to_string());
        assert_eq!(full_execution.0.load(std::sync::atomic::Ordering::SeqCst), 2);
        assert_eq!(compact_execution.0.load(std::sync::atomic::Ordering::SeqCst), 2);
        assert_eq!(opening.continuing_state(0).unwrap().to_text(), before);
    }

    #[test]
    fn scoped_refine_binds_the_whole_call_to_its_producer_even_with_a_different_working_clone() {
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (opening, moment, phases) = empty_moment(&reference, &field);
        let mut oracle = opening.clone();
        let (oracle_id, expected) = reference.refine(&mut oracle, &moment, &phases).unwrap();
        let ReceiptDetail::Refine {
            reached: expected_reached,
            ..
        } = &expected.receipt.detail
        else {
            panic!("a refine receipt");
        };
        let released = *expected_reached
            .first()
            .expect("this word reaches material");
        let mut working = opening.clone();
        working
            .constitution
            .release(&BTreeSet::from([released]))
            .unwrap();
        assert!(working.constitution.released().contains(&released));
        assert!(!opening.constitution.released().contains(&released));
        let mut rings = crate::hnn::propagation::RingScope::new(&field, &opening.constitution);
        let (id, actual) = reference
            .refine_view_scoped(
                &mut working,
                &moment,
                &phases,
                &crate::hnn::ring::modes::ModeView::whole(),
                Some(&mut rings),
            )
            .unwrap();
        assert_eq!(actual.forward, expected.forward);
        let ReceiptDetail::Refine { reached, .. } = &actual.receipt.detail else {
            panic!("a refine receipt");
        };
        assert_eq!(
            reached, expected_reached,
            "the filter reads the producing constitution"
        );
        let actual = &working.pending[&id];
        let expected = &oracle.pending[&oracle_id];
        assert_eq!(actual.ratio, expected.ratio);
        assert_eq!(
            actual.kept.as_ref().unwrap().commit,
            opening.constitution.commit()
        );
        actual
            .kept
            .as_ref()
            .unwrap()
            .word
            .operands()
            .assert_same_execution(expected.kept.as_ref().unwrap().word.operands());
    }

    #[test]
    fn carried_epoch_forward_matches_sequential_refine_and_ingest_without_deposits() {
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (opening, moment, phases) = empty_moment(&reference, &field);
        let cells = encoded(&field, &[0, 1, 2, 3, 1, 0, 2, 1, 3, 0, 1, 2]);
        let forward = reference
            .read_epoch(&opening, &moment, &phases, &cells)
            .unwrap();
        assert_eq!(forward.commit, opening.constitution.commit());
        assert_eq!(forward.consumed, forward.reads.len());

        let mut oracle = opening.clone();
        let mut oracle_carry_out = false;
        for (at, read) in forward.reads.iter().enumerate() {
            let (id, result) = reference.refine(&mut oracle, &moment, &phases).unwrap();
            let returned_faces = result.forward.into_present().unwrap();
            assert_eq!(returned_faces, read.faces, "faces at cell {at}");
            let slot = oracle.pending.get(&id).unwrap();
            assert_eq!(slot.ratio, read.ratio, "producing ratio at cell {at}");
            assert_eq!(slot.opening, read.opening, "word opening at cell {at}");
            let kept = slot.kept.as_ref().unwrap();
            read.word
                .operands()
                .assert_same_execution(kept.word.operands());
            for ring in read.word.operands().rings() {
                if let Some(chart) = ring.chart() {
                    assert_eq!(chart.start == ChartStart::Reused, at != 0);
                    if at != 0 {
                        assert_eq!(chart.steps, 0);
                    }
                }
            }
            assert_eq!(kept.faces, read.faces, "kept faces at cell {at}");
            assert_eq!(kept.commit, read.commit, "kept commit at cell {at}");
            assert_eq!(read.commit, forward.commit, "fixed material at cell {at}");
            for tick in 0..phases.junction_steps() {
                for ring in 0..field.rings().len() {
                    assert_eq!(
                        read.word.anchor(tick, ring),
                        kept.word.anchor(tick, ring),
                        "kept anchor at cell {at}, tick {tick}, ring {ring}",
                    );
                }
            }

            let one_cell = cells.part(at..at + 1).unwrap();
            let (_, ingested) = reference
                .ingest(&mut oracle, Some(&moment), &one_cell)
                .unwrap();
            oracle_carry_out = ingested.forward.present().unwrap().carry_out;
        }

        assert_eq!(forward.carry_out, oracle_carry_out);
        assert_eq!(forward.current, oracle.current);
        assert_eq!(forward.source, *oracle.moments.get(&moment).unwrap());
        assert_eq!(forward.address, oracle.address);
        assert_eq!(forward.carried, oracle.carried);
        assert_eq!(forward.charts, oracle.charts);
        assert_eq!(forward.tally, oracle.tally);
    }

    #[test]
    fn warm_carried_forward_stops_at_the_actual_joint_carry() {
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (mut opening, moment, phases) = empty_moment(&reference, &field);
        // Reach a genuine continuing opening: source counts, pair buffer, warm charts and the
        // preceding word's reception end all predate the candidate batch.
        for class in [0, 1, 2] {
            let (id, _) = reference.refine(&mut opening, &moment, &phases).unwrap();
            opening.pending.remove(&id).unwrap();
            reference
                .ingest(&mut opening, Some(&moment), &encoded(&field, &[class]))
                .unwrap();
        }
        assert!(opening.carried.is_some());
        let cells = encoded(&field, &[0; 64]);
        let forward = reference
            .read_epoch(&opening, &moment, &phases, &cells)
            .unwrap();
        assert!(forward.carry_out);
        assert!(forward.consumed < cells.len());
        let mut oracle = opening.clone();
        for (at, read) in forward.reads.into_iter().enumerate() {
            let (id, result) = reference.refine(&mut oracle, &moment, &phases).unwrap();
            assert_eq!(
                result.forward.into_present().unwrap(),
                read.faces,
                "cell {at}"
            );
            let slot = oracle.pending.remove(&id).unwrap();
            assert_eq!(slot.opening, read.opening, "carried opening at cell {at}");
            assert_eq!(slot.ratio, read.ratio, "source/address at cell {at}");
            let kept = slot.kept.unwrap();
            assert_eq!(kept.commit, forward.commit);
            let actual_word = read.word.resume(&field);
            let oracle_word = kept.word.resume(&field);
            actual_word
                .operands()
                .assert_same_execution(oracle_word.operands());
            let mut actual_release = actual_word.released().unwrap();
            let oracle_release = oracle_word.released().unwrap();
            for (actual, expected) in actual_release.charts.iter_mut().zip(&oracle_release.charts) {
                if actual.start == ChartStart::Reused {
                    assert_eq!(actual.steps, 0);
                    actual.start = expected.start;
                    actual.steps = expected.steps;
                    if let (Some(op), Some(expected_op)) =
                        (&mut actual.operator, &expected.operator)
                    {
                        op.wide_reasons = expected_op.wide_reasons.clone();
                    }
                }
            }
            assert_eq!(
                actual_release, oracle_release,
                "whole word release at cell {at}"
            );
            let (_, ingested) = reference
                .ingest(&mut oracle, Some(&moment), &cells.part(at..at + 1).unwrap())
                .unwrap();
            assert_eq!(
                ingested.forward.present().unwrap().carry_out,
                at + 1 == forward.consumed
            );
        }
        assert_eq!(forward.current, oracle.current);
        assert_eq!(forward.source, *oracle.moments.get(&moment).unwrap());
        assert_eq!(forward.address, oracle.address);
        assert_eq!(forward.carried, oracle.carried);
        assert_eq!(forward.charts, oracle.charts);
        assert_eq!(forward.tally, oracle.tally);
        assert_eq!(opening.constitution.commit(), forward.commit);
        assert!(!opening.aeon.awaiting);
    }

    #[test]
    fn rest_and_invalid_epoch_inputs_refuse_without_changing_the_resident() {
        let field = single_phase_chain();
        let resident_reference = Reference::new(16, 1 << 40);
        let (resident, moment, phases) = empty_moment(&resident_reference, &field);
        let before_current = resident.current.clone();
        let before_address = resident.address.clone();
        let before_moments = resident.moments.clone();
        let before_charts = resident.charts.clone();
        let before_carried = resident.carried.clone();
        let cells = encoded(&field, &[0, 1, 0]);
        let empty = resident_reference
            .read_epoch(&resident, &moment, &phases, &encoded(&field, &[]))
            .unwrap();
        assert_eq!(empty.consumed, 0);
        assert!(empty.reads.is_empty());
        assert_eq!(empty.charts, before_charts);
        assert_eq!(empty.tally, resident.tally);

        let rest = Reference::new(16, 1 << 40).with_reception(Reception::Rest);
        assert!(
            rest.read_epoch(&resident, &moment, &phases, &cells)
                .is_err()
        );
        assert_eq!(resident.current, before_current);
        assert_eq!(resident.address, before_address);
        assert_eq!(resident.moments, before_moments);
        assert_eq!(resident.charts, before_charts);
        assert_eq!(resident.carried, before_carried);

        let mut wrong_declaration = field.declaration().clone();
        // A smaller alphabet alone remains admissible. Encode against a genuinely different
        // source ring, with classes that still fit that source's port chart.
        wrong_declaration.alphabet = 2;
        wrong_declaration.sources = vec![1];
        let wrong_field = Field::declare(wrong_declaration.by_lattice_rule()).unwrap();
        let wrong_cells = encoded(&wrong_field, &[0, 1]);
        assert!(
            resident_reference
                .read_epoch(&resident, &moment, &phases, &wrong_cells)
                .is_err()
        );
        assert_eq!(resident.current, before_current);
        assert_eq!(resident.address, before_address);
        assert_eq!(resident.moments, before_moments);
        assert_eq!(resident.charts, before_charts);
        assert_eq!(resident.carried, before_carried);
    }
}
