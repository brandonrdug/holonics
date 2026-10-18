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
    pub(crate) ratio: PendingRatio,
    pub(crate) word: KeptWord,
    pub(crate) opening: WordOpening,
    pub(crate) faces: Faces,
    pub(crate) commit: u64,
}

/// A tape-free epoch forward result. `reads` is the transient return operand for this one epoch;
/// `source`, `current` and `address` are the exact closing values after the consumed prefix.
#[derive(Debug)]
pub(crate) struct EpochForward {
    pub(crate) reads: Vec<EpochRead>,
    pub(crate) consumed: usize,
    pub(crate) carry_out: bool,
    pub(crate) carried: Option<ReceptionCarry>,
    pub(crate) charts: Charts,
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

        let mut working = resident.clone();
        let mut reads = Vec::with_capacity(consumed);
        for at in 0..consumed {
            working.current = scan.current_at(field, at)?;
            working.moments.insert(*moment, scan.moment_at(at)?);

            let (id, _) = self.refine_view(
                &mut working,
                moment,
                phases,
                &crate::hnn::ring::modes::ModeView::whole(),
            )?;
            let slot = working
                .pending
                .remove(&id)
                .expect("the refine just inserted its pending slot");
            let kept = slot.kept.ok_or(HnnError::Unadmitted {
                reason: "an epoch forward retains the word from its own successful read",
            })?;
            reads.push(EpochRead {
                ratio: slot.ratio,
                word: kept.word,
                opening: slot.opening,
                faces: kept.faces,
                commit: kept.commit,
            });

            let class = cells.cells()[at].class();
            working.address.receive_at(class, cells.advance(at))?;
            working.address.refresh(field, &working.constitution)?;
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
            reads,
            consumed,
            carry_out,
            carried: working.carried,
            charts: working.charts,
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

    #[test]
    fn carried_epoch_forward_matches_sequential_refine_and_ingest_without_deposits() {
        let field = single_phase_chain();
        let reference = Reference::new(16, 1 << 40);
        let (opening, moment, phases) = empty_moment(&reference, &field);
        let cells = encoded(&field, &[0, 1, 2, 3, 1, 0, 2, 1, 3, 0, 1, 2]);
        let forward = reference
            .read_epoch(&opening, &moment, &phases, &cells)
            .unwrap();
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
            assert_eq!(kept.faces, read.faces, "kept faces at cell {at}");
            assert_eq!(kept.commit, read.commit, "kept commit at cell {at}");

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
        let wrong_field = Field::declare(wrong_declaration).unwrap();
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
