//! A stream boundary for the native atomic observed-epoch owner.
//!
//! A committed resident and its finite closing crib are retained. Only the current unfinished
//! physical interval's boundary classes wait beside that opening. At its actual receiving tick,
//! the grouped owner consumes them once and the completed input batch is discarded. This is an
//! unpublished transaction, never a history of published updates or a source replay model.
//!
//! [agent-inferred] On the admitted Lock route, ring zero fits every boundary class and advances
//! once per cell. A receiving ring r must therefore tick within H = product(g < r) d_g cells;
//! other fitting locks can only make that arrival earlier. An unfinished batch has fewer than H
//! classes. Routes without this finite bound refuse, rather than accepting an unbounded queue.
//! This owner touches helix/carry, receiving placement and the compatible continuing thread;
//! paired contacts, holonomy and the tube remain attached through the actual epoch owner.

use super::*;

#[derive(Clone, Debug)]
pub struct ObservedStream {
    resident: Resident,
    crib: ObservedCrib,
    scope: ObservedEpochDepositionScope,
    pending: Vec<usize>,
    bound: usize,
}

/// Exterior evidence for this delivery, never retained by the stream.
#[derive(Debug)]
pub struct ObservedStreamReceipt {
    /// New boundary classes accepted by this call, including its unfinished interval.
    pub accepted: usize,
    /// Classes actually published in this call, including a preceding pending fragment.
    pub published: usize,
    pub pending: usize,
    pub epochs: Vec<ObservedEpochReceipt>,
}

fn refuse(what: &'static str) -> HnnError {
    HnnError::ContinuingState { what }
}

impl ObservedStream {
    pub fn new(
        resident: Resident,
        crib: ObservedCrib,
        scope: ObservedEpochDepositionScope,
    ) -> Result<Self, HnnError> {
        Self::restore(resident, crib, scope, Vec::new())
    }

    fn finite_bound(resident: &Resident) -> Result<usize, HnnError> {
        resident.admit_exact_current()?;
        if resident.observed_epoch_terminal
            || resident.moments.len() != 1
            || !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.aeon.awaiting
        {
            return Err(refuse(
                "a bounded observed stream needs one continuing moment at an ordinary committed native opening",
            ));
        }
        resident.field.admit_lock_route()?;
        let [phases] = resident.admitted.as_slice() else {
            return Err(refuse("one receiving section bounds an observed stream"));
        };
        if phases.aperture() != 1
            || !resident.field.sources().contains(&0)
            || (0..resident.field.alphabet()).any(|class| {
                !resident
                    .field
                    .ring(0)
                    .fits(resident.field.ring(0).port(class))
            })
        {
            return Err(refuse(
                "a bounded observed stream needs an aperture-one receiver and an always-ticking first source ring",
            ));
        }
        resident.field.rings()[..phases.ring()]
            .iter()
            .try_fold(1usize, |product, ring| {
                product
                    .checked_mul(
                        usize::try_from(ring.period()).map_err(|_| HnnError::CountOverflow)?,
                    )
                    .ok_or(HnnError::CountOverflow)
            })
    }

    /// Validate a saved current transaction against the restored native opening. Complete
    /// sections cannot appear here: they must already have been consumed and dropped.
    pub fn restore(
        resident: Resident,
        crib: ObservedCrib,
        scope: ObservedEpochDepositionScope,
        pending: Vec<usize>,
    ) -> Result<Self, HnnError> {
        let bound = Self::finite_bound(&resident)?;
        let published = resident
            .moments
            .values()
            .next()
            .map_or(0, SourceMoment::cells);
        if crib.next_position()
            != usize::try_from(published).map_err(|_| HnnError::CountOverflow)?
            || pending.len() >= bound
            || published
                .checked_add(u64::try_from(pending.len()).map_err(|_| HnnError::CountOverflow)?)
                .ok_or(HnnError::CountOverflow)?
                > resident.field.population()
        {
            return Err(refuse(
                "the observed stream's finite transaction against its native opening and horizon",
            ));
        }
        ObservedCrib::from_unplaced_checkpoint(
            &resident.field,
            &resident.current,
            crib.next_position(),
            &crib.unplaced_checkpoint()?,
        )?;
        let stream = Self {
            resident,
            crib,
            scope,
            pending,
            bound,
        };
        // Clock validation does not need a newly authored pairing: use the native selective
        // law in-crate and admit the actual producing codec when a delivery or view consumes it.
        let mut lift = stream.resident.current.lift().to_vec();
        let receiver = stream.resident.admitted[0].ring();
        for &class in &stream.pending {
            let step = stream.resident.field.step_class(&mut lift, class, None)?;
            if step.ticks[receiver] != 0 || step.carry_out {
                return Err(refuse(
                    "a saved pending interval already crossed its actual receiving section",
                ));
            }
        }
        Ok(stream)
    }

    pub fn resident(&self) -> &Resident {
        &self.resident
    }
    pub fn crib(&self) -> &ObservedCrib {
        &self.crib
    }
    pub fn pending_classes(&self) -> &[usize] {
        &self.pending
    }
    pub fn epoch_bound(&self) -> usize {
        self.bound
    }
    pub fn scope(&self) -> ObservedEpochDepositionScope {
        self.scope
    }
    pub fn accepted_cells(&self) -> Result<u64, HnnError> {
        self.resident
            .moments
            .values()
            .next()
            .map_or(0, SourceMoment::cells)
            .checked_add(u64::try_from(self.pending.len()).map_err(|_| HnnError::CountOverflow)?)
            .ok_or(HnnError::CountOverflow)
    }

    fn pending_frontier(&self, pairing: &PairingDeclaration) -> Result<Current, HnnError> {
        let boundary =
            PairedObservation::admit(&self.resident.field, &self.resident.constitution, pairing)?;
        let encoded = boundary.encode(&self.pending)?;
        let mut frontier = self.resident.current.clone();
        let receiver = self.resident.admitted[0].ring();
        for at in 0..encoded.len() {
            let step = frontier.step(&self.resident.field, &encoded, at)?;
            if step.ticks[receiver] != 0 || step.carry_out {
                return Err(refuse(
                    "the unfinished observed interval crossed its receiving section",
                ));
            }
        }
        Ok(frontier)
    }

    /// Accept source classes transactionally. Only actual receiving ticks publish the native
    /// grouped comparison; no end-of-source flush or artificial terminal clock is introduced.
    pub fn receive(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        classes: &[usize],
    ) -> Result<ObservedStreamReceipt, HnnError> {
        let mut next = self.clone();
        if next
            .accepted_cells()?
            .checked_add(u64::try_from(classes.len()).map_err(|_| HnnError::CountOverflow)?)
            .ok_or(HnnError::CountOverflow)?
            > next.resident.field.population()
        {
            return Err(refuse(
                "the observed stream delivery exceeds its declared source horizon",
            ));
        }
        let mut frontier = next.pending_frontier(pairing)?;
        let mut boundary =
            PairedObservation::admit(&next.resident.field, &next.resident.constitution, pairing)?;
        let mut receiver = next.resident.admitted[0].ring();
        let mut epochs = Vec::new();
        let mut published = 0;
        for &class in classes {
            let encoded = boundary.encode(&[class])?;
            let step = frontier.step(&next.resident.field, &encoded, 0)?;
            next.pending.push(class);
            if next.pending.len() > next.bound {
                return Err(refuse(
                    "the physical receiving bound did not close the observed interval",
                ));
            }
            if step.ticks[receiver] != 0 || step.carry_out {
                let receipt = reference.observe_epoch_continuing_at_cuts_with_scope(
                    &mut next.resident,
                    &mut next.crib,
                    pairing,
                    &next.pending,
                    None,
                    &[],
                    false,
                    &HostObservedEpochExecution,
                    next.scope,
                )?;
                if receipt.consumed != next.pending.len() || receipt.terminal_partial {
                    return Err(refuse(
                        "the grouped owner did not consume exactly the actual unfinished interval",
                    ));
                }
                published += receipt.consumed;
                epochs.push(receipt);
                next.pending.clear();
                next.bound = Self::finite_bound(&next.resident)?;
                receiver = next.resident.admitted[0].ring();
                frontier = next.resident.current.clone();
                boundary = PairedObservation::admit(
                    &next.resident.field,
                    &next.resident.constitution,
                    pairing,
                )?;
            }
        }
        let receipt = ObservedStreamReceipt {
            accepted: classes.len(),
            published,
            pending: next.pending.len(),
            epochs,
        };
        *self = next;
        Ok(receipt)
    }

    /// Private query fork of the actual unfinished native word chain. The existing epoch
    /// forward owner advances its source moment, current, address, carried interior and charts
    /// once through this current fragment. No comparison or deposition is performed; the
    /// committed stream is untouched and no completed source interval is replayed.
    pub fn query_fork(
        &self,
        reference: &Reference,
        pairing: &PairingDeclaration,
    ) -> Result<(Resident, ObservedCrib), HnnError> {
        let frontier = self.pending_frontier(pairing)?;
        if self.pending.is_empty() {
            return Ok((self.resident.clone(), self.crib.clone()));
        }
        let boundary =
            PairedObservation::admit(&self.resident.field, &self.resident.constitution, pairing)?;
        let encoded = boundary.encode(&self.pending)?;
        let moment = *self
            .resident
            .moments
            .keys()
            .next()
            .ok_or_else(|| refuse("the query fork's one continuing moment"))?;
        let mut forward = reference.read_epoch_at_cuts(
            &self.resident,
            &moment,
            &self.resident.admitted[0],
            &encoded,
            &[self.pending.len()],
        )?;
        if forward.consumed != self.pending.len() || forward.carry_out {
            return Err(refuse("the query fork's unfinished native prefix"));
        }
        let resident = forward
            .prefixes
            .remove(&self.pending.len())
            .ok_or_else(|| refuse("the actual unfinished native prefix was not returned"))?;
        // The words are transient operands of this current transaction, never part of a save.
        drop(forward);
        if resident.current != frontier || resident.constitution != self.resident.constitution {
            return Err(refuse(
                "the query prefix must retain contemporary material and its actual frontier",
            ));
        }
        let mut crib = self.crib.clone();
        let mut current = self.resident.current.clone();
        for (at, &class) in self.pending.iter().enumerate() {
            let before = current.clone();
            current.step(&self.resident.field, &encoded, at)?;
            crib.push(
                &self.resident.field,
                &before,
                class,
                None,
                self.resident.field.crib().window,
            )?;
        }
        Ok((resident, crib))
    }

    /// Only the bounded unfinished boundary transaction is serialized here. Native material,
    /// passage and the closing crib retain their existing owners and checkpoint codecs.
    pub fn pending_checkpoint(&self) -> String {
        let scope = match self.scope {
            ObservedEpochDepositionScope::All => "all",
            ObservedEpochDepositionScope::NormalMaps => "normal-maps",
        };
        format!(
            "observed-stream-pending-v1 {scope} {} {} {}\n{}\n",
            self.resident.constitution.commit(),
            self.crib.next_position(),
            self.pending.len(),
            self.pending
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn restore_checkpoint(
        resident: Resident,
        crib: ObservedCrib,
        text: &str,
    ) -> Result<Self, HnnError> {
        let bound = Self::finite_bound(&resident)?;
        let mut lines = text.lines();
        let header: Vec<_> = lines
            .next()
            .ok_or_else(|| refuse("the unfinished observed transaction header"))?
            .split_whitespace()
            .collect();
        if header.len() != 5 || header[0] != "observed-stream-pending-v1" {
            return Err(refuse("the unfinished observed transaction version"));
        }
        let scope = match header[1] {
            "all" => ObservedEpochDepositionScope::All,
            "normal-maps" => ObservedEpochDepositionScope::NormalMaps,
            _ => return Err(refuse("the saved observed deposition scope")),
        };
        let commit: u64 = header[2]
            .parse()
            .map_err(|_| refuse("the unfinished transaction commit"))?;
        let published: usize = header[3]
            .parse()
            .map_err(|_| refuse("the unfinished transaction opening"))?;
        let count: usize = header[4]
            .parse()
            .map_err(|_| refuse("the unfinished transaction count"))?;
        if commit != resident.constitution.commit()
            || published != crib.next_position()
            || count >= bound
        {
            return Err(refuse(
                "the unfinished transaction against its native opening and physical bound",
            ));
        }
        let mut pending = Vec::new();
        for value in lines
            .next()
            .ok_or_else(|| refuse("the unfinished transaction classes"))?
            .split_whitespace()
        {
            if pending.len() == count {
                return Err(refuse("the unfinished transaction class count"));
            }
            pending.push(
                value
                    .parse()
                    .map_err(|_| refuse("an unfinished transaction class"))?,
            );
        }
        if pending.len() != count || lines.next().is_some() {
            return Err(refuse("the unfinished transaction class count"));
        }
        Self::restore(resident, crib, scope, pending)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::tests::support::{contact, small_field_of};

    fn opening() -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
        // The existing serial small-field declaration, with the always-ticking first source
        // and the grouped phase owner's smallest odd receiving period.
        let base = small_field_of(
            &[5, 2, 3],
            vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
            2,
            4,
        );
        let mut declaration = base.declaration().clone();
        declaration.rings[0].lock = (0..4).collect();
        for ring in &mut declaration.rings[1..] {
            ring.lock.clear();
        }
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..4).map(|class| (class, class ^ 1)).collect(),
        };
        let material = PairedCarrier::found(
            &field,
            Constitution::initial(&field, 1 << 40).unwrap(),
            0,
            &pairing,
        )
        .unwrap()
        .0;
        let reference = Reference::new(16, 1 << 40);
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), material.clone())
            .unwrap();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let stream = ObservedStream::new(
            resident,
            ObservedCrib::new(0),
            ObservedEpochDepositionScope::NormalMaps,
        )
        .unwrap();
        (reference, stream, pairing, material)
    }

    #[test]
    fn unfinished_native_interval_roundtrips_and_closes_at_the_actual_receiving_tick() {
        let (reference, mut stream, pairing, opening) = opening();
        let before = stream.resident.continuing_state(0).unwrap();
        let partial = stream
            .receive(&reference, &pairing, &[0, 1, 2, 3, 0, 1, 2])
            .unwrap();
        assert_eq!(
            (partial.accepted, partial.published, partial.pending),
            (7, 0, 7)
        );
        assert!(partial.epochs.is_empty());
        assert_eq!(stream.epoch_bound(), 10);
        assert_eq!(stream.resident.continuing_state(0).unwrap(), before);
        let pending_text = stream.pending_checkpoint();
        let parsed = ContinuingState::from_text(&before.to_text(), 1 << 40).unwrap();
        let field = stream.resident.field.clone();
        let cold_resident = reference
            .mount_continued(&field, &Current::at_rest(&field), opening, &parsed)
            .unwrap();
        let cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold_resident.current(),
            0,
            &stream.crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        let mut cold =
            ObservedStream::restore_checkpoint(cold_resident, cold_crib, &pending_text).unwrap();
        assert_eq!(cold.pending_checkpoint(), pending_text);
        let (warm_view, _) = stream.query_fork(&reference, &pairing).unwrap();
        let (cold_view, _) = cold.query_fork(&reference, &pairing).unwrap();
        assert_eq!(
            warm_view.continuing_state(0).unwrap(),
            cold_view.continuing_state(0).unwrap()
        );
        assert_eq!(warm_view.moments.values().next().unwrap().cells(), 7);
        assert!(
            warm_view.carried.is_some(),
            "the unfinished word chain's physical interior reaches the query"
        );
        assert_eq!(
            stream.resident.carried, None,
            "the committed opening remains untouched"
        );
        let warm_receipt = stream.receive(&reference, &pairing, &[3, 0, 1]).unwrap();
        let cold_receipt = cold.receive(&reference, &pairing, &[3, 0, 1]).unwrap();
        assert_eq!(
            (
                warm_receipt.accepted,
                warm_receipt.published,
                warm_receipt.pending
            ),
            (3, 10, 0)
        );
        assert_eq!(warm_receipt.epochs.len(), 1);
        assert!(warm_receipt.epochs[0].closed_section);
        assert!(!warm_receipt.epochs[0].terminal_partial);
        assert_eq!(
            warm_receipt.epochs[0].outcome,
            cold_receipt.epochs[0].outcome
        );
        assert_eq!(
            stream.resident.continuing_state(0).unwrap(),
            cold.resident.continuing_state(0).unwrap()
        );
        assert_eq!(stream.pending_checkpoint(), cold.pending_checkpoint());
        assert_eq!(stream.accepted_cells().unwrap(), 10);
    }

    #[test]
    fn unfinished_stream_rejects_completed_or_mismatched_saved_transactions_and_rolls_back_refused_delivery()
     {
        let (reference, mut stream, pairing, _) = opening();
        let saved = stream.pending_checkpoint();
        let malformed = format!(
            "observed-stream-pending-v1 normal-maps {} 0 10\n0 0 0 0 0 0 0 0 0 0\n",
            stream.resident.constitution.commit()
        );
        assert!(
            ObservedStream::restore_checkpoint(
                stream.resident.clone(),
                stream.crib.clone(),
                &malformed
            )
            .is_err()
        );
        assert!(
            ObservedStream::restore_checkpoint(
                stream.resident.clone(),
                stream.crib.clone(),
                &saved.replace("normal-maps", "other")
            )
            .is_err()
        );
        let before = stream.resident.continuing_state(0).unwrap();
        let mut missing = stream.resident.clone();
        missing.moments.clear();
        assert!(ObservedStream::new(missing, stream.crib.clone(), stream.scope).is_err());
        assert!(stream.receive(&reference, &pairing, &[0, 1, 4]).is_err());
        assert_eq!(stream.pending_checkpoint(), saved);
        assert_eq!(stream.resident.continuing_state(0).unwrap(), before);
    }
}
