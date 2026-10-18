//! Host-only, aperture-one observed continuation through the existing execution port.
//!
//! The helical pair interaction keeps its helix, pair, faces and occurrence placement;
//! cell holonomy, tube and tower laws are unchanged. Comparison reads E_Θ(u,x), then
//! ingestion reads E_Θ′(u,x). The caller, never the resident, holds the finite crib.

use super::*;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::encoding::placement::OccurrencePlacement;
use crate::hnn::paired::PairingDeclaration;

/// A delivered cell eligible for the next closing crib, outside the resident.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedCribCell {
    pub position: usize,
    pub class: usize,
    pub placement: Option<OccurrencePlacement>,
}

/// Caller-owned finite crib of the current aeon.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedCrib {
    opening: usize,
    next: usize,
    opening_lift: Option<Vec<BigInt>>,
    entries: Vec<ObservedCribCell>,
}

impl ObservedCrib {
    pub fn new(opening: usize) -> Self {
        Self {
            opening,
            next: opening,
            opening_lift: None,
            entries: Vec::new(),
        }
    }
    pub fn opening(&self) -> usize {
        self.opening
    }
    pub fn next_position(&self) -> usize {
        self.next
    }
    pub fn entries(&self) -> &[ObservedCribCell] {
        &self.entries
    }

    fn push(
        &mut self,
        field: &Field,
        before: &Current,
        class: usize,
        placement: Option<&OccurrencePlacement>,
        window: usize,
    ) -> Result<(), HnnError> {
        if self.opening_lift.is_none() {
            self.opening_lift = Some(before.lift().to_vec());
        }
        let position = self.next;
        self.next = self.next.checked_add(1).ok_or(HnnError::CountOverflow)?;
        self.entries.push(ObservedCribCell {
            position,
            class,
            placement: placement.cloned(),
        });
        let keep = self.next.saturating_sub(window);
        let drop = self.entries.partition_point(|entry| entry.position < keep);
        if drop > 0 {
            let lift = self
                .opening_lift
                .as_ref()
                .expect("nonempty crib has opening lift");
            let opening = Current::at(field, lift.clone())?;
            let passed: Vec<_> = self.entries[..drop]
                .iter()
                .map(|entry| (entry.class, entry.placement.clone()))
                .collect();
            let placed = OccurrencePlacement::observed_crib(field, &opening, &passed)?;
            self.opening_lift = Some(
                placed
                    .arrivals()
                    .last()
                    .cloned()
                    .expect("evicted cells have an arrival"),
            );
            self.entries.drain(..drop);
        }
        Ok(())
    }

    fn closing(
        &self,
        field: &Field,
        boundary: &PairedObservation,
        window: usize,
    ) -> Result<Encoded, HnnError> {
        let span = closing_crib(self.opening, self.next, window, &[]);
        let entries: Vec<_> = self
            .entries
            .iter()
            .filter(|entry| span.contains(&entry.position))
            .collect();
        let classes: Vec<_> = entries.iter().map(|entry| entry.class).collect();
        if entries.iter().all(|entry| entry.placement.is_none()) {
            return Ok(boundary.encode(&classes)?);
        }
        let lift = self.opening_lift.as_ref().ok_or(HnnError::Unadmitted {
            reason: "the observed crib has no opening lift",
        })?;
        let opening = Current::at(field, lift.clone())?;
        let cells: Vec<_> = entries
            .iter()
            .map(|entry| (entry.class, entry.placement.clone()))
            .collect();
        let placement = OccurrencePlacement::observed_crib(field, &opening, &cells)?;
        Ok(boundary.encode_placed(&classes, &placement)?)
    }

    fn reopen(&mut self) {
        self.opening = self.next;
        self.opening_lift = None;
        self.entries.clear();
    }
}

/// The exact return from a delivered or drawn one-class ingest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IngestClassReceipt {
    pub cells: u64,
    pub ingest: PortReceipt,
    pub close: Option<ClosedLocated>,
}

/// Exterior evidence for the post-deposit receiving-publication interval.
/// The resident retains none of these receipts. A checked interval with no event is a complete
/// natural outcome; no authored precision level is selected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedPrecisionReceipt {
    pub checked: bool,
    /// Only this comparison's actual Receiving(ring) sample features, never covectors/targets.
    pub features: Vec<Vec<Rat>>,
    pub event: Option<ReceivingPrecision>,
    pub before_commit: u64,
    pub after_commit: u64,
    pub before_exponent: u32,
    pub after_exponent: u32,
    /// Captured before ingest/close can reset the local aeon's counters.
    pub balance_before: crate::aeon::EnclosedBalance,
    pub balance_after: crate::aeon::EnclosedBalance,
}

/// Exterior receipt for one delivered cell. The resident retains no receipt history.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedCellReceipt<T = ()> {
    pub cells: u64,
    pub comparison_commit: u64,
    pub ingestion_commit: u64,
    /// Actual sealed blind faces, read without consulting this observation.
    pub prediction: Faces,
    pub refine: PortReceipt,
    pub compare: PortReceipt,
    pub deposit: PortReceipt,
    pub precision: ObservedPrecisionReceipt,
    pub ingest: PortReceipt,
    pub close: Option<ClosedLocated>,
    /// The observer's post-deposit view, released only after the cell commits.
    pub view: T,
}

/// The declared source-operand horizon, shared by the pre-comparison admission
/// and the ingest step so a refused cell is not compared or observed first.
fn admit_observed_horizon(resident: &Resident) -> Result<(), HnnError> {
    let field = &resident.field;
    let ring = *field.sources().first().ok_or(HnnError::Unadmitted {
        reason: "the observed continuation needs a source port",
    })?;
    let source_operand_bound = field
        .source_operand_bound(Locus::SourcePort(ring))
        .ok_or(HnnError::MissingSourcePort { ring })?;
    let received = resident
        .moments
        .values()
        .next()
        .map_or(0, SourceMoment::cells);
    if received >= field.population() {
        return Err(HnnError::Horizon {
            population: field.population(),
            source_operand_bound,
        });
    }
    Ok(())
}

/// Admission shared by the pre-refine observed path and the contemporary ingest.
/// None of these refusals needs the later comparison, deposit or ingested state.
fn admit_observed_cell(
    resident: &Resident,
    crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    class: usize,
    placement: Option<&OccurrencePlacement>,
) -> Result<(PairedObservation, Encoded), HnnError> {
    resident.admit_exact_current()?;
    if resident.moments.len() > 1 {
        return Err(HnnError::Unadmitted {
            reason: "observed continuation requires at most one moment",
        });
    }
    admit_observed_horizon(resident)?;
    let received = resident
        .moments
        .values()
        .next()
        .map_or(0, SourceMoment::cells);
    let expected = usize::try_from(received).map_err(|_| HnnError::CountOverflow)?;
    if crib.next != expected {
        return Err(HnnError::Shape {
            what: "the observed crib's position against the continuing moment",
            expected,
            found: crib.next,
        });
    }
    if resident.aeon.awaiting {
        return Err(HnnError::AeonAwaitingClose);
    }
    let boundary = PairedObservation::admit(&resident.field, &resident.constitution, pairing)?;
    let target = match placement {
        Some(placement) => boundary.encode_placed(&[class], placement)?,
        None => boundary.encode(&[class])?,
    };
    resident.field.capacity_for(&target)?;
    Ok((boundary, target))
}

impl Reference {
    /// Ingest one class at contemporary material and close with location at carry-out.
    /// This public wrapper leaves both the resident and caller's crib unchanged on refusal.
    pub fn ingest_class_continuing(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        class: usize,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<IngestClassReceipt, HnnError> {
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        let reading =
            self.ingest_class_step(&mut next, &mut next_crib, pairing, class, placement)?;
        *resident = next;
        *crib = next_crib;
        Ok(reading)
    }

    /// The one ingest, population and close step used by both public paths.
    fn ingest_class_step(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        class: usize,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<IngestClassReceipt, HnnError> {
        let (boundary, encoded) = admit_observed_cell(resident, crib, pairing, class, placement)?;
        let field = resident.field.clone();
        let moment = match resident.moments.keys().next().copied() {
            Some(moment) => moment,
            None => self.ingest(resident, None, &boundary.encode(&[])?)?.0,
        };
        let before = resident.current.clone();
        let (_, ingested) = self.ingest(resident, Some(&moment), &encoded)?;
        let consumed = ingested
            .forward
            .into_present()
            .expect("ingest returns consumption");
        if consumed.cells != 1 {
            return Err(HnnError::Unadmitted {
                reason: "observed continuation must consume exactly one class",
            });
        }
        crib.push(&field, &before, class, placement, field.crib().window)?;
        let close = if consumed.carry_out {
            let closing = PairedObservation::admit(&field, &resident.constitution, pairing)?;
            let encoded_crib = crib.closing(&field, &closing, field.crib().window)?;
            let family = resident.admitted.clone();
            let closed = close_and_locate(self, resident, &family, &encoded_crib)?;
            crib.reopen();
            Some(closed)
        } else {
            None
        };
        let cells = resident
            .moment(&moment)
            .expect("continuing moment remains open")
            .cells();
        Ok(IngestClassReceipt {
            cells,
            ingest: ingested.receipt,
            close,
        })
    }

    /// Compare and deposit one actually delivered cell, then use the shared ingest step.
    /// The observer receives read-only post-deposit, pre-ingest operands at most once.
    /// Return any exterior view from the observer: it is released inside the successful
    /// receipt only after commit. A later refusal drops that view without publishing it.
    /// Every refusal leaves both the resident and caller-owned crib unchanged.
    pub fn observe_cell_continuing<T>(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        class: usize,
        placement: Option<&OccurrencePlacement>,
        observer: impl FnOnce(
            &Field,
            &Constitution,
            &SourceMoment,
            &ActiveAddress,
            &DepositReading,
        ) -> T,
    ) -> Result<ObservedCellReceipt<T>, HnnError> {
        let (boundary, target) = admit_observed_cell(resident, crib, pairing, class, placement)?;
        if self.refining {
            return Err(HnnError::Unadmitted {
                reason: "contact-grain scheduling is not wired for the observed continuation consumer",
            });
        }
        if !resident.pending.is_empty() || !resident.staged.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "observed continuation requires consumed comparison handles",
            });
        }
        let phases = match resident.admitted.as_slice() {
            [phases] if phases.aperture() == 1 => phases.clone(),
            [_] => {
                return Err(HnnError::Unadmitted {
                    reason: "observed continuation is wired only for aperture one; no unscored tail",
                });
            }
            _ => {
                return Err(HnnError::Unadmitted {
                    reason: "observed continuation requires one unambiguous declared receiver",
                });
            }
        };
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        let field = next.field.clone();
        let moment = match next.moments.keys().next().copied() {
            Some(moment) => moment,
            None => self.ingest(&mut next, None, &boundary.encode(&[])?)?.0,
        };
        let comparison_commit = next.constitution.commit();
        // Admission has checked the target, but the blind read cannot consult it.
        let (pending, refined) = self.refine(&mut next, &moment, &phases)?;
        let (staged, compared) = self.compare(&mut next, pending, &target)?;
        let features = compared
            .deposit
            .present()
            .ok_or(HnnError::Unadmitted {
                reason: "observed precision requires the actual comparison's staged return",
            })?
            .linear()
            .iter()
            .filter(|step| step.locus == LinearLocus::Receiving(phases.ring()))
            .flat_map(|step| step.samples.iter().map(|sample| sample.feature.clone()))
            .collect::<Vec<Vec<Rat>>>();
        let deposited = self.deposit(&mut next, staged)?;
        let before_commit = next.constitution.commit();
        let before_exponent = next
            .constitution
            .lattice(Locus::ReceivingMap(phases.ring()))?
            .exponent();
        let balance_before = next.ledger.balance().clone();
        let event = next.constitution.receiving_precision_event(
            phases.ring(),
            &features,
            phases.tolerance(),
        )?;
        if let Some(event) = &event {
            next.publish_receiving_precision(event)?;
        }
        let precision = ObservedPrecisionReceipt {
            checked: true,
            features,
            event,
            before_commit,
            after_commit: next.constitution.commit(),
            before_exponent,
            after_exponent: next
                .constitution
                .lattice(Locus::ReceivingMap(phases.ring()))?
                .exponent(),
            balance_before,
            balance_after: next.ledger.balance().clone(),
        };
        let post_deposit = deposited
            .deposit
            .into_present()
            .expect("deposit returns a reading");
        let view = observer(
            &field,
            &next.constitution,
            next.moment(&moment).expect("open moment"),
            &next.address,
            &post_deposit,
        );
        let ingestion_commit = next.constitution.commit();
        let fed = self.ingest_class_step(&mut next, &mut next_crib, pairing, class, placement)?;
        let receipt = ObservedCellReceipt {
            cells: fed.cells,
            comparison_commit,
            ingestion_commit,
            prediction: refined
                .forward
                .into_present()
                .expect("refine returns blind faces"),
            refine: refined.receipt,
            compare: compared.receipt,
            deposit: deposited.receipt,
            precision,
            ingest: fed.ingest,
            close: fed.close,
            view,
        };
        *resident = next;
        *crib = next_crib;
        Ok(receipt)
    }
}

#[cfg(test)]
mod precision_tests {
    use super::*;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::tests::learning::{OPEN_BUDGET, chain_declaration};
    use crate::ratio::integer;

    fn prepared(awaiting: bool) -> (Reference, Resident, PairingDeclaration, MomentId) {
        prepared_at(if awaiting { Some(1) } else { None })
    }

    fn prepared_at(
        steps_to_boundary: Option<u64>,
    ) -> (Reference, Resident, PairingDeclaration, MomentId) {
        let mut declaration = chain_declaration(1 << 16);
        declaration.receivers[0].ring = 0;
        declaration.receivers[0].aperture = 1;
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        let free = ExactRatMatrix::shaped(
            8,
            4,
            (0..8)
                .map(|r| {
                    (0..4)
                        .map(|c| integer(i64::from((r == 2 && c == 0) || (r == 3 && c == 2))))
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let source = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &source).unwrap();
        let material = crate::hnn::tests::learning::generic_within(&field, 81, OPEN_BUDGET)
            .with_ports(
                0,
                None,
                None,
                Some(ExactRatMatrix::zero(8, field.ring(0).width()).unwrap()),
            )
            .unwrap()
            .with_symmetric_source(0, source, carrier.symmetry())
            .unwrap();
        let current = if let Some(steps) = steps_to_boundary {
            Current::at(
                &field,
                field
                    .rings()
                    .iter()
                    .map(|ring| BigInt::from(ring.period() - steps))
                    .collect(),
            )
            .unwrap()
        } else {
            Current::at_rest(&field)
        };
        let port = Reference::new(4, OPEN_BUDGET);
        let mut resident = port.mount_with(&field, &current, material).unwrap();
        let cell = PairedObservation::admit(&field, resident.constitution(), &pairing)
            .unwrap()
            .encode(&[0])
            .unwrap();
        let (moment, _) = port.ingest(&mut resident, None, &cell).unwrap();
        assert_eq!(resident.awaiting_boundary(), steps_to_boundary == Some(1));
        // Unit fixture only: retain a legal sub-lattice imaginary component along an actual
        // blind receiving operand. No target or diagnostic output chooses its direction.
        let mut pilot = resident.clone();
        let phases = pilot.admitted[0].clone();
        let (pending, _) = port.refine(&mut pilot, &moment, &phases).unwrap();
        let features = pilot.receiving_inputs(&pending, &phases).unwrap().unwrap();
        let column = features[0]
            .iter()
            .position(|x| !x.is_zero())
            .expect("a reached receiving coordinate");
        let width = field.ring(0).width();
        let unit = resident
            .constitution
            .lattice(Locus::ReceivingMap(0))
            .unwrap()
            .unit();
        let mut text = resident.constitution.continuing_state(0).unwrap().to_text();
        let start = text.find(&format!("receiving 8 {width}\n")).unwrap();
        let at = start + text[start..].find("map-carry 0\n").unwrap();
        text.replace_range(
            at..at + "map-carry 0\n".len(),
            &format!("map-carry 1\n{} {}\n", width + column, unit / integer(4)),
        );
        super::super::precision_publication_tests::receiving_carry_clock(&mut text, 0, 2);
        let text = ContinuingState::stamped(&text, &resident.constitution).unwrap();
        let state = ContinuingState::from_text(&text).unwrap();
        resident.constitution = resident.constitution.clone().continued(&state).unwrap();
        (port, resident, pairing, moment)
    }

    fn manual_publication(
        port: &Reference,
        next: &mut Resident,
        pairing: &PairingDeclaration,
        moment: MomentId,
    ) -> (
        Vec<Vec<Rat>>,
        ReceivingPrecision,
        Constitution,
        crate::aeon::EnclosedBalance,
    ) {
        let phases = next.admitted[0].clone();
        let boundary = PairedObservation::admit(&next.field, &next.constitution, pairing).unwrap();
        let (pending, _) = port.refine(next, &moment, &phases).unwrap();
        let target = boundary.encode(&[2]).unwrap();
        let (staged, compared) = port.compare(next, pending, &target).unwrap();
        let features: Vec<Vec<Rat>> = compared
            .deposit
            .present()
            .unwrap()
            .linear()
            .iter()
            .filter(|step| step.locus == LinearLocus::Receiving(phases.ring()))
            .flat_map(|step| step.samples.iter().map(|sample| sample.feature.clone()))
            .collect();
        port.deposit(next, staged).unwrap();
        let before = next.constitution.clone();
        let ledger = next.ledger.balance().clone();
        let event = before.receiving_precision_event(phases.ring(), &features, phases.tolerance()).unwrap()
            .expect("the fixed unit fixture must actually publish a previously erased carried component");
        next.publish_receiving_precision(&event).unwrap();
        (features, event, before, ledger)
    }

    fn conserved(before: &Constitution, after: &Constitution, ring: usize) {
        let a = before.receiving_law(ring).unwrap();
        let b = after.receiving_law(ring).unwrap();
        for ((x, rx), (y, ry)) in a
            .map()
            .entries()
            .iter()
            .zip(a.map_remainder().entries())
            .zip(b.map().entries().iter().zip(b.map_remainder().entries()))
        {
            assert_eq!(x + rx, y + ry);
        }
        for ((x, rx), (y, ry)) in a
            .gram()
            .entries()
            .iter()
            .zip(a.gram_remainder().entries())
            .zip(b.gram().entries().iter().zip(b.gram_remainder().entries()))
        {
            assert_eq!(x + rx, y + ry);
        }
    }

    fn crib(resident: &Resident) -> ObservedCrib {
        ObservedCrib::new(resident.moments.values().next().unwrap().cells() as usize)
    }
    #[test]
    fn observed_precision_uses_actual_staged_features_at_the_successor() {
        let (port, mut entry, pairing, moment) = prepared(false);
        let mut manual = entry.clone();
        let (features, event, before, ledger) =
            manual_publication(&port, &mut manual, &pairing, moment);
        conserved(&before, &manual.constitution, event.ring());
        let after = manual.ledger.balance().clone();
        let mut crib = crib(&entry);
        let receipt = port
            .observe_cell_continuing(&mut entry, &mut crib, &pairing, 2, None, |_, _, _, _, _| ())
            .unwrap();
        assert!(receipt.precision.checked);
        assert_eq!(receipt.precision.features, features);
        assert_eq!(receipt.precision.event, Some(event));
        assert_eq!(receipt.precision.balance_before, ledger);
        assert_eq!(receipt.precision.balance_after, after);
        assert_eq!(after.arrivals, ledger.arrivals);
        assert_eq!(after.arrived, ledger.arrived);
        assert_eq!(after.publications, ledger.publications + 1);
        assert_eq!(entry.continuing().unwrap().0, moment);
    }
    #[test]
    fn observed_precision_late_ingest_refusal_rolls_back_publication_when_its_close_rejects_the_crib()
     {
        let (port, mut entry, pairing, moment) = prepared_at(Some(2));
        let mut manual = entry.clone();
        let (_, event, before, _) = manual_publication(&port, &mut manual, &pairing, moment);
        assert!(event.to_exponent() > event.from_exponent());
        assert!(manual.constitution.commit() > before.commit());
        let placement = OccurrencePlacement::at(
            &entry.field,
            &entry.current,
            &[vec![0; entry.field.rings().len()]],
        )
        .unwrap();
        let next = entry.moments[&moment].cells() as usize;
        let mut crib = ObservedCrib::new(next.saturating_sub(1));
        crib.next = next;
        // A caller-owned invalid closing cell is not read by blind admission or refine.
        // It is refused when the shared close owner encodes the crib after publication.
        crib.entries.push(ObservedCribCell {
            position: next.saturating_sub(1),
            class: entry.field.alphabet(),
            placement: None,
        });
        let before = format!("{entry:?}");
        let prior_crib = crib.clone();
        let initial_commit = entry.constitution.commit();
        let saw_publication = std::cell::Cell::new(false);
        assert!(
            port.observe_cell_continuing(
                &mut entry,
                &mut crib,
                &pairing,
                2,
                Some(&placement),
                |_, material, _, _, _| saw_publication.set(material.commit() >= initial_commit + 2)
            )
            .is_err()
        );
        assert!(
            saw_publication.get(),
            "the view was reached after deposit and publication, before the closing refusal"
        );
        assert_eq!(format!("{entry:?}"), before);
        assert_eq!(crib, prior_crib);
    }
}
