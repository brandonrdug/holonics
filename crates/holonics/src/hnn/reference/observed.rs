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
        let deposited = self.deposit(&mut next, staged)?;
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
            ingest: fed.ingest,
            close: fed.close,
            view,
        };
        *resident = next;
        *crib = next_crib;
        Ok(receipt)
    }
}
