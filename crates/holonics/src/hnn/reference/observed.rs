//! Aperture-one observed continuation through the native transactional owner.
//! The epoch route can explicitly select execution of its actual return and grouped
//! reached records; its source, face and publication laws remain this owner's.
//!
//! The helical pair interaction keeps its helix, pair, faces and occurrence placement;
//! cell holonomy, tube and tower laws are unchanged. Comparison reads E_Θ(u,x), then
//! ingestion reads E_Θ′(u,x). The caller, never the resident, holds the finite crib.

use super::comparison::FrozenComparison;
use super::*;
use crate::hnn::constitution::Sample;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::encoding::placement::OccurrencePlacement;
use crate::hnn::paired::PairingDeclaration;

mod checkpoint;
mod diagnostic;
mod epoch;
pub use diagnostic::{
    PendingReadoutDiagnostic, ReceiverPrefixReceipt, TargetPrefixReadoutControlReceipt,
};
mod tree_release;
pub use tree_release::TreeReleaseReceipt;
mod stream;
pub use epoch::{
    ChannelMaterialProbeRefusal, EpochStageAttempt, EpochStageCondition, EpochStageReading,
    EpochStageRefusal, EpochStageValue, ObservedChannelStorageAblationReading,
    ObservedEpochCellReceipt, ObservedEpochDepositionScope, ObservedEpochEnergy,
    ObservedEpochOutcome, ObservedEpochProbeState, ObservedEpochReceipt, ObservedEpochWallTimes,
};
pub use stream::{ObservedStream, ObservedStreamReceipt};
mod execution;
pub use execution::{
    HostObservedEpochExecution, ObservedEpochExecution, ObservedEpochForwardContext,
    ObservedEpochForwardWord, ObservedEpochWord, ScannedHostObservedEpochExecution,
};

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
    if resident.observed_epoch_terminal {
        return Err(HnnError::Unadmitted {
            reason: "a terminal partial epoch cannot continue as an ordinary observed life",
        });
    }
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

    /// Continue a private release fork with its actual emitted class. The next draw reads
    /// `P_scored(c | emitted_prefix)`: receive the same family likelihoods as `release_cells`,
    /// and the same addressed tree arrival as an observed prefix, before advancing ingress.
    /// Physical maps, comparison/deposition clocks and the trunk do not learn from this receipt.
    /// A refusal publishes neither the conditional prefix nor the ingest/crib successor.
    pub fn ingest_released_cell_continuing(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        pending: PendingId,
        decision: &crate::hnn::receiving::cells::CellDecision,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<IngestClassReceipt, HnnError> {
        if resident.receiving_law() != crate::hnn::receiving::ReceivingLaw::CoarseGrainV1 {
            return Err(HnnError::Unadmitted {
                reason: "the selected retained-fibre resident receives its own full-fibre prefix receipt",
            });
        }
        let refuse = |reason| HnnError::Unadmitted { reason };
        let class = decision
            .class()
            .ok_or_else(|| refuse("only an emitted release cell advances a conditional prefix"))?;
        admit_observed_cell(resident, crib, pairing, class, placement)?;
        if resident.pending.len() != 1 || !resident.staged.is_empty() {
            return Err(refuse(
                "a release continuation consumes its one producing pending ratio",
            ));
        }
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        let phases = slot.ratio.phases();
        let receiver = phases.ring();
        if phases.aperture() != 1 || decision.phase != 0 {
            return Err(refuse(
                "release continuation receives one aperture-one decision",
            ));
        }
        if slot.ratio.commit() != resident.constitution.commit()
            || slot.ratio.current(&resident.field)? != resident.current
            || resident.moments.values().next() != Some(slot.ratio.moment())
        {
            return Err(refuse(
                "a released cell continues its producing material and current",
            ));
        }
        let producing = decision
            .scored_face
            .as_ref()
            .ok_or_else(|| refuse("a released cell keeps its producing scored family"))?;
        let population = resident
            .constitution
            .population(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
        // CellDecision is exterior evidence with public fields. Bind its whole producing
        // expression to this pending word, using private chart state so a stale/forged
        // expression cannot change even the resident's solver view on refusal.
        let mut validation_charts = resident.charts.clone();
        let (_, wave) = slot.ratio.read_on(
            &resident.field,
            &resident.constitution,
            &mut validation_charts,
            &slot.opening,
        )?;
        let against = slot.ratio.against(&resident.constitution, &wave, &[])?;
        if against.trees.len() != 1 || against.faces.faces.len() != 1 {
            return Err(refuse(
                "one producing tree and combined face belong to the released cell",
            ));
        }
        let actual = crate::hnn::receiving::cells::ScoredFaceReading {
            population: population.clone(),
            tree_probabilities: against.trees[0].probabilities.clone(),
            combined: against.faces.faces[0].clone(),
        };
        if producing != &actual || decision.face != actual.masses_at(decision.bits)? {
            return Err(refuse(
                "a release continuation receives its actual producing population, tree and combined face",
            ));
        }
        let step = ReceivingStep {
            ring: receiver,
            tree: producing
                .tree_probabilities
                .get(class)
                .ok_or(HnnError::CellOutside {
                    code: class,
                    alphabet: producing.tree_probabilities.len(),
                })?
                .clone(),
            // As in release_cells/score, family likelihood is received at the declared
            // reading precision, independently of the demand depth certifying the draw.
            combined: crate::hnn::receiving::face_enclosure_at(
                &producing.combined,
                class,
                crate::ratio::exponentiated::READING_BITS,
            )?,
        };
        let mut tree = resident
            .constitution
            .landmarks(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
            .clone();
        match slot.ratio.observed_addresses(&[])? {
            Some(addresses) => {
                tree.receive_observed_arrivals(&addresses, &[class], phases.grain())?;
            }
            None => {
                tree.receive_arrivals(&slot.ratio.addresses(&[])?, &[class], phases.grain())?;
            }
        }
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        next.constitution = next
            .constitution
            .observed_epoch_prefix(receiver, tree, &[step])?;
        self.discard(&mut next, Handle::Pending(pending))?;
        let receipt =
            self.ingest_class_step(&mut next, &mut next_crib, pairing, class, placement)?;
        *resident = next;
        *crib = next_crib;
        Ok(receipt)
    }

    /// The common source ingest and close step; conditional receiving is joined by its caller.
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
        self.observe_cell_continuing_inner(
            resident,
            crib,
            pairing,
            class,
            placement,
            false,
            |field, material, moment, address, reading, _, _| {
                observer(field, material, moment, address, reading)
            },
        )
    }

    /// Diagnostic-only variant that exposes the exact staged receiving samples used by this
    /// comparison. Samples are copied before deposit consumes the staged value and are returned
    /// only inside the ordinary successful receipt. The callback runs at the same post-deposit,
    /// pre-ingest point as `observe_cell_continuing`; callers should keep it read-only because
    /// external callback side effects cannot be rolled back if the later ingest refuses.
    pub fn observe_cell_continuing_with_samples<T>(
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
            &[Sample],
            Option<&FrozenComparison>,
        ) -> T,
    ) -> Result<ObservedCellReceipt<T>, HnnError> {
        self.observe_cell_continuing_inner(
            resident, crib, pairing, class, placement, true, observer,
        )
    }

    fn observe_cell_continuing_inner<T>(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        class: usize,
        placement: Option<&OccurrencePlacement>,
        capture_samples: bool,
        observer: impl FnOnce(
            &Field,
            &Constitution,
            &SourceMoment,
            &ActiveAddress,
            &DepositReading,
            &[Sample],
            Option<&FrozenComparison>,
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
        let frozen_comparison = if capture_samples {
            let slot = next.pending.get(&pending).ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
            let wave = refined.forward.present().ok_or(HnnError::Unadmitted {
                reason: "diagnostic sample view requires the actual refined wave",
            })?;
            Some(FrozenComparison::new(
                &field,
                &next.constitution,
                &slot.ratio,
                &slot.opening,
                &target,
                wave,
            )?)
        } else {
            None
        };
        let (staged, compared) = self.compare(&mut next, pending, &target)?;
        let captured_samples = if capture_samples {
            compared
                .deposit
                .present()
                .ok_or(HnnError::Unadmitted {
                    reason: "observed sample view requires the actual comparison's staged return",
                })?
                .linear()
                .iter()
                .filter(|step| step.locus == LinearLocus::Receiving(phases.ring()))
                .flat_map(|step| step.samples.iter().cloned())
                .collect::<Vec<Sample>>()
        } else {
            Vec::new()
        };
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
            &captured_samples,
            frozen_comparison.as_ref(),
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
        let base = crate::hnn::tests::learning::generic_within(&field, 81, OPEN_BUDGET)
            .with_ports(
                0,
                None,
                None,
                Some(ExactRatMatrix::zero(8, field.ring(0).width()).unwrap()),
            )
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
        let width = field.ring(0).width();
        let grain = Rat::new(
            BigInt::from(1),
            BigInt::from(field.finest_grain()) << 1usize,
        );
        let mut source_scale = Rat::one();
        // The same real word is re-read at each power of two. Neither the target nor a
        // fabricated receiver tolerance chooses the seed or its scale.
        let (mut resident, moment, column, unit) = loop {
            let rows = (0..source.rows())
                .map(|r| {
                    (0..source.columns())
                        .map(|c| source.get(r, c).unwrap() * &source_scale)
                        .collect()
                })
                .collect();
            let scaled = ExactRatMatrix::shaped(source.rows(), source.columns(), rows).unwrap();
            let carrier = PairedCarrier::admit(&field, 0, &pairing, &scaled).unwrap();
            let material = base
                .clone()
                .with_symmetric_source(0, scaled, carrier.symmetry())
                .unwrap();
            let mut resident = port.mount_with(&field, &current, material).unwrap();
            let cell = PairedObservation::admit(&field, resident.constitution(), &pairing)
                .unwrap()
                .encode(&[0])
                .unwrap();
            let (moment, _) = port.ingest(&mut resident, None, &cell).unwrap();
            assert_eq!(resident.awaiting_boundary(), steps_to_boundary == Some(1));
            let mut pilot = resident.clone();
            let phases = pilot.admitted[0].clone();
            let (pending, _) = port.refine(&mut pilot, &moment, &phases).unwrap();
            let features = pilot.receiving_inputs(&pending, &phases).unwrap().unwrap();
            let column = features[0]
                .iter()
                .enumerate()
                .max_by(|(_, a), (_, b)| a.abs().cmp(&b.abs()))
                .map(|(column, _)| column)
                .expect("a reached receiving coordinate");
            let unit = resident
                .constitution
                .lattice(Locus::ReceivingMap(0))
                .unwrap()
                .unit();
            let read = &unit / integer(4) * features[0][column].abs();
            let norm: Rat = features[0].iter().map(|x| x.abs()).sum();
            if read > grain && norm > integer(width as i64) {
                break (resident, moment, column, unit);
            }
            // The scale stops at the lattice's own reach `2^L = 1/unit`: past it a unit cell of
            // the map would hold the whole feature, so a failure there is the fixture's, not a
            // larger search's.
            assert!(
                &source_scale * &unit < Rat::one(),
                "observed precision fixture: no read above the grain by source scale \
                 {source_scale} (boundary {steps_to_boundary:?}, feature l1 {norm}, X {width}, \
                 retained read {read}, grain {grain})"
            );
            source_scale *= integer(2);
        };
        let mut text = resident.constitution.continuing_state(0).unwrap().to_text();
        let start = text.find(&format!("receiving 8 {width}\n")).unwrap();
        let at = start + text[start..].find("map-carry 0\n").unwrap();
        text.replace_range(
            at..at + "map-carry 0\n".len(),
            &format!("map-carry 1\n{} {}\n", width + column, unit / integer(4)),
        );
        super::super::precision_publication_tests::receiving_carry_clock(&mut text, 0, 2);
        let text = ContinuingState::stamped(&text, &resident.constitution).unwrap();
        let state = ContinuingState::from_text(&text, resident.constitution().budget()).unwrap();
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
        let event = before
            .receiving_precision_event(phases.ring(), &features, phases.tolerance())
            .unwrap()
            .expect("the above-grain real-word fixture must publish its erased carried component");
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
    fn diagnostic_sample_hook_matches_ordinary_execution_and_exposes_actual_samples() {
        let (port, mut ordinary, pairing, _) = prepared(false);
        let mut diagnostic = ordinary.clone();
        let mut ordinary_crib = crib(&ordinary);
        let mut diagnostic_crib = ordinary_crib.clone();
        let ordinary_receipt = port
            .observe_cell_continuing(
                &mut ordinary,
                &mut ordinary_crib,
                &pairing,
                2,
                None,
                |_, _, _, _, reading| reading.commit,
            )
            .unwrap();
        let diagnostic_receipt = port
            .observe_cell_continuing_with_samples(
                &mut diagnostic,
                &mut diagnostic_crib,
                &pairing,
                2,
                None,
                |_, _, _, _, reading, samples, frozen| {
                    let held = frozen
                        .map(|comparison| comparison.recompare_covector(comparison.wave()))
                        .transpose();
                    (reading.commit, samples.to_vec(), held)
                },
            )
            .unwrap();
        assert_eq!(ordinary_receipt.view, diagnostic_receipt.view.0);
        assert!(!diagnostic_receipt.view.1.is_empty());
        assert_eq!(
            ordinary
                .continuing_state(ordinary.field.sources()[0])
                .unwrap(),
            diagnostic
                .continuing_state(diagnostic.field.sources()[0])
                .unwrap()
        );
        assert_eq!(ordinary_crib, diagnostic_crib);
        assert_eq!(ordinary_receipt.prediction, diagnostic_receipt.prediction);
        assert_eq!(ordinary_receipt.precision, diagnostic_receipt.precision);
        assert_eq!(ordinary_receipt.ingest, diagnostic_receipt.ingest);
        assert_eq!(
            diagnostic_receipt
                .view
                .1
                .iter()
                .map(|sample| sample.feature.clone())
                .collect::<Vec<_>>(),
            diagnostic_receipt.precision.features
        );
        let held = diagnostic_receipt
            .view
            .2
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap();
        assert_eq!(
            held,
            &diagnostic_receipt
                .view
                .1
                .iter()
                .map(|sample| sample.covector.clone())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn diagnostic_sample_hook_refusal_returns_no_view_and_rolls_back() {
        let (port, mut entry, pairing, _) = prepared_at(Some(2));
        let placement = OccurrencePlacement::at(
            &entry.field,
            &entry.current,
            &[vec![0; entry.field.rings().len()]],
        )
        .unwrap();
        let next = entry.moments.values().next().unwrap().cells() as usize;
        let mut crib = ObservedCrib::new(next.saturating_sub(1));
        crib.next = next;
        crib.entries.push(ObservedCribCell {
            position: next.saturating_sub(1),
            class: entry.field.alphabet(),
            placement: None,
        });
        let before = format!("{entry:?}");
        let crib_before = crib.clone();
        let result = port.observe_cell_continuing_with_samples(
            &mut entry,
            &mut crib,
            &pairing,
            2,
            Some(&placement),
            |_, _, _, _, reading, samples, _| (reading.commit, samples.to_vec()),
        );
        assert!(
            result.is_err(),
            "a refused close returns no diagnostic receipt/view"
        );
        assert_eq!(format!("{entry:?}"), before);
        assert_eq!(crib, crib_before);
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

#[cfg(test)]
mod released_prefix_tests {
    use super::*;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::receiving::cells::{CellDecision, CellLaw};
    use crate::hnn::tests::learning::chain_declaration;
    use crate::ratio::rat;
    use crate::receiver::release::KeyStream;

    fn opening() -> (Reference, Resident, ObservedCrib, PairingDeclaration) {
        opening_at(false)
    }

    fn opening_at(before_carry: bool) -> (Reference, Resident, ObservedCrib, PairingDeclaration) {
        let mut declaration = chain_declaration(1 << 16);
        declaration.receivers[0].aperture = 1;
        declaration.rings[0].lock = (0..declaration.rings[0].period).collect();
        declaration.rings[2] = declaration.rings[1].clone();
        declaration.rings[2].lock.clear();
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        let free = ExactRatMatrix::shaped(
            8,
            4,
            (0..8)
                .map(|row| {
                    (0..4)
                        .map(|column| {
                            if (row == 2 && column == 0) || (row == 3 && column == 2) {
                                rat(1, 32)
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let source = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &source).unwrap();
        let material = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, source, carrier.symmetry())
            .unwrap();
        let reference = Reference::new(16, 1 << 40);
        let current = if before_carry {
            Current::at(
                &field,
                field
                    .rings()
                    .iter()
                    .map(|ring| BigInt::from(ring.period() - 1))
                    .collect(),
            )
            .unwrap()
        } else {
            Current::at_rest(&field)
        };
        let mut resident = reference.mount_with(&field, &current, material).unwrap();
        let boundary = PairedObservation::admit(&field, &resident.constitution, &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        (reference, resident, ObservedCrib::new(0), pairing)
    }

    fn draw(
        port: &Reference,
        resident: &mut Resident,
        keys: &mut KeyStream,
    ) -> (PendingId, CellDecision) {
        let (moment, _) = resident.continuing().unwrap();
        let phases = resident.admitted[0].clone();
        let (pending, _) = port.refine(resident, &moment, &phases).unwrap();
        let release = port
            .release_cells(resident, &pending, CellLaw::Draw(keys))
            .unwrap()
            .forward
            .into_present()
            .unwrap();
        (pending, release.cells.into_iter().next().unwrap())
    }

    fn same_refused_state(
        actual: &Resident,
        before: &Resident,
        crib: &ObservedCrib,
        old_crib: &ObservedCrib,
    ) {
        assert_eq!(actual.constitution, before.constitution);
        assert_eq!(actual.current, before.current);
        assert_eq!(actual.address, before.address);
        assert_eq!(actual.moments, before.moments);
        assert_eq!(actual.carried, before.carried);
        assert_eq!(actual.observed_epoch_ingress, before.observed_epoch_ingress);
        assert_eq!(actual.ledger.balance(), before.ledger.balance());
        assert_eq!(
            actual.pending.keys().collect::<Vec<_>>(),
            before.pending.keys().collect::<Vec<_>>()
        );
        assert_eq!(actual.next, before.next);
        assert_eq!(actual.state_bits(), before.state_bits());
        assert_eq!(crib, old_crib);
    }

    #[test]
    fn released_prefix_matches_scored_conditional_family_and_preserves_first_draw() {
        let (port, trunk, trunk_crib, pairing) = opening();
        let untouched = trunk.clone();
        let mut fork = trunk.clone();
        let mut crib = trunk_crib.clone();
        let receiver = trunk.admitted[0].ring();
        let opening_ingress = trunk.receiver_ingress_ticks();
        let maximum_cells: usize = trunk.field.rings()[..receiver]
            .iter()
            .map(|ring| ring.period() as usize)
            .product();
        let mut keys = KeyStream::new(vec![0; maximum_cells], 1).unwrap();
        let mut classes = Vec::new();
        let mut decisions = Vec::new();
        let mut successors = Vec::new();
        for index in 0..maximum_cells {
            let (pending, decision) = draw(&port, &mut fork, &mut keys);
            if index == 0 {
                let mut old_first = trunk.clone();
                let mut old_keys = KeyStream::new(vec![0], 1).unwrap();
                let (_, unchanged) = draw(&port, &mut old_first, &mut old_keys);
                assert_eq!(decision, unchanged);
                assert_eq!(old_keys.keys_read(), 1);
            }
            let class = decision
                .class()
                .expect("the declared key selects one exact class");
            classes.push(class);
            let receiver = fork.admitted[0].ring();
            let material_commit = fork.constitution.commit();
            let ledger = fork.ledger.balance().clone();
            port.ingest_released_cell_continuing(
                &mut fork, &mut crib, &pairing, pending, &decision, None,
            )
            .unwrap();
            assert!(fork.pending.is_empty());
            assert_eq!(fork.constitution.commit(), material_commit);
            assert_eq!(fork.ledger.balance().depositions, ledger.depositions);
            assert_eq!(
                fork.constitution.receiving_map(receiver),
                trunk.constitution.receiving_map(receiver)
            );
            decisions.push(decision);
            successors.push(fork.clone());
            if fork.receiver_ingress_ticks() != opening_ingress {
                break;
            }
        }
        assert!(
            classes.len() >= 3,
            "the fixture reaches two later conditional faces"
        );
        assert_ne!(fork.receiver_ingress_ticks(), opening_ingress);
        // The ordinary batched heard owner is the independent oracle. Its requested cuts
        // retain the producing physical medium and advance only actual prefix tree/population.
        let mut teacher = trunk.clone();
        let mut teacher_crib = trunk_crib.clone();
        let cuts: Vec<_> = (1..=classes.len()).collect();
        let receipt = port
            .observe_epoch_continuing_at_cuts(
                &mut teacher,
                &mut teacher_crib,
                &pairing,
                &classes,
                None,
                &cuts,
                false,
            )
            .unwrap();
        assert_eq!(receipt.consumed, classes.len());
        assert!(receipt.closed_section);
        assert!(!receipt.terminal_partial);
        assert_eq!(keys.keys_read(), classes.len());
        for (index, (decision, heard)) in decisions.iter().zip(&receipt.reads).enumerate() {
            assert_eq!(
                decision.scored_face.as_ref(),
                Some(&heard.scored_face),
                "conditional prefix {index}"
            );
            assert_eq!(
                decision.face,
                heard.scored_face.masses_at(decision.bits).unwrap()
            );
            let (_, prefix, _) = receipt
                .prefixes
                .iter()
                .find(|(at, _, _)| *at == index + 1)
                .unwrap();
            let successor = &successors[index];
            let ring = successor.admitted[0].ring();
            assert_eq!(
                successor.constitution.population(ring),
                prefix.constitution.population(ring)
            );
            assert_eq!(
                successor.constitution.landmarks(ring),
                prefix.constitution.landmarks(ring)
            );
            assert_eq!(successor.current, prefix.current);
            assert_eq!(successor.address, prefix.address);
            assert_eq!(successor.moments, prefix.moments);
            assert_eq!(successor.carried, prefix.carried);
        }
        same_refused_state(&trunk, &untouched, &trunk_crib, &ObservedCrib::new(0));
    }

    #[test]
    fn released_prefix_late_close_refusal_rolls_back_conditional_reception() {
        let (port, mut fork, mut crib, pairing) = opening_at(true);
        let mut keys = KeyStream::new(vec![0], 1).unwrap();
        let (pending, decision) = draw(&port, &mut fork, &mut keys);
        let class = decision.class().unwrap();
        let boundary = PairedObservation::admit(&fork.field, &fork.constitution, &pairing).unwrap();
        let mut clock = fork.current.clone();
        assert!(
            clock
                .step(&fork.field, &boundary.encode(&[class]).unwrap(), 0)
                .unwrap()
                .carry_out
        );
        // Admission checks the crib position; only the shared close reads this malformed
        // prior entry after conditional reception and ingress have already run on the clone.
        crib.entries.push(ObservedCribCell {
            position: 0,
            class: fork.field.alphabet(),
            placement: None,
        });
        let before = fork.clone();
        let crib_before = crib.clone();
        assert!(
            port.ingest_released_cell_continuing(
                &mut fork, &mut crib, &pairing, pending, &decision, None
            )
            .is_err()
        );
        same_refused_state(&fork, &before, &crib, &crib_before);
    }

    #[test]
    fn released_prefix_refusals_preserve_population_tree_pending_and_crib() {
        let (port, mut fork, mut crib, pairing) = opening();
        let mut keys = KeyStream::new(vec![0], 1).unwrap();
        let (pending, decision) = draw(&port, &mut fork, &mut keys);
        let before = fork.clone();
        let old_crib = crib.clone();
        let mut stale = decision.clone();
        let class = stale.class().unwrap();
        let producing = stale.scored_face.as_mut().unwrap();
        producing
            .population
            .receive(&[
                crate::ratio::algebraic::ExactInterval::point(
                    producing.tree_probabilities[class].clone(),
                ),
                crate::hnn::receiving::face_enclosure_at(
                    &producing.combined,
                    class,
                    crate::ratio::exponentiated::READING_BITS,
                )
                .unwrap(),
            ])
            .unwrap();
        assert!(
            port.ingest_released_cell_continuing(
                &mut fork, &mut crib, &pairing, pending, &stale, None
            )
            .is_err()
        );
        same_refused_state(&fork, &before, &crib, &old_crib);
        let mut wrong_combined = decision.clone();
        let trees = fork.pending[&pending]
            .ratio
            .tree_faces(&fork.constitution, &[])
            .unwrap();
        let phases = fork.admitted[0].clone();
        let mut wave = vec![Rat::zero(); 2 * fork.field.alphabet()];
        wave[0] = Rat::one();
        let changed =
            crate::hnn::receiving::ReceivingRead::combined(wave, &trees[0], phases.grain())
                .unwrap();
        let changed = crate::hnn::ratio::Face::of_read(&changed, phases.grain()).unwrap();
        assert_ne!(
            changed,
            wrong_combined.scored_face.as_ref().unwrap().combined
        );
        wrong_combined.scored_face.as_mut().unwrap().combined = changed;
        assert!(
            port.ingest_released_cell_continuing(
                &mut fork,
                &mut crib,
                &pairing,
                pending,
                &wrong_combined,
                None
            )
            .is_err()
        );
        same_refused_state(&fork, &before, &crib, &old_crib);
        let mut wrong_enclosure = decision.clone();
        wrong_enclosure.face[0].upper += Rat::one();
        assert!(
            port.ingest_released_cell_continuing(
                &mut fork,
                &mut crib,
                &pairing,
                pending,
                &wrong_enclosure,
                None
            )
            .is_err()
        );
        same_refused_state(&fork, &before, &crib, &old_crib);
        let mut wrong_crib = ObservedCrib::new(1);
        let old_wrong = wrong_crib.clone();
        assert!(
            port.ingest_released_cell_continuing(
                &mut fork,
                &mut wrong_crib,
                &pairing,
                pending,
                &decision,
                None
            )
            .is_err()
        );
        same_refused_state(&fork, &before, &wrong_crib, &old_wrong);
        assert_eq!(keys.keys_read(), 1);
        let (port, mut held, mut held_crib, pairing) = opening();
        let mut no_keys = KeyStream::new(Vec::new(), 1).unwrap();
        let (pending, decision) = draw(&port, &mut held, &mut no_keys);
        assert!(decision.class().is_none());
        let before = held.clone();
        let crib_before = held_crib.clone();
        assert!(
            port.ingest_released_cell_continuing(
                &mut held,
                &mut held_crib,
                &pairing,
                pending,
                &decision,
                None
            )
            .is_err()
        );
        same_refused_state(&held, &before, &held_crib, &crib_before);
        assert_eq!(no_keys.keys_read(), 0);
    }
}
