//! The native contact return consumed by the next continuing Word (Refs #73 #62).
//!
//! [agent-inferred] Source admission happens at open through SourceMoment::open_storage on the
//! producing constitution and Current. The full-tick contact return retains one reached change,
//! not the word's recorded passages. Its comparison return uses the producing executed solves.
//! Contact factors change C, K and D at the contact's held canonical state `(u, π = C w)`: the
//! rate after the deposit solves `C′ w′ = C w` (the storage-resolution record §9); the reflected
//! stationary chart is a receiver analysis, not the executed state. Ring/pump/source-map changes
//! need their own transported return and are not silently treated as contact-coordinate changes
//! here.

use std::sync::Arc;

use super::*;
use crate::hnn::constitution::{Constitution, DepositReading, FactorGradient, Locus, Reach};
use crate::hnn::port::{Deposit, WordReturn};
use crate::hnn::encoding::Encoded;
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector, target_phases};
use crate::hnn::retention::Diamond;
use crate::receiver::reception::{Component, InteractionReturn};

/// The full-tick source-bound contact cut, promoted from ContactCut's private producer checks.
/// Only a native source-opened word's actual return issues one. No public state constructor.
#[derive(Debug)]
pub struct ContactCut {
    field: Field,
    producing: Constitution,
    current: Current,
    source: Arc<SourceMoment>,
    operands: Operands,
    change: EndChange,
    next_tick: usize,
    released: Remainders,
    deposit: Option<Deposit>,
}

/// Separate material work from the opening split and from the subsequent executed balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuationReceipt {
    pub before: Rat,
    pub committed: Rat,
    pub deposition_work: Rat,
    pub opening: Rat,
    pub opening_difference: Rat,
    pub released: Remainders,
}

impl<'c> Word<'c> {
    /// Open the existing word on the source's actual encoded moment, recording its native
    /// constitution/current/source binding. Warm charts are the existing certified operands.
    pub fn open_source(
        field: &'c Field,
        producing: &Constitution,
        current: &Current,
        source: Arc<SourceMoment>,
        charts: &mut Charts,
    ) -> Result<Self, HnnError> {
        let mut word = Self::open_charted(field, producing, current, &source, charts)?;
        word.native_source = Some((producing.clone(), current.clone(), source));
        Ok(word)
    }

    /// Enter the exact physical field with this native producer binding, on its carried
    /// interior. The target-independent opening uses the same source chart as open_source;
    /// a later comparison uses this producing constitution/current/source identity.
    pub fn open_source_exact_received(
        field: &'c Field,
        producing: &Constitution,
        current: &Current,
        source: Arc<SourceMoment>,
        opening: &WordOpening,
    ) -> Result<(Self, SourceOpeningReceipt), HnnError> {
        let (mut word, receipt) =
            Self::open_exact_received(field, producing, current, &source, opening)?;
        word.native_source = Some((producing.clone(), current.clone(), source));
        Ok((word, receipt))
    }

    /// Compare the actual receiving anchors and compose contact storage from that same return.
    /// [agent-inferred] The first admitted material family is C at one reached contact; K and D
    /// remain fixed. The receiver declaration, phases, map and lift come from this producer.
    /// Targets use the same field encoding and phase transport; no map or covector is supplied.
    pub fn compare_contact_storage(
        self,
        receiver: usize,
        contact: usize,
        targets: &Encoded,
    ) -> Result<
        (HolonRatio, InteractionReturn<ContactCut, WordReturn, Deposit, Vec<Option<usize>>, Remainders>),
        HnnError,
    > {
        let (theta, current, source) = self.native_source.as_ref().ok_or(HnnError::Shape {
            what: "a native comparison requires its source producer", expected: 1, found: 0,
        })?.clone();
        let field = self.field;
        let declaration = field.receivers().get(receiver).ok_or(HnnError::Shape {
            what: "the native admitted receiver", expected: field.receivers().len(), found: receiver,
        })?;
        if contact >= field.contacts().len() {
            return Err(HnnError::Shape {
                what: "the native compared contact", expected: field.contacts().len(), found: contact,
            });
        }
        let phases = ReceivingPhases::declare(field, &theta, &current, declaration)?;
        let reads: Vec<_> = phases.epochs().map(|epoch| {
            let anchor = self.anchor(epoch, phases.ring()).ok_or(HnnError::WordEnded {
                ticks: self.ticks(),
            })?;
            phases.read(field, &theta, &current, anchor)
        }).collect::<Result<_, _>>()?;
        let classes: Vec<usize> = targets.classes_read().collect();
        let ratio = HolonRatio::compare(
            Faces::of_reads(&reads, phases.grain())?, &classes,
            &target_phases(field, current.lift(), phases.ring(), targets)?,
        )?;
        let returned = self.return_contact(
            &ratio.covector()?, theta.receiving_map(phases.ring()).ok_or(HnnError::Shape {
                what: "the native producing receiving map", expected: 1, found: 0,
            })?,
            &current.lift()[phases.ring()], &phases,
        )?;
        let mut cut = returned.forward.into_present().ok_or(HnnError::Realization {
            what: "the actual compared contact cut",
        })?;
        let back = returned.pullback.into_present().ok_or(HnnError::Realization {
            what: "the actual compared contact adjoint",
        })?;
        let diamond = Diamond::of(field, &phases);
        let retained = |locus| locus == Locus::Channel(contact) && diamond.retains(field, locus);
        let (steps, _) = crate::hnn::reference::compose_contact(
            field, &theta, &back, &diamond, &retained, current.lift(), field.step(), contact,
        )?;
        let steps: Vec<_> = steps.into_iter().filter(|step| {
            matches!(step.gradient, FactorGradient::Storage { .. })
        }).collect();
        let occupied = field.sources().iter().map(|&g| {
            let mut count = 0u64;
            for c in 0..field.ring(g).placements().len() {
                if source.phase_counts(g,c)?.iter().any(|n| *n != 0) {
                    count = count.checked_add(1).ok_or(HnnError::CountOverflow)?;
                }
            }
            Ok(count)
        }).collect::<Result<Vec<_>, HnnError>>()?.into_iter().max().unwrap_or(0);
        let deposit = Deposit::new(theta.commit(), vec![], steps, vec![Locus::Channel(contact)])
            .with_reach(Reach {
                receiver: phases.ring(), stations: phases.epochs().map(|e| e as u64).collect(),
                entries: vec![0], phases: occupied,
                loci: diamond.retained(field),
            });
        cut.deposit = Some(deposit.clone());
        Ok((ratio, InteractionReturn {
            forward: Component::Present(cut), pullback: Component::Present(back),
            deposit: Component::Present(deposit), order: returned.order,
            phases: returned.phases, receipt: returned.receipt,
        }))
    }

    /// Consume the actual comparison return and retain its reached full-tick change. A terminal
    /// junction has different arriving/outgoing ports and cannot issue this cut. The pulled-back
    /// covector uses the actual producing operands, including warm charts and pump phases.
    pub(crate) fn return_contact(
        self,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        lift: &num_bigint::BigInt,
        phases: &ReceivingPhases,
    ) -> Result<
        InteractionReturn<ContactCut, WordReturn, (), Vec<Option<usize>>, Remainders>,
        HnnError,
    > {
        let (producing, current, source) = self.native_source.as_ref().ok_or(HnnError::Shape {
            what: "a contact return requires its native source producer",
            expected: 1,
            found: 0,
        })?;
        let change = self.change()?;
        if self.fields.len() != self.ticks() || self.balances.len() != self.ticks() {
            return Err(HnnError::Shape {
                what: "a contact return requires a complete tick",
                expected: self.ticks(),
                found: self.fields.len(),
            });
        }
        let next_tick = self
            .opened_at
            .checked_add(self.ticks())
            .ok_or(HnnError::CountOverflow)?;
        if self.clock.ticks() != BigUint::from(next_tick) {
            return Err(HnnError::Shape {
                what: "the full-tick cut carries its actual hop clock",
                expected: next_tick,
                found: self.opened_at,
            });
        }
        for (ring, resonator) in self.operands.resonators().iter().enumerate() {
            if let Some(resonator) = resonator {
                if change.resonator_phases[ring]
                    != Some(resonator.phase_at(next_tick.saturating_sub(1)))
                {
                    return Err(HnnError::Resonator {
                        ring,
                        what: "the contact return carries the actual last pump phase",
                    });
                }
            }
        }
        let released = self
            .resonators
            .iter()
            .flatten()
            .fold(self.carried.released(), |reading, resonance| {
                reading.join(&Remainders::of(resonance.remainders.all()))
            });
        let cut = ContactCut {
            released,
            deposit: None,
            field: self.field.clone(),
            producing: producing.clone(),
            current: current.clone(),
            source: source.clone(),
            operands: self.operands.clone(),
            change,
            next_tick,
        };
        let phase_carry = cut.change.resonator_phases.clone();
        let back = self.pull_back(covector, map, lift, phases)?;
        let released = back.released.clone();
        Ok(InteractionReturn {
            forward: Component::Present(cut),
            pullback: Component::Present(back),
            deposit: Component::Absent("the comparison return stages no successor here"),
            order: Component::Absent("a contact cut carries no new source order"),
            phases: Component::Present(phase_carry),
            receipt: released,
        })
    }
}

impl ContactCut {
    pub fn change(&self) -> &EndChange {
        &self.change
    }
    pub fn next_tick(&self) -> usize {
        self.next_tick
    }

    /// Apply a native contact-factor deposit, read its work at the held momentum, and open the
    /// next Word on the held change (`C′ w′ = C w` per contact; `HnnError::HeldMomentum` where
    /// `C′` cannot hold it).
    /// The source and Current stay bound. The native deposit checks commit/reach/certificate and
    /// returns the actual whole successor/publication; no caller-supplied successor is accepted.
    /// The native coordinates and complete last pump phase carry; successor inverse charts are
    /// re-certified by Operands::at_cut_charted before the private chart cache is published.
    pub fn continue_deposited<'c>(
        self,
        field: &'c Field,
        current: &Current,
        source: &Arc<SourceMoment>,
        deposit: &Deposit,
        charts: &mut Charts,
    ) -> Result<
        (
            Constitution,
            InteractionReturn<
                Word<'c>,
                (),
                DepositReading,
                Vec<Option<usize>>,
                ContinuationReceipt,
            >,
        ),
        HnnError,
    > {
        if field != &self.field || current != &self.current || !Arc::ptr_eq(source, &self.source) {
            return Err(HnnError::Shape {
                what: "the contact continuation keeps its field/current/source producer",
                expected: 1,
                found: 0,
            });
        }
        if self.deposit.as_ref() != Some(deposit) {
            return Err(HnnError::Shape {
                what: "the deposited contact covector is this cut's actual comparison return",
                expected: 1, found: 0,
            });
        }
        if deposit
            .loci()
            .iter()
            .any(|locus| !matches!(locus, crate::hnn::constitution::Locus::Channel(_)))
            || !deposit.linear().is_empty()
            || !deposit.landmarks().is_empty()
            || !deposit.receiving().is_empty()
            || deposit.factors().iter().any(|step| {
                !matches!(
                    step.gradient,
                    FactorGradient::Storage { .. }
                        | FactorGradient::Stiffness { .. }
                        | FactorGradient::Dissipation { .. }
                )
            })
        {
            return Err(HnnError::Shape {
                what: "this native return changes contact factors in their same physical coordinates",
                expected: deposit.factors().len(),
                found: 0,
            });
        }
        #[cfg(test)] let started = std::time::Instant::now();
        #[cfg(test)] eprintln!("unit certificate begin elapsed_ms=0");
        let (successor, publication) = self.producing.deposited(deposit)?;
        #[cfg(test)] eprintln!("unit certificate end elapsed_ms={}", started.elapsed().as_millis());
        let mut next_charts = charts.clone();
        let operands = if self.operands.lattice().is_some() {
            Operands::at_cut_charted(field, &successor, current, &mut next_charts)?
        } else {
            Operands::exact_at_cut(field, &successor, current)?
        };
        #[cfg(test)] eprintln!("unit successor-operands elapsed_ms={}", started.elapsed().as_millis());
        // The unchanged material families preserve ring storage, coupling ports and every lifted
        // pump. This comparison uses their actual declarations, not inverse-chart seed equality.
        for (old, new) in self.operands.rings().iter().zip(operands.rings()) {
            if old.element() != new.element()
                || old.passive() != new.passive()
                || old.contrast() != new.contrast()
                || old.sheets() != new.sheets()
                || old.admittance() != new.admittance()
            {
                return Err(HnnError::Shape {
                    what: "contact deposition preserves the ring and junction constitution",
                    expected: 0,
                    found: 1,
                });
            }
        }
        if self.operands.resonators() != operands.resonators()
            || self.operands.surfaces() != operands.surfaces()
            || self.operands.step() != operands.step()
        {
            return Err(HnnError::Shape {
                what: "contact deposition preserves the pump/surface/hop declarations",
                expected: 0,
                found: 1,
            });
        }
        for (old, new) in self.operands.contacts().iter().zip(operands.contacts()) {
            if old.ends() != new.ends()
                || old.exponent() != new.exponent()
                || old.conductance() != new.conductance()
            {
                return Err(HnnError::Shape {
                    what: "contact deposition preserves the geometric coupling and ports",
                    expected: 0,
                    found: 1,
                });
            }
        }
        // [definition; the storage-resolution record §9, the deposit record §2–§3] The deposit is
        // a sudden change of the constitution between two ticks of one continuing motion, so the
        // contact's canonical state `(u, π = C w)` holds across it and the rate solves
        // `C′ w′ = C w` ([`PowerForm::held`]); a momentum `C′` cannot hold is refused.
        let old = PowerForm::read(field, &self.producing, current)?;
        let new = PowerForm::read(field, &successor, current)?;
        let held = old.held(&new, &self.change)?;
        let before = old.power(&self.change)? + old.resonator_power(&self.change)?;
        let committed = new.power(&held.change)? + new.resonator_power(&held.change)?;
        let deposition_work = held.deposition;
        if &committed - &before != deposition_work {
            return Err(HnnError::Shape {
                what: "the native contact return's work at the held momentum closes",
                expected: 0,
                found: 1,
            });
        }
        let nothing: Vec<_> = self
            .change
            .storage
            .iter()
            .map(|wave| zeros(wave.len()))
            .collect();
        let mut word = Word::continuing(field, operands, &held.change, &nothing, self.next_tick)?;
        word.native_source = Some((successor.clone(), current.clone(), source.clone()));
        #[cfg(test)] eprintln!("unit next-word-open elapsed_ms={}", started.elapsed().as_millis());
        let opened = word.change()?;
        let opening = new.power(&opened)? + new.resonator_power(&opened)?;
        let opening_difference = &opening - &committed;
        let released = self.released;
        *charts = next_charts;
        Ok((
            successor,
            InteractionReturn {
                forward: Component::Present(word),
                pullback: Component::Absent("the native deposit consumes the reached covectors"),
                deposit: Component::Present(publication),
                order: Component::Absent("contact deposition keeps source order"),
                phases: Component::Present(self.change.resonator_phases),
                receipt: ContinuationReceipt {
                    before,
                    committed,
                    deposition_work,
                    opening,
                    opening_difference,
                    released,
                },
            },
        ))
    }
}
