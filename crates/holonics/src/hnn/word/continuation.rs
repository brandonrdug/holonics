//! The native contact return consumed by the next continuing Word (Refs #73 #62).
//!
//! [agent-inferred] Source admission happens at open through SourceMoment::open_storage on the
//! producing constitution and Current. The full-tick contact return retains the reached change,
//! not the word's recorded passages. Its comparison return uses the producing executed solves.
//! Contact factors change C, K and D at the contact's held canonical state `(u, π = C w)`: the
//! rate after the deposit solves `C′ w′ = C w` (the storage-resolution record §9); the reflected
//! stationary chart is a receiver analysis, not the executed state. Ring/pump/source-map changes
//! need their own transported return and are not silently treated as contact-coordinate changes
//! here.

use std::sync::Arc;

use super::*;
use crate::hnn::constitution::{Constitution, DepositReading, FactorGradient, Family, Locus, Reach};
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
    opening_support: Vec<usize>,
    operands: Operands,
    change: EndChange,
    opened_at: usize,
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
    /// The actual applied C/K/D-factor movements, including their quadratic terms and the
    /// lattice/carry's effect. The proposal's eta times direction is not substituted here.
    pub material: Vec<ContactMaterialMove>,
    /// C_old <= (1 + epsilon) C_new, read by the existing fixed inertia search. This is the
    /// held-momentum bound, distinct from publication.storage_growth's held-rate bound.
    /// None withholds a uniform bound; actual held-state work remains explicitly charged.
    pub held_momentum_growth: Option<Rat>,
}

/// One reached contact family's actual finite reaction:
/// `dA = dF Sigma F^T + F Sigma dF^T + dF Sigma dF^T`.
/// Sigma is the producing K signature, or identity for C/D. D changes the next tick's
/// `h omega^T D omega`; it contributes no stored energy at the held cut. This identity includes
/// the square term, uses the applied coarse factor, and asserts no finite comparison decrease.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactMaterialMove {
    pub contact: usize,
    /// Existing channel families: Factor(0) is C, Factor(1) is K, Factor(2) is D.
    pub family: Family,
    pub factor: ExactRatMatrix,
    pub linear: ExactRatMatrix,
    pub quadratic: ExactRatMatrix,
    pub form: ExactRatMatrix,
}

impl ContactMaterialMove {
    /// Read the full finite movement against the forms actually admitted to each Word.
    pub(crate) fn between(
        producing: &Constitution,
        successor: &Constitution,
        before: &Operands,
        after: &Operands,
        contact: usize,
        family: Family,
    ) -> Result<Self, HnnError> {
        let (old_factor, new_factor, old_form, new_form, signature) = match family {
            Family::Factor(0) => (producing.contact_storage(contact),
                successor.contact_storage(contact), before.contacts()[contact].forms().0,
                after.contacts()[contact].forms().0, None),
            Family::Factor(1) => {
                let signature = producing.contact_stiffness_signature(contact);
                if signature != successor.contact_stiffness_signature(contact) {
                    return Err(HnnError::Realization { what: "the continuing contact keeps its producing stiffness signature" });
                }
                (producing.contact_stiffness(contact), successor.contact_stiffness(contact),
                    before.contacts()[contact].forms().1, after.contacts()[contact].forms().1, signature)
            },
            Family::Factor(2) => (producing.contact_dissipation(contact),
                successor.contact_dissipation(contact), before.contacts()[contact].forms().2,
                after.contacts()[contact].forms().2, None),
            _ => return Err(HnnError::Realization { what: "a finite contact movement is a C/K/D factor family" }),
        };
        let factor = new_factor.subtract(old_factor)?;
        let signed = |factor: &ExactRatMatrix| match signature {
            Some(signs) => crate::hnn::constitution::signed_columns(factor, signs),
            None => Ok(factor.clone()),
        };
        let transpose = factor.transpose()?;
        let linear = signed(&factor)?.multiply(&old_factor.transpose()?)?
            .add(&signed(old_factor)?.multiply(&transpose)?)?;
        let quadratic = signed(&factor)?.multiply(&transpose)?;
        let form = new_form.subtract(old_form)?;
        if linear.add(&quadratic)? != form {
            return Err(HnnError::Realization { what: "the full applied C/K/D contact reaction" });
        }
        Ok(Self { contact, family, factor, linear, quadratic, form })
    }
}

/// C_old <= (1 + epsilon) C_new bounds the energy at held momentum. The storage-growth
/// owner's argument order is deliberately reversed: its usual direction bounds held rate.
fn certify_held_momentum_growth(
    before: &[ExactRatMatrix],
    after: &[ExactRatMatrix],
) -> Result<Option<Rat>, HnnError> {
    crate::hnn::constitution::certify_storage_growth(after, before)
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
        let support = word.change()?.support(field);
        word.native_source = Some((producing.clone(), current.clone(), source, support));
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
        // Include the carried support before an opening split can put a small coordinate wholly
        // into its remainder. Source rings are seeded separately by Diamond::opened.
        let mut support = opening.support(field);
        support.extend(word.change()?.support(field));
        support.sort_unstable();
        support.dedup();
        word.native_source = Some((producing.clone(), current.clone(), source, support));
        Ok((word, receipt))
    }

    pub(super) fn contact_receiving(&self, receiver: usize) -> Result<(ReceivingPhases, Faces), HnnError> {
        let (theta, current, _, _) = self.native_source.as_ref().ok_or(HnnError::Shape {
            what: "a native reading requires its source producer", expected: 1, found: 0,
        })?;
        let declaration = self.field.receivers().get(receiver).ok_or(HnnError::Shape {
            what: "the native admitted receiver", expected: self.field.receivers().len(), found: receiver,
        })?;
        let phases = ReceivingPhases::declare(self.field, theta, current, declaration)?;
        let reads: Vec<_> = phases.epochs().map(|epoch| {
            let anchor = self.anchor(epoch, phases.ring()).ok_or(HnnError::WordEnded {
                ticks: self.ticks(),
            })?;
            phases.read(self.field, theta, current, anchor)
        }).collect::<Result<_, _>>()?;
        let faces = Faces::of_reads(&reads, phases.grain())?;
        Ok((phases, faces))
    }

    /// Read every complex receiving face, with its grain fibre, before any target/comparison.
    /// This observes the actual Word; it neither deposits nor authorizes boundary release.
    pub fn contact_faces(&self, receiver: usize) -> Result<Faces, HnnError> {
        Ok(self.contact_receiving(receiver)?.1)
    }

    /// Compare a declared observed consequence and react at every reached contact's C/K/D factors.
    /// The full Encoded consequence declares the selective target clock;
    /// `compared` projects its receiving stations, not unknown target cells/advances. No caller
    /// selects a contact, map, gradient or step. Uncompared faces remain in the returned ratio.
    /// The existing Gauss--Newton proposal selector and all native physical gates are retained;
    /// their certificate does not prove full finite comparison decrease (constitution scope).
    pub fn compare_contacts(
        self,
        receiver: usize,
        targets: &Encoded,
        compared: &[bool],
    ) -> Result<
        (HolonRatio, InteractionReturn<ContactCut, WordReturn, Deposit, Vec<Option<usize>>, Remainders>),
        HnnError,
    > {
        let (theta, current, source, support) = self.native_source.as_ref().ok_or(HnnError::Shape {
            what: "a native comparison requires its source producer", expected: 1, found: 0,
        })?.clone();
        let field = self.field;
        let (phases, faces) = self.contact_receiving(receiver)?;
        let classes: Vec<usize> = targets.classes_read().collect();
        let ratio = HolonRatio::compare_partition(
            faces, &classes,
            &target_phases(field, current.lift(), phases.ring(), targets)?,
            compared,
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
        let diamond = Diamond::opened(field, &phases, &support);
        let retained = |locus| matches!(locus, Locus::Channel(_)) && diamond.retains(field, locus);
        let mut steps = Vec::new();
        for contact in 0..field.contacts().len() {
            let (contact_steps, _) = crate::hnn::reference::compose_contact(
                field, &theta, &back, &diamond, &retained, current.lift(), field.step(), contact,
            )?;
            steps.extend(contact_steps);
        }
        // A completely unconstrained reading causes no material statistic or deposit clock.
        if ratio.stations().is_empty() {
            steps.clear();
        }
        let occupied = field.sources().iter().map(|&g| {
            let mut count = 0u64;
            for c in 0..field.ring(g).placements().len() {
                if source.phase_counts(g,c)?.iter().any(|n| *n != 0) {
                    count = count.checked_add(1).ok_or(HnnError::CountOverflow)?;
                }
            }
            Ok(count)
        }).collect::<Result<Vec<_>, HnnError>>()?.into_iter().max().unwrap_or(0);
        let reached = steps.iter().map(|step| step.gradient.locus()).collect();
        let deposit = Deposit::new(theta.commit(), vec![], steps, reached)
            .with_reach(Reach {
                receiver: phases.ring(), stations: ratio.stations().iter()
                    .map(|&j| (phases.first_epoch() + j) as u64).collect(),
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

    /// Capture the actual full-tick end before consuming this Word's adjoint. Both ordinary
    /// and continuing-material comparisons use this one producer/clock/phase admission.
    pub(super) fn contact_cut(&self) -> Result<ContactCut,HnnError> {
        let (producing, current, source, opening_support) = self.native_source.as_ref().ok_or(HnnError::Shape {
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
        Ok(ContactCut {
            released,
            deposit: None,
            field: self.field.clone(),
            producing: producing.clone(),
            current: current.clone(),
            source: source.clone(),
            opening_support: opening_support.clone(),
            operands: self.operands.clone(),
            change,
            opened_at: self.opened_at,
            next_tick,
        })

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
        let cut = self.contact_cut()?;
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
    /// Source-private binding by the actual comparison consumer. A caller cannot replace the
    /// covector once the native cut has been issued.
    pub(super) fn bind_comparison(mut self, deposit:Deposit) -> Self {
        self.deposit = Some(deposit);
        self
    }

    /// The support captured before this Word's first tick, not the reached cut's support.
    pub fn opening_support(&self) -> &[usize] {
        &self.opening_support
    }

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
        // The exact contact route reads the entire loaded field, at the producing
        // absolute clock, rather than multiplying undriven local ring certificates.
        let (successor, publication) = if self.operands.lattice().is_none() {
            let spans = super::finite_gain::FiniteContactSpans::of(&self.operands, self.opened_at,
                deposit.reach().ok_or(HnnError::MissingReach)?)?;
            self.producing.deposited_with_contact_spans(deposit, &spans)?
        } else {
            // Historical charted consumer keeps its conditional certificate. It issues
            // no loaded witness: rounding/split residual inputs are not covered here.
            self.producing.deposited(deposit)?
        };
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
        // Read the applied movement, not eta times the unrounded proposal. Cross terms between
        // contacts act through the next full coupled Word; none is removed by a local surrogate.
        let mut material = Vec::new();
        for step in deposit.factors() {
            let (contact, family) = match step.gradient {
                FactorGradient::Storage { contact, .. } => (contact, Family::Factor(0)),
                FactorGradient::Stiffness { contact, .. } => (contact, Family::Factor(1)),
                FactorGradient::Dissipation { contact, .. } => (contact, Family::Factor(2)),
                _ => unreachable!("the bound contact deposit was admitted above"),
            };
            material.push(ContactMaterialMove::between(&self.producing, &successor,
                &self.operands, &operands, contact, family)?);
        }
        let before_capacity: Vec<_> = self.operands.contacts().iter()
            .map(|contact| contact.forms().0.clone()).collect();
        let after_capacity: Vec<_> = operands.contacts().iter()
            .map(|contact| contact.forms().0.clone()).collect();
        let held_momentum_growth = certify_held_momentum_growth(
            &before_capacity, &after_capacity,
        )?;
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
        // The held state is the actual unsplit opening; a zero lattice representative does not
        // remove a carried coordinate's support from the comparison horizon.
        let support = held.change.support(field);
        let mut word = Word::continuing(field, operands, &held.change, &nothing, self.next_tick)?;
        word.native_source = Some((successor.clone(), current.clone(), source.clone(), support));
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
                    material,
                    held_momentum_growth,
                },
            },
        ))
    }
}
