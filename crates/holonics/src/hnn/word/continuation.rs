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
//!
//! [definition; agent-inferred, October 9; the medium-of-joints record §7, passed by Epime's
//! source review] **The finite-decrease landing.** The certified contact step sits 20 to 22 binary
//! orders below the material lattice's half-unit, so its applied factor change is zero and the move
//! stays in the remainder. The landing is an a posteriori admission of ONE declared candidate per
//! deposit:
//! - the native deposit law declares each reached family's first reach `k_f`, the least
//!   `k ≥ k_cert(f)` at which the owner's own split of `2^k d_{f,i} + r_i` leaves its cell at some
//!   entry (`Constitution::first_reach`), and produces the candidate `θ′` at those exponents with
//!   every other law shared (`Constitution::deposited_with_contact_spans_at`);
//! - a transient Word of the same declared passage re-reads the comparison on `θ′`: the same source,
//!   the Word's own opening (below), the same junction steps, receiver, targets and mask
//!   ([`Word::compare_contacts_landing`]);
//! - [`FiniteDecrease`] is issued only on an exact, strict improvement of that comparison:
//!   `upper(L′) < lower(L)` with `X′ ≤ X`, or the reading-identity witness with `X′ < X`
//!   ([`decide`], [`reading_identity`]; Lean `HNN/FiniteDecrease.admission_sound`).
//!
//! The claim is only this: `θ′`, in force from this Word's opening cut, reads the declared comparison
//! no worse classically and strictly better in one part. It is not a claim that the held
//! continuation, a later perception or any unseen comparison improves; those remain measured
//! outcomes. The scope is a source-opened, contact-only comparison on exact operands, opened at Rest
//! or on a received carry with nothing absorbed: a completely absorbing opening, an opening that is
//! not the Word's own, the held-variation route and charted operands refuse, typed
//! ([`LandingRefusal`]). A contact-factor candidate has the identical source injection
//! (`SourceMoment::open_storage` reads no contact factor).
//!
//! [definition; agent-inferred, October 9; the held law, `PowerForm::held`] **The opening the
//! candidate re-reads.** A constitution that changes at a cut holds momentum, `C′w′ = π`, so the only
//! realizable "`θ′` in force from this opening" re-opens the Word's own opening through `θ′`: Rest
//! stays Rest, and a received carry crosses into `θ′` at held momentum (`ReceptionCarry::crossed`,
//! `w′_a = w_a + δ_a` with `C_a(θ′) δ_a = π_a − C_a(θ′) w_a`; displacements and storage as carried;
//! arriving waves transmitted at conductances no contact factor moves), at the carry's own clock.
//! At the producing `θ` that crossing is the identity, because the resident publishes only
//! `C_θ w = π` and `held_rate` returns `w` itself when its target `π − C w` is zero (a short circuit
//! that holds for a singular `C` too; the Lean `held_crossing_at_producing` assumes `C` injective). A momentum outside `range C_a(θ′)` refuses the candidate (`HnnError::HeldMomentum`).
//! The proposal is the existing deposit, whose pullback keeps no opening dual (no `J_open` term): it
//! holds the opening rate fixed, which is the re-read's own objective at Rest, where every rate is
//! zero. At a received opening it is only a proposal for the held-crossing objective, and the exact
//! admission alone decides. Making it that objective's first variation needs the opening's
//! held-crossing term `−Σ_a ⟨C_a⁻¹ μ_(w,a), dC_a w_a⟩` in the deposit and an initial-state term in the
//! step's certificate (`FiniteContactSpans`); both are owed (#73).

use std::sync::Arc;

use num_bigint::BigInt;

use super::*;
use crate::hnn::constitution::{
    CommittedReach, Constitution, DeclaredExponents, DeclaredStepRefusal, DepositReading,
    FactorGradient, Family, Locus, Reach,
};
use crate::hnn::port::{ChangeCovector, Deposit, WordReturn};
use crate::ratio::linear::vector::scale;
use crate::hnn::encoding::Encoded;
use crate::hnn::field::ReceiverDeclaration;
use crate::hnn::ratio::{Face, Faces, HolonRatio, RatioCovector, TargetPhases, target_phases};
use crate::hnn::retention::Diamond;
use crate::holon::deposition::strictly_better;
use crate::ratio::algebraic::ExactInterval;
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
    /// The Word's own opening, by value ([`Word::open_exact_received`]); `None` when another opener
    /// entered the Word, whose cut no landing re-reads.
    opening: Option<WordOpening>,
    /// The comparison a landing issued this cut for ([`Word::compare_contacts_landing`]); `None` on
    /// every other route, whose cut no [`FiniteDecrease`] binds.
    landing: Option<LandingBinding>,
    /// Set by the held-variation route's binding, which the landing does not admit.
    held: bool,
}

/// What the landing's comparison bound into its cut: the receiver, the targets and mask, the
/// producing ratio and the opening, by value.
#[derive(Clone, Debug, PartialEq)]
struct LandingBinding {
    receiver: usize,
    declaration: ReceiverDeclaration,
    targets: Encoded,
    compared: Vec<bool>,
    ratio: HolonRatio,
    opening: WordOpening,
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
    /// With an admitted landing ([`ContactCut::continue_admitted`]): the exact
    /// `e = candidate_end − held`, both at `θ′` and at the same absolute tick. `None` otherwise.
    pub landing: Option<LandingDifference>,
}

/// [definition; agent-inferred, October 9] **Where the transient candidate ends against where the
/// held continuation starts**: `e = candidate_end.change − held.change`, every coordinate of the
/// complete [`EndChange`] (storage, arriving waves, contact and resonator states), both at the
/// admitted `θ′` and at the same absolute tick; the resonator phases are their common phases. It is
/// a reading of the gap between the re-read passage and the actual continuing motion, not a claim
/// that the continuation improves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandingDifference {
    pub tick: usize,
    pub difference: EndChange,
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
        self.compare_contacts_read(receiver, targets, compared)
            .map(|(ratio, returned, _)| (ratio, returned))
    }

    /// [`Word::compare_contacts`], with what it read beside its return: the producer binding, the
    /// receiving phases, the target classes and phases, and the junction steps it ran. The landing
    /// re-reads the same declared comparison from these ([`Word::compare_contacts_landing`]).
    fn compare_contacts_read(
        self,
        receiver: usize,
        targets: &Encoded,
        compared: &[bool],
    ) -> Result<
        (
            HolonRatio,
            InteractionReturn<ContactCut, WordReturn, Deposit, Vec<Option<usize>>, Remainders>,
            ComparedRead,
        ),
        HnnError,
    > {
        let (theta, current, source, support) = self.native_source.as_ref().ok_or(HnnError::Shape {
            what: "a native comparison requires its source producer", expected: 1, found: 0,
        })?.clone();
        let field = self.field;
        let ticks = self.ticks();
        let (phases, faces) = self.contact_receiving(receiver)?;
        let classes: Vec<usize> = targets.classes_read().collect();
        let target_reading = target_phases(field, current.lift(), phases.ring(), targets)?;
        let ratio = HolonRatio::compare_partition(
            faces, &classes,
            &target_reading,
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
        // The deposit's loci are the distinct reached loci in first-reached order, as
        // `compose_return` reads them: a contact returns one step per form (C, K and D).
        let mut reached = Vec::new();
        for step in &steps {
            let locus = step.gradient.locus();
            if !reached.contains(&locus) {
                reached.push(locus);
            }
        }
        let deposit = Deposit::new(theta.commit(), vec![], steps, reached)
            .with_reach(Reach {
                receiver: phases.ring(), stations: ratio.stations().iter()
                    .map(|&j| (phases.first_epoch() + j) as u64).collect(),
                entries: vec![0], phases: occupied,
                loci: diamond.retained(field),
            });
        cut.deposit = Some(deposit.clone());
        let read = ComparedRead {
            current,
            source,
            phases,
            classes,
            target_phases: target_reading,
            ticks,
        };
        Ok((ratio, InteractionReturn {
            forward: Component::Present(cut), pullback: Component::Present(back),
            deposit: Component::Present(deposit), order: returned.order,
            phases: returned.phases, receipt: returned.receipt,
        }, read))
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
            opening: self.opened_on.clone(),
            landing: None,
            held: false,
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
        // The held-variation route's combined covector pairs the opening's `J_open`; no landing
        // admits its cut ([`LandingRefusal::HeldVariation`]).
        self.held = true;
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
        let prepared = self.prepare(field, current, source, deposit, charts, None)?;
        Ok(self.finish(prepared, charts))
    }

    /// [definition; agent-inferred, October 9] **The admitted continuation**: the same laws as
    /// [`ContactCut::continue_deposited`], on the admitted candidate `θ′` instead of the certified
    /// successor: [`ContactCut::prepare_admitted`], then [`ContactCut::finish`]. The admission
    /// certifies only the declared re-read comparison; the held continuation's outcome is not
    /// asserted, and a refusal here is returned, never answered by another step.
    pub fn continue_admitted<'c>(
        self,
        field: &'c Field,
        current: &Current,
        source: &Arc<SourceMoment>,
        deposit: &Deposit,
        admission: &FiniteDecrease,
        charts: &mut Charts,
    ) -> Result<(Constitution, Continued<'c>), LandingRefusal> {
        let prepared = self.prepare_admitted(field, current, source, deposit, admission, charts)?;
        Ok(self.finish(prepared, charts))
    }

    /// [definition; agent-inferred, October 9] **The admitted continuation, prepared without
    /// consuming the cut.** It first checks that every binding of the admission equals this cut's
    /// own ([`BindingRefusal`]: the producing `θ` as a whole value, the source by identity and
    /// value, the opening by value, both supports, the cut's change and absolute ticks, the deposit, the
    /// receiver, targets, mask, the producing ratio and the candidate's tick). It then recomputes
    /// `θ′` with the declared-step producer and requires its full equality, material and carries,
    /// with the admitted `θ′`, its publication and its committed reach
    /// ([`BindingRefusal::Candidate`]), and re-reads the admission's decision from its two ratios
    /// ([`BindingRefusal::Decision`]). Every existing check and the held law `C′w′ = Cw` then run
    /// unchanged on `θ′` (the one fallible body both continuations share), with
    /// `e = candidate_end − held` ([`LandingDifference`]). A refusal of that body at `θ′` (the held
    /// law, a preservation check, the held-momentum growth, the work closure, the next Word) is the
    /// typed post-admission refusal [`LandingRefusal::Continuation`]. The cut is untouched either
    /// way, so the route that issued the admission continues on the certified step exactly as before.
    pub(crate) fn prepare_admitted<'c>(
        &self,
        field: &'c Field,
        current: &Current,
        source: &Arc<SourceMoment>,
        deposit: &Deposit,
        admission: &FiniteDecrease,
        charts: &Charts,
    ) -> Result<PreparedContinuation<'c>, LandingRefusal> {
        self.binds(admission, source, deposit)?;
        let reach = deposit.reach().ok_or(HnnError::MissingReach)?;
        let spans = super::finite_gain::FiniteContactSpans::of(&self.operands, self.opened_at, reach)?;
        let (successor, publication, committed) = self
            .producing
            .deposited_with_contact_spans_at(deposit, &spans, &admission.candidate.declared)?
            .map_err(LandingRefusal::Declared)?;
        if successor != admission.candidate.theta
            || publication != admission.candidate.publication
            || committed != admission.candidate.committed
        {
            return Err(LandingRefusal::Binding(BindingRefusal::Candidate));
        }
        // The admission's decision re-read from its two bound ratios.
        if admit(&admission.ratio, &admission.candidate.ratio) != Ok(admission.admitted) {
            return Err(LandingRefusal::Binding(BindingRefusal::Decision));
        }
        let declared = DeclaredSuccessor {
            successor,
            publication,
            end: admission.candidate.end.clone(),
            tick: admission.candidate.tick,
        };
        self.prepare(field, current, source, deposit, charts, Some(declared))
            .map_err(|reason| LandingRefusal::Continuation {
                admitted: admission.admitted,
                reason,
            })
    }

    /// The one fallible body of both continuations, read without consuming the cut: the native
    /// successor (or the admitted declared one), its operands and preservation checks, the applied
    /// material movements, the held-momentum growth, the held law `C′w′ = Cw` and its work closure,
    /// the admitted `e`, and the next Word on the held change. Nothing is published here: the charts
    /// are read, and [`ContactCut::finish`] alone moves the cut's released remainders and pump phases
    /// and assigns the charts.
    fn prepare<'c>(
        &self,
        field: &'c Field,
        current: &Current,
        source: &Arc<SourceMoment>,
        deposit: &Deposit,
        charts: &Charts,
        declared: Option<DeclaredSuccessor>,
    ) -> Result<PreparedContinuation<'c>, HnnError> {
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
        if !contact_only(deposit) {
            return Err(HnnError::Shape {
                what: "this native return changes contact factors in their same physical coordinates",
                expected: deposit.factors().len(),
                found: 0,
            });
        }
        #[cfg(test)] let started = std::time::Instant::now();
        #[cfg(test)] eprintln!("unit certificate begin elapsed_ms=0");
        // The exact contact route reads the entire loaded field, at the producing
        // absolute clock, rather than multiplying undriven local ring certificates. An admitted
        // landing supplies its declared successor, recomputed and compared whole by the caller.
        let (successor, publication, landing) = match declared {
            Some(DeclaredSuccessor { successor, publication, end, tick }) => {
                (successor, publication, Some((end, tick)))
            }
            None => {
                let (successor, publication) = if self.operands.lattice().is_none() {
                    let spans = super::finite_gain::FiniteContactSpans::of(&self.operands, self.opened_at,
                        deposit.reach().ok_or(HnnError::MissingReach)?)?;
                    self.producing.deposited_with_contact_spans(deposit, &spans)?
                } else {
                    // Historical charted consumer keeps its conditional certificate. It issues
                    // no loaded witness: rounding/split residual inputs are not covered here.
                    self.producing.deposited(deposit)?
                };
                (successor, publication, None)
            }
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
        // [definition; agent-inferred, October 9] The admitted candidate's end against the held
        // change, both at the successor and at the same absolute tick: `e = candidate − held`.
        let landing = match landing {
            Some((end, tick)) => {
                if tick != self.next_tick {
                    return Err(HnnError::Shape {
                        what: "the landing's candidate ends at the held change's absolute tick",
                        expected: self.next_tick,
                        found: tick,
                    });
                }
                Some(LandingDifference {
                    tick,
                    difference: end_difference(&end, &held.change)?,
                })
            }
            None => None,
        };
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
        Ok(PreparedContinuation {
            successor,
            publication,
            next_charts,
            word,
            before,
            committed,
            deposition_work,
            opening,
            opening_difference,
            material,
            held_momentum_growth,
            landing,
        })
    }

    /// The infallible end of both continuations: it moves the cut's released remainders and last
    /// pump phases into the return and assigns the prepared charts, and nothing else.
    pub(crate) fn finish<'c>(
        self,
        prepared: PreparedContinuation<'c>,
        charts: &mut Charts,
    ) -> (Constitution, Continued<'c>) {
        let PreparedContinuation {
            successor,
            publication,
            next_charts,
            word,
            before,
            committed,
            deposition_work,
            opening,
            opening_difference,
            material,
            held_momentum_growth,
            landing,
        } = prepared;
        *charts = next_charts;
        (
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
                    released: self.released,
                    material,
                    held_momentum_growth,
                    landing,
                },
            },
        )
    }
}

/// [definition; agent-inferred, October 9] **A continuation with every fallible law already read
/// on its cut and nothing consumed**: the successor and its publication, the prepared charts, the
/// next Word on the held change, and the receipt's readings. Only [`ContactCut::prepare_admitted`]
/// and the certified continuation's own body build one, and only [`ContactCut::finish`] spends it.
pub(crate) struct PreparedContinuation<'c> {
    successor: Constitution,
    publication: DepositReading,
    next_charts: Charts,
    word: Word<'c>,
    before: Rat,
    committed: Rat,
    deposition_work: Rat,
    opening: Rat,
    opening_difference: Rat,
    material: Vec<ContactMaterialMove>,
    held_momentum_growth: Option<Rat>,
    landing: Option<LandingDifference>,
}

/// The continuation's return: the held next Word, the publication and the receipt.
pub type Continued<'c> =
    InteractionReturn<Word<'c>, (), DepositReading, Vec<Option<usize>>, ContinuationReceipt>;

/// What a contact comparison read beside its return ([`Word::compare_contacts`]): the current
/// and source of its producer binding, the receiving phases, the target classes and phases read in
/// the cut's frame, and the junction steps the Word ran. The landing re-reads the same declared
/// comparison from these; nothing here is retained past the comparison.
struct ComparedRead {
    current: Current,
    source: Arc<SourceMoment>,
    phases: ReceivingPhases,
    classes: Vec<usize>,
    target_phases: TargetPhases,
    ticks: usize,
}

/// An admitted landing's declared successor and its candidate's end, passed to the one body.
struct DeclaredSuccessor {
    successor: Constitution,
    publication: DepositReading,
    end: EndChange,
    tick: usize,
}

/// The native contact return's scope: every locus a channel, no linear, landmark or receiving
/// step, and every factor step a contact's `C`, `K` or `D` in its own physical coordinates.
fn contact_only(deposit: &Deposit) -> bool {
    deposit
        .loci()
        .iter()
        .all(|locus| matches!(locus, Locus::Channel(_)))
        && deposit.linear().is_empty()
        && deposit.landmarks().is_empty()
        && deposit.receiving().is_empty()
        && deposit.factors().iter().all(|step| {
            matches!(
                step.gradient,
                FactorGradient::Storage { .. }
                    | FactorGradient::Stiffness { .. }
                    | FactorGradient::Dissipation { .. }
            )
        })
}

/// `a − b` in every coordinate of two ends of one field at one pump phase; refused where their
/// shapes or phases differ.
fn end_difference(a: &EndChange, b: &EndChange) -> Result<EndChange, HnnError> {
    let refuse = || HnnError::Shape {
        what: "a landing difference reads two ends of one field at one pump phase",
        expected: 0,
        found: 1,
    };
    if a.resonator_phases != b.resonator_phases
        || a.storage.len() != b.storage.len()
        || a.arrivals.len() != b.arrivals.len()
        || a.states.len() != b.states.len()
        || a.resonators.len() != b.resonators.len()
    {
        return Err(refuse());
    }
    let wave = |x: &[Rat], y: &[Rat]| -> Result<Vec<Rat>, HnnError> {
        if x.len() != y.len() {
            return Err(refuse());
        }
        Ok(x.iter().zip(y).map(|(p, q)| p - q).collect())
    };
    let pair = |x: &[Vec<Rat>; 2], y: &[Vec<Rat>; 2]| -> Result<[Vec<Rat>; 2], HnnError> {
        Ok([
            wave(x[0].as_slice(), y[0].as_slice())?,
            wave(x[1].as_slice(), y[1].as_slice())?,
        ])
    };
    Ok(EndChange {
        storage: a
            .storage
            .iter()
            .zip(&b.storage)
            .map(|(x, y)| wave(x.as_slice(), y.as_slice()))
            .collect::<Result<_, _>>()?,
        arrivals: a
            .arrivals
            .iter()
            .zip(&b.arrivals)
            .map(|(x, y)| pair(x, y))
            .collect::<Result<_, _>>()?,
        states: a
            .states
            .iter()
            .zip(&b.states)
            .map(|(x, y)| pair(x, y))
            .collect::<Result<_, _>>()?,
        resonators: a
            .resonators
            .iter()
            .zip(&b.resonators)
            .map(|(x, y)| match (x, y) {
                (Some(x), Some(y)) => pair(x, y).map(Some),
                (None, None) => Ok(None),
                _ => Err(refuse()),
            })
            .collect::<Result<_, _>>()?,
        resonator_phases: a.resonator_phases.clone(),
    })
}

// -------------------------------------------------------------------------------------------
// the finite-decrease landing

impl<'c> Word<'c> {
    /// [definition; agent-inferred, October 9] **The comparison, its deposit, and the landing it
    /// issues** (the W0 flow's route, `hnn::physical::contact`). The comparison and its return are
    /// exactly [`Word::compare_contacts`]'s, and its cut binds this comparison (receiver, targets,
    /// mask, producing ratio, opening). `opening` is the one the caller declares this Word was opened
    /// at; it must equal, by value, the opening the Word itself records ([`Word::open_exact_received`]).
    /// Any other declaration, a completely absorbing opening, or a clock that is not the opening's
    /// own (zero at Rest, the carry's ticks on a received carry) issues no candidate and refuses typed
    /// ([`LandingRefusal::Opening`]), as charted operands do ([`LandingRefusal::ChartedOperands`]).
    ///
    /// At a Rest opening, or a received carry with nothing absorbed, on exact operands the landing
    /// reads ONE declared candidate: the native
    /// deposit law's first reach `k_f` per reached family (`Constitution::first_reach`), its
    /// candidate `θ′` (`Constitution::deposited_with_contact_spans_at`), and a transient Word on `θ′`
    /// with its own producer, the same opening entered through `θ′` (a received carry crosses at held
    /// momentum; module header) and the same source, run for the same junction
    /// steps, read at the same receiver and compared with the same targets and mask
    /// ([`HolonRatio::compare_partition`]). Its support must equal the producing support. The
    /// candidate's end change and absolute tick are captured before it is dropped. The landing is
    /// admitted ([`FiniteDecrease`]) only on [`decide`]'s exact strict improvement; every other
    /// outcome is a typed refusal ([`LandingRefusal`]), a measurement, never retried. A refusal of
    /// the landing never refuses the comparison: the cut and the deposit return either way.
    pub(crate) fn compare_contacts_landing(
        self,
        receiver: usize,
        targets: &Encoded,
        compared: &[bool],
        opening: &WordOpening,
    ) -> Result<
        (
            HolonRatio,
            InteractionReturn<ContactCut, WordReturn, Deposit, Vec<Option<usize>>, Remainders>,
            Landing,
        ),
        HnnError,
    > {
        let field = self.field;
        let declaration = field.receivers().get(receiver).cloned().ok_or(HnnError::Shape {
            what: "the native admitted receiver",
            expected: field.receivers().len(),
            found: receiver,
        })?;
        let (ratio, returned, read) = self.compare_contacts_read(receiver, targets, compared)?;
        let InteractionReturn { forward, pullback, deposit, order, phases, receipt } = returned;
        let mut cut = forward.into_present().ok_or(HnnError::Realization {
            what: "the actual compared contact cut",
        })?;
        let issued = deposit.into_present().ok_or(HnnError::Realization {
            what: "the actual compared contact deposit",
        })?;
        cut.landing = Some(LandingBinding {
            receiver,
            declaration: declaration.clone(),
            targets: targets.clone(),
            compared: compared.to_vec(),
            ratio: ratio.clone(),
            opening: opening.clone(),
        });
        let mut landing = Landing {
            declared: None,
            candidate: None,
            outcome: Err(LandingRefusal::Unconstrained),
        };
        landing.outcome = cut.land(
            field,
            &issued,
            &ratio,
            &read,
            opening,
            (receiver, &declaration),
            (targets, compared),
            (&mut landing.declared, &mut landing.candidate),
        );
        Ok((
            ratio,
            InteractionReturn {
                forward: Component::Present(cut),
                pullback,
                deposit: Component::Present(issued),
                order,
                phases,
                receipt,
            },
            landing,
        ))
    }
}

/// [definition; agent-inferred, October 9] **The landing a comparison issues**: the
/// declared exponents when the first reach was read, the transient candidate when it was read, and
/// the admission or its typed refusal. Every value is the machine's; none is retained.
#[derive(Debug)]
pub struct Landing {
    pub declared: Option<DeclaredExponents>,
    pub candidate: Option<LandingCandidate>,
    pub outcome: Result<FiniteDecrease, LandingRefusal>,
}

/// [definition; agent-inferred, October 9] **The transient candidate as read**: its declared
/// exponents, its `θ′` with the declared publication and committed reach, its comparison on the
/// same passage from the same opening, its opening support, and its end change and absolute tick, captured
/// before its Word was dropped. Only the landing builds one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandingCandidate {
    pub(crate) declared: DeclaredExponents,
    pub(crate) theta: Constitution,
    pub(crate) publication: DepositReading,
    pub(crate) committed: CommittedReach,
    pub(crate) ratio: HolonRatio,
    pub(crate) support: Vec<usize>,
    pub(crate) end: EndChange,
    pub(crate) tick: usize,
}

impl LandingCandidate {
    pub fn declared(&self) -> &DeclaredExponents {
        &self.declared
    }
    pub fn theta(&self) -> &Constitution {
        &self.theta
    }
    pub fn publication(&self) -> &DepositReading {
        &self.publication
    }
    pub fn committed(&self) -> &CommittedReach {
        &self.committed
    }
    pub fn ratio(&self) -> &HolonRatio {
        &self.ratio
    }
    pub fn support(&self) -> &[usize] {
        &self.support
    }
    pub fn end(&self) -> &EndChange {
        &self.end
    }
    pub fn tick(&self) -> usize {
        self.tick
    }
}

/// Which case of the admission held (Lean `HNN/FiniteDecrease.admission_sound`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admitted {
    /// `upper(L′) < lower(L)` and `X′ ≤ X`: strictly better classically, no worse in phase.
    Classical,
    /// The reading-identity witness and `X′ < X`: the same code, strictly better in phase.
    Phase,
}

/// [definition; agent-inferred, October 9; Lean `HNN/FiniteDecrease.admission_sound`] **The
/// finite-decrease admission of one declared candidate.** Its claim is only this: the candidate
/// `θ′`, in force from the Word's opening cut, reads the declared comparison (the same source, the
/// same opening entered through `θ′`, junction steps, receiver, targets and mask) no worse
/// classically and strictly better in one part, exactly:
/// `upper(L′) < lower(L)` with `X′ ≤ X`, or equal code expressions (the reading-identity witness)
/// with `X′ < X`. It does not claim that the held continuation improves, that a later perception
/// changes, or that any other comparison descends; those stay measured outcomes. It is the
/// certificate of the declared step, and nothing moves without it.
///
/// Issued only by [`Word::compare_contacts_landing`], the comparison consumer of the cut whose
/// deposit it binds; its fields are crate-private and it has no public constructor. It binds by
/// equality, never by a commit counter: the full producing `θ` and candidate `θ′` with their carries,
/// the declared exponents and each family's committed reach, the source (identity and value), the
/// opening by value and both supports, the cut's change and absolute ticks, the deposit, the receiving
/// declaration and index, the targets and mask, both evaluated ratios, and the candidate's end
/// change and tick ([`ContactCut::continue_admitted`]).
#[derive(Clone, Debug, PartialEq)]
pub struct FiniteDecrease {
    pub(crate) producing: Constitution,
    pub(crate) source: Arc<SourceMoment>,
    pub(crate) opening: WordOpening,
    pub(crate) support: Vec<usize>,
    pub(crate) change: EndChange,
    pub(crate) opened_at: usize,
    pub(crate) next_tick: usize,
    pub(crate) deposit: Deposit,
    pub(crate) receiver: usize,
    pub(crate) declaration: ReceiverDeclaration,
    pub(crate) targets: Encoded,
    pub(crate) compared: Vec<bool>,
    pub(crate) ratio: HolonRatio,
    pub(crate) candidate: LandingCandidate,
    pub(crate) admitted: Admitted,
}

impl FiniteDecrease {
    /// Which case admitted the candidate.
    pub fn admitted(&self) -> Admitted {
        self.admitted
    }
    /// The producing comparison.
    pub fn ratio(&self) -> &HolonRatio {
        &self.ratio
    }
    /// The candidate as read.
    pub fn candidate(&self) -> &LandingCandidate {
        &self.candidate
    }
    /// The declared exponents.
    pub fn declared(&self) -> &DeclaredExponents {
        &self.candidate.declared
    }
    /// Each claimed family's committed reach.
    pub fn committed(&self) -> &CommittedReach {
        &self.candidate.committed
    }
}

/// [definition; agent-inferred, October 9] **Why a landing was not admitted**, typed. Each is a
/// measurement of this one candidate: none is answered by a larger limit, a halving or a second
/// candidate.
#[derive(Debug, PartialEq)]
pub enum LandingRefusal {
    /// A shared native law refused (its owner's own typed refusal).
    Native(HnnError),
    /// An opening the landing does not re-read: a declaration that is not the Word's own opening
    /// (by value), a completely absorbing carry, or a clock that is not the opening's own.
    Opening,
    /// Charted (lattice or split) operands: outside the exact scope.
    ChartedOperands,
    /// The held-variation route's cut.
    HeldVariation,
    /// A deposit that is not contact-only.
    ContactOnly,
    /// No compared station or no reached family: nothing was compared or nothing steps.
    Unconstrained,
    /// The declared step's own refusal.
    Declared(DeclaredStepRefusal),
    /// The candidate's passage differs from the producing one (receiving phases, opening tick or
    /// absolute end tick).
    Passage,
    /// The candidate's opening support differs from the producing support.
    Support,
    /// The exact comparison did not strictly improve.
    Admission(AdmissionRefusal),
    /// An admission does not bind this cut.
    Binding(BindingRefusal),
    /// [definition; agent-inferred, October 9] **A post-admission refusal**: the admitted
    /// candidate's continuation refused at `θ′` (the held law, a preservation check, the
    /// held-momentum growth, the work closure or the next Word), with its native reason. The cut
    /// was not consumed, and the route that issued the admission continues on the certified step.
    Continuation { admitted: Admitted, reason: HnnError },
}

impl From<HnnError> for LandingRefusal {
    fn from(refusal: HnnError) -> Self {
        LandingRefusal::Native(refusal)
    }
}

/// The admission's typed refusals ([`decide`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdmissionRefusal {
    /// `X′ > X`: the phase part grew.
    PhaseWorse,
    /// `upper(L) < lower(L′)`: the classical part grew.
    CodeWorse,
    /// Identical code endpoints without the reading-identity witness: equal endpoints are not
    /// equal codes.
    EqualEndpoints,
    /// The code enclosures overlap: the inequality is not separated.
    Overlap,
    /// The witness holds and `X′ = X`: neither part strictly improved.
    Unchanged,
}

/// The binding's typed refusals ([`ContactCut::continue_admitted`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingRefusal {
    /// The cut was not issued by a landing comparison.
    ForeignCut,
    Producing,
    Source,
    Opening,
    Support,
    Cut,
    Deposit,
    Receiver,
    Targets,
    Mask,
    Ratio,
    Tick,
    /// The admission's decision does not re-read from its two ratios.
    Decision,
    /// The recomputed `θ′`, publication or committed reach is not the admitted one.
    Candidate,
}

/// The gauge-normalized cells of one face, `(n_c − n_max, k_c)` for every class, `n_max` the
/// largest carry VALUE at the station, as [`Face`] normalizes (no argmax class is read). The
/// unresolved fibre is never read.
fn gauge(face: &Face) -> Option<Vec<(BigInt, u64)>> {
    let top = face.cells().iter().map(|cell| &cell.carry).max()?;
    Some(
        face.cells()
            .iter()
            .map(|cell| (&cell.carry - top, cell.phase))
            .collect(),
    )
}

/// [definition; agent-inferred, October 9; Lean `HNN/FiniteDecrease.witness_code_eq`] **The exact
/// reading-identity witness**: at every compared station the grain `L`, the target class, the
/// target phase and the branch are the same, and every class's gauge-normalized cell
/// `(n_c − n_max, k_c)` is equal. Equal inputs give equal exact code expressions
/// (`log₂ Z − (n_c − n_max) − k_c/L`, `Z = Σ_d 2^(n_d − n_max) θ^(k_d)`). The fibre is never read as a
/// value, and identical enclosure endpoints alone never count as equality.
pub(crate) fn reading_identity(producing: &HolonRatio, candidate: &HolonRatio) -> bool {
    if producing.stations() != candidate.stations()
        || producing.phases().len() != candidate.phases().len()
    {
        return false;
    }
    producing
        .stations()
        .iter()
        .zip(producing.phases().iter().zip(candidate.phases()))
        .all(|(&station, (ours, theirs))| {
            let (Some(face), Some(other)) = (
                producing.faces().faces.get(station),
                candidate.faces().faces.get(station),
            ) else {
                return false;
            };
            face.grain() == other.grain()
                && ours.target == theirs.target
                && ours.target_phase == theirs.target_phase
                && ours.branch == theirs.branch
                && gauge(face) == gauge(other)
        })
}

/// [definition; agent-inferred, October 9; Lean `HNN/FiniteDecrease.admission_sound`] **The
/// admission**: with `L`, `L′` the producing and candidate code enclosures and `X`, `X′` their exact
/// phase excesses, admit iff `upper(L′) < lower(L)` and `X′ ≤ X`
/// ([`strictly_better`]`(L, L′)`), or the witness holds and `X′ < X`. Everything else refuses,
/// typed: `X′ > X`, the candidate's code strictly above, identical endpoints without the witness,
/// overlap, and an unchanged witnessed reading.
pub(crate) fn decide(
    code: &ExactInterval,
    excess: &Rat,
    candidate_code: &ExactInterval,
    candidate_excess: &Rat,
    witness: bool,
) -> Result<Admitted, AdmissionRefusal> {
    if candidate_excess > excess {
        return Err(AdmissionRefusal::PhaseWorse);
    }
    if strictly_better(code, candidate_code) {
        return Ok(Admitted::Classical);
    }
    if witness {
        return if candidate_excess < excess {
            Ok(Admitted::Phase)
        } else {
            Err(AdmissionRefusal::Unchanged)
        };
    }
    if strictly_better(candidate_code, code) {
        return Err(AdmissionRefusal::CodeWorse);
    }
    if candidate_code == code {
        return Err(AdmissionRefusal::EqualEndpoints);
    }
    Err(AdmissionRefusal::Overlap)
}

/// The admission read from two evaluated ratios: their code enclosures, exact excesses and the
/// reading-identity witness ([`decide`]).
pub(crate) fn admit(producing: &HolonRatio, candidate: &HolonRatio) -> Result<Admitted, LandingRefusal> {
    let witness = reading_identity(producing, candidate);
    decide(
        &producing.code_length()?,
        &producing.excess(),
        &candidate.code_length()?,
        &candidate.excess(),
        witness,
    )
    .map_err(LandingRefusal::Admission)
}

impl ContactCut {
    /// The landing of this cut's comparison (see [`Word::compare_contacts_landing`]).
    #[allow(clippy::too_many_arguments)]
    fn land(
        &self,
        field: &Field,
        deposit: &Deposit,
        ratio: &HolonRatio,
        read: &ComparedRead,
        opening: &WordOpening,
        (receiver, declaration): (usize, &ReceiverDeclaration),
        (targets, compared): (&Encoded, &[bool]),
        (declared, candidate): (&mut Option<DeclaredExponents>, &mut Option<LandingCandidate>),
    ) -> Result<FiniteDecrease, LandingRefusal> {
        if self.held {
            return Err(LandingRefusal::HeldVariation);
        }
        // Scope: the Word's own opening, Rest at zero or a received carry with nothing absorbed at
        // the carry's ticks; the candidate re-enters it through `θ′` (module header).
        if self.opening.as_ref() != Some(opening) {
            return Err(LandingRefusal::Opening);
        }
        let own_clock = match opening {
            WordOpening::Rest => self.opened_at == 0,
            WordOpening::Received { carry, absorption: Absorption::Nothing } => {
                carry.ticks == self.opened_at
            }
            WordOpening::Received { absorption: Absorption::Complete, .. } => false,
        };
        if !own_clock {
            return Err(LandingRefusal::Opening);
        }
        if self.operands.lattice().is_some()
            || self.operands.rings().iter().any(|ring| ring.chart().is_some())
            || self.operands.contacts().iter().any(|contact| contact.chart().is_some())
        {
            return Err(LandingRefusal::ChartedOperands);
        }
        if !contact_only(deposit) {
            return Err(LandingRefusal::ContactOnly);
        }
        if ratio.stations().is_empty() || deposit.factors().is_empty() {
            return Err(LandingRefusal::Unconstrained);
        }
        // The declared step, produced by the native deposit law at its first reach.
        let reach = deposit.reach().ok_or(HnnError::MissingReach)?;
        let spans = super::finite_gain::FiniteContactSpans::of(&self.operands, self.opened_at, reach)?;
        let exponents = self
            .producing
            .first_reach(deposit, &spans)?
            .map_err(LandingRefusal::Declared)?;
        *declared = Some(exponents.clone());
        let (theta, publication, committed) = self
            .producing
            .deposited_with_contact_spans_at(deposit, &spans, &exponents)?
            .map_err(LandingRefusal::Declared)?;
        // The transient candidate Word: its own producer, the same opening entered through `θ′`
        // (Rest, or the carry crossed at held momentum; a momentum `θ′` cannot hold refuses), the
        // same source, the same junction steps, receiver, targets and mask.
        let (mut word, _) = Word::open_source_exact_received(
            field,
            &theta,
            &read.current,
            Arc::clone(&read.source),
            opening,
        )?;
        word.run(read.ticks)?;
        let (phases, faces) = word.contact_receiving(receiver)?;
        if phases != read.phases {
            return Err(LandingRefusal::Passage);
        }
        let candidate_ratio =
            HolonRatio::compare_partition(faces, &read.classes, &read.target_phases, compared)?;
        let support = word
            .native_source
            .as_ref()
            .map(|(_, _, _, support)| support.clone())
            .ok_or(HnnError::Realization {
                what: "the candidate Word keeps its source producer",
            })?;
        // Its end and absolute tick, captured before the Word is dropped.
        let end = word.contact_cut()?;
        if end.opened_at != self.opened_at || end.next_tick != self.next_tick {
            return Err(LandingRefusal::Passage);
        }
        let read_candidate = LandingCandidate {
            declared: exponents,
            theta,
            publication,
            committed,
            ratio: candidate_ratio,
            support,
            end: end.change,
            tick: end.next_tick,
        };
        *candidate = Some(read_candidate.clone());
        if read_candidate.support != self.opening_support {
            return Err(LandingRefusal::Support);
        }
        let admitted = admit(ratio, &read_candidate.ratio)?;
        Ok(FiniteDecrease {
            producing: self.producing.clone(),
            source: Arc::clone(&self.source),
            opening: opening.clone(),
            support: self.opening_support.clone(),
            change: self.change.clone(),
            opened_at: self.opened_at,
            next_tick: self.next_tick,
            deposit: deposit.clone(),
            receiver,
            declaration: declaration.clone(),
            targets: targets.clone(),
            compared: compared.to_vec(),
            ratio: ratio.clone(),
            candidate: read_candidate,
            admitted,
        })
    }

    /// Every binding of an admission against this cut's own, typed ([`BindingRefusal`]).
    fn binds(
        &self,
        admission: &FiniteDecrease,
        source: &Arc<SourceMoment>,
        deposit: &Deposit,
    ) -> Result<(), LandingRefusal> {
        if self.held {
            return Err(LandingRefusal::HeldVariation);
        }
        let Some(landing) = &self.landing else {
            return Err(LandingRefusal::Binding(BindingRefusal::ForeignCut));
        };
        let refuse = |refusal: BindingRefusal| -> Result<(), LandingRefusal> {
            Err(LandingRefusal::Binding(refusal))
        };
        if admission.producing != self.producing {
            return refuse(BindingRefusal::Producing);
        }
        if !Arc::ptr_eq(&admission.source, &self.source)
            || !Arc::ptr_eq(source, &self.source)
            || *admission.source != *self.source
        {
            return refuse(BindingRefusal::Source);
        }
        if admission.opening != landing.opening || self.opening.as_ref() != Some(&landing.opening) {
            return refuse(BindingRefusal::Opening);
        }
        if admission.support != self.opening_support
            || admission.candidate.support != self.opening_support
        {
            return refuse(BindingRefusal::Support);
        }
        if admission.change != self.change
            || admission.opened_at != self.opened_at
            || admission.next_tick != self.next_tick
        {
            return refuse(BindingRefusal::Cut);
        }
        if &admission.deposit != deposit || self.deposit.as_ref() != Some(deposit) {
            return refuse(BindingRefusal::Deposit);
        }
        if admission.receiver != landing.receiver || admission.declaration != landing.declaration {
            return refuse(BindingRefusal::Receiver);
        }
        if admission.targets != landing.targets {
            return refuse(BindingRefusal::Targets);
        }
        if admission.compared != landing.compared {
            return refuse(BindingRefusal::Mask);
        }
        if admission.ratio != landing.ratio {
            return refuse(BindingRefusal::Ratio);
        }
        if admission.candidate.tick != self.next_tick {
            return refuse(BindingRefusal::Tick);
        }
        Ok(())
    }
}

/// [definition; agent-inferred, October 9; the held-carry record §3] **One contact-material
/// direction**: the derivatives `δC`, `δK`, `δD` of one contact's forms along a declared parameter
/// direction, in the contact's own coordinates. A factor direction `H` of `C = c cᵀ` reads
/// `δC = H cᵀ + c Hᵀ`; `D` is analogous, and `K = b Σ bᵀ` reads `δK = H Σ bᵀ + b Σ Hᵀ` at the
/// declared signature. The finite factor move's `H Σ Hᵀ` is not a tangent term. `None` is a form the
/// direction leaves fixed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialDirection {
    pub contact: usize,
    pub storage: Option<ExactRatMatrix>,
    pub stiffness: Option<ExactRatMatrix>,
    pub dissipation: Option<ExactRatMatrix>,
}

impl MaterialDirection {
    /// **The transit's material right side** (the held-carry record, eq. 1): the derivative of
    /// `m_a ζ = right` along this direction with the state held,
    /// `r_δ = 2δC (w − ω) − hδD ω − hδK (u + hω/2)`, at the tick's start state `(u, w)` and its
    /// executed midpoint `ω`. Its solve `δζ = m_a⁻¹ r_δ` is the transit's material increment.
    fn right(
        &self,
        step: &Rat,
        displacement: &[Rat],
        rate: &[Rat],
        midpoint: &[Rat],
    ) -> Result<Vec<Rat>, HnnError> {
        let mut right = vec![Rat::zero(); rate.len()];
        if let Some(storage) = &self.storage {
            right = add(
                &right,
                &scale(&integer(2), &storage.apply(&sub(rate, midpoint))?),
            );
        }
        if let Some(dissipation) = &self.dissipation {
            right = sub(&right, &scale(step, &dissipation.apply(midpoint)?));
        }
        if let Some(stiffness) = &self.stiffness {
            let reached = add(displacement, &scale(&(step / integer(2)), midpoint));
            right = sub(&right, &scale(step, &stiffness.apply(&reached)?));
        }
        Ok(right)
    }
}

/// [definition; agent-inferred, October 9; the held-carry record §3, eqs. (1)–(3)] **A contact
/// material's forward tangent, carried beside a Word**: `χ = ∂x/∂θ · H`, the change of the Word's
/// whole state along one material direction, of the change's own shape.
///
/// - **Within the Word** (eq. 2): `χ_(k+1) = T_k χ_k + b_(a,k)`, where `T_k` is the tick's full
///   fixed-operand state map ([`crate::hnn::prediction::physical_signed_tick`]) and `b_(a,k)` the
///   transit's update of its material increment alone (`transit_update` at `δζ` with zero waves and
///   zero state: `b_u = hη`, `b_w = 2η`, the channel's arriving waves `∓δζ/h`, `η = (G/2h)δζ`). The
///   start state `(u_k, w_k)` and midpoint `ω_k` are the Word's own passage record.
/// - **At the opening:** `χ_0 = 0`, the held, parameter-independent opening.
/// - **Across the passage boundary** (eq. 3, [`Self::opened`]): the linear part of
///   [`ReceptionCarry::crossed`] (the arriving waves transmitted at `2G_old/(G_old + G_new)`; the
///   contact and resonator states as carried, because for the same material on both sides the two
///   `δC w` terms cancel, singular `C` included) and every source ring's storage replaced (`Π_int`).
///   No contact factor enters the source opening.
///
/// It retains no Word, event or trajectory: `χ` is overwritten at each tick. The scope is an exact,
/// unsplit Word on fixed operands with nothing deposited or released between the two Words; a
/// lattice Word, a deposited parameter or a nonlinear passage owes its own differential and is
/// refused or out of scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialTangent {
    direction: MaterialDirection,
    /// The producing material commit the direction is based at.
    commit: u64,
    /// The Word's opening tick and the full ticks the tangent has followed.
    opened_at: usize,
    ticks: usize,
    tangent: EndChange,
}

impl MaterialTangent {
    /// **The tangent at a held opening** (`χ_0 = 0`) of an exact, unrun Word, along `direction`,
    /// based at the producing material `commit`.
    pub fn held_opening(
        word: &Word<'_>,
        commit: u64,
        direction: MaterialDirection,
    ) -> Result<Self, HnnError> {
        if word.operands().lattice().is_some() {
            return Err(HnnError::Unadmitted {
                reason: "a material tangent follows an exact, unsplit Word",
            });
        }
        if !word.recorded().is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a material tangent opens with its Word, before any junction step",
            });
        }
        let contacts = word.operands().contacts();
        let contact = contacts
            .get(direction.contact)
            .ok_or(HnnError::Unadmitted {
                reason: "a material direction names a contact of the Word",
            })?;
        let width = contact.width();
        for form in [
            &direction.storage,
            &direction.stiffness,
            &direction.dissipation,
        ]
        .into_iter()
        .flatten()
        {
            if form.rows() != width || form.columns() != width {
                return Err(HnnError::Shape {
                    what: "a material direction's form derivative (the contact's width)",
                    expected: width,
                    found: form.rows(),
                });
            }
        }
        let opening = word.change()?;
        let zero = |v: &Vec<Rat>| vec![Rat::zero(); v.len()];
        let tangent = EndChange {
            storage: opening.storage.iter().map(zero).collect(),
            arrivals: opening
                .arrivals
                .iter()
                .map(|[g, h]| [zero(g), zero(h)])
                .collect(),
            states: opening
                .states
                .iter()
                .map(|[u, w]| [zero(u), zero(w)])
                .collect(),
            resonators: opening
                .resonators
                .iter()
                .map(|state| state.as_ref().map(|[u, w]| [zero(u), zero(w)]))
                .collect(),
            resonator_phases: opening.resonator_phases.clone(),
        };
        Ok(Self {
            direction,
            commit,
            opened_at: word.opened_at(),
            ticks: 0,
            tangent,
        })
    }

    /// **Follow the Word's next full tick** (eq. 2): call after the Word has executed it.
    pub fn step(&mut self, word: &Word<'_>) -> Result<(), HnnError> {
        if word.opened_at() != self.opened_at {
            return Err(HnnError::Unadmitted {
                reason: "a material tangent follows the Word it opened with",
            });
        }
        let k = self.ticks;
        let record = word.recorded().get(k).ok_or(HnnError::Unadmitted {
            reason: "a material tangent follows a full tick the Word has executed",
        })?;
        if record.rates.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a material tangent follows a full tick, not a last junction",
            });
        }
        let operands = word.operands();
        let mut next = crate::hnn::prediction::physical_signed_tick(
            operands,
            &self.tangent,
            self.opened_at + k,
        )?;
        let a = self.direction.contact;
        let contact = &operands.contacts()[a];
        let h = operands.step();
        let [displacement, rate] = &record.states[a];
        let right = self
            .direction
            .right(h, displacement, rate, &record.rates[a])?;
        let solved = contact.solve()?.apply(&right)?;
        let forced = transit_update(
            contact,
            h,
            &solved,
            &vec![Rat::zero(); next.arrivals[a][0].len()],
            &vec![Rat::zero(); next.arrivals[a][1].len()],
            &vec![Rat::zero(); displacement.len()],
            &vec![Rat::zero(); rate.len()],
        );
        next.arrivals[a][0] = add(&next.arrivals[a][0], &forced.arrive_from);
        next.arrivals[a][1] = add(&next.arrivals[a][1], &forced.arrive_to);
        next.states[a][0] = add(&next.states[a][0], &forced.displacement);
        next.states[a][1] = add(&next.states[a][1], &forced.rate);
        self.tangent = next;
        self.ticks += 1;
        Ok(())
    }

    /// The tangent `χ` after the full ticks it has followed: at a Word that ended at a last
    /// junction, the tangent of its reception carry ([`Word::reception_end`]).
    pub fn tangent(&self) -> &EndChange {
        &self.tangent
    }

    pub fn direction(&self) -> &MaterialDirection {
        &self.direction
    }

    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// **The tangent at the next opening** (eq. 3): `χ_open = Π_int B_ref χ_carry`, for a Word
    /// opened on `carry` with the same material, whose contacts take `conductances`. The carry must
    /// be the one this tangent followed (its tick).
    pub fn opened(
        &self,
        carry: &ReceptionCarry,
        conductances: &[Rat],
        field: &Field,
    ) -> Result<EndChange, HnnError> {
        if carry.ticks != self.opened_at + self.ticks {
            return Err(HnnError::Unadmitted {
                reason: "a material tangent crosses with the carry of the ticks it followed",
            });
        }
        if conductances.len() != carry.conductances.len()
            || self.tangent.arrivals.len() != conductances.len()
        {
            return Err(HnnError::Shape {
                what: "the next opening's contacts against the carry's",
                expected: carry.conductances.len(),
                found: conductances.len(),
            });
        }
        let mut crossed = self.tangent.clone();
        for (pair, (from, to)) in crossed
            .arrivals
            .iter_mut()
            .zip(carry.conductances.iter().zip(conductances))
        {
            for wave in pair.iter_mut() {
                *wave = transmitted(wave, from, to);
            }
        }
        Ok(interior_of(field, crossed))
    }

    /// **The delayed material credit** `⟨μ_open, χ_open⟩` (eq. 3): the next Word's full returned
    /// opening covector paired with this tangent crossed into its opening.
    pub fn credit(
        &self,
        carry: &ReceptionCarry,
        conductances: &[Rat],
        field: &Field,
        opening: &ChangeCovector,
    ) -> Result<Rat, HnnError> {
        Ok(opening.pairing(&self.opened(carry, conductances, field)?))
    }
}
