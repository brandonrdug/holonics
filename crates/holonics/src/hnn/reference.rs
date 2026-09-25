//! **The host reference: the exact implementation of the execution port, and the exposure.**
//!
//! [definition] [`Reference`] implements [`ExecutionPort`] exactly (design (c), "The host
//! reference"). Its [`Resident`] holds the field, the lift point, the constitution, the open
//! moments, the open pending ratios and the staged deposits. Every value is in ℚ, in `ℚ(θ)` at a
//! face, or an enclosure read at the exterior; nothing is committed or rounded, and no float exists.
//!
//! [definition] **The resident's clock law** (design (c), R2 M12). `ingest` stops at the joint
//! clock's carry-out and the resident then refuses further cells until `close_aeon`, which it refuses
//! at any other time. Keys are located only between `close_aeon` and the next ingest, from the crib
//! that closed the aeon: at most the closed aeon's own last cells, already ingested and read
//! (review D1; [`crate::hnn::keys::locate_closing`]). Re-keying moves only `λ`'s phase classes and
//! leaves every open moment untouched.
//!
//! [definition] **The compare's composition** ([`compose`]): the word's return
//! ([`crate::hnn::Word::pull_back`]) is carried to every locus:
//!
//! ```text
//! R        sample (P_R^(τ_R) v_R(e_j), −g_j) per receiving phase                   normal law
//! W_c,g    sample (c_t, −u_t) at each tick of the element's window                  normal law
//! E_g      sample (M_g[c], −P^(c−τ_g) s̄_g(0)) per phase with counts                  normal law
//! f_g      G = (K̄ + K̄ᵀ) f,  K̄ = Σ_t u_t x̄_tᵀ;   slices ∂/∂u_ρ = σ_ρ[(x̄·v)u − (u·v)x̄], ∂/∂v_ρ likewise
//! q_g      the class covector g_σρ = Σ_t Re⟨u_t, A_ρ x̄_t⟩ carried to q by the transpose of q ↦ Δ
//! E_g^(δ)  ∂/∂e_ρ = Σ_c w_ρc h_c,  ∂/∂a_ρ = Σ_c (e_ρ·h_c) C_g(δ)[c] b_ρ, ∂/∂b_ρ likewise, h_c = P^(c−τ) s̄(0)
//! c,b,F    C̄ = Σ 2 r̄ (w − ω)ᵀ,  K̄ = −h Σ r̄ (u + ½hω)ᵀ,  D̄ = −h Σ r̄ ωᵀ;  ∂/∂c = (C̄ + C̄ᵀ) c, …
//! ```
//!
//! each only at loci inside the causal diamond of the source rings and the pending ratio's
//! receiver, and each statistic only over the locus's time-indexed window
//! ([`crate::hnn::retention::Diamond`]).
//!
//! [definition] **The Holon, the Holarchy and the aeon at the mount.** A mount is the resident's
//! declaration: it certifies that the field at the mounted constitution is a Holarchy that glues
//! (`Field::holon`, `Holon::interconnect`'s typed gluing, refused with its defect), and it keeps
//! that Holarchy's parametric orientation ([`crate::holarchy::Holarchy::parametric`], the lift of
//! the rings' joint clock torus) as the complex of every aeon it reads. The resident's aeon is an
//! [`crate::aeon::Aeon`] on it, carried by its opening lift point and read at the boundary through
//! the aeon owners ([`crate::hnn::retention::aeon_readings`]).
//!
//! [definition] **The first law over an aeon** ([`crate::aeon::EnclosedLedger`], Lean
//! `Aeon/Production/FirstLaw.{ledger_telescopes, enclosed_telescopes}`). A compare's code length
//! `ℓ_k(Θ_k)` arrives through the unchanged constitution, an exchange step
//! `ℓ_k(Θ_k) − ℓ_(k−1)(Θ_k)` from the occurrence reached; a deposit re-reads the arrived targets at
//! the successor, a deposition step `ℓ_k(Θ_(k+1)) − ℓ_k(Θ_k)`; a collapse that releases a locus the
//! arrived targets' diamond reads re-reads them, the released part counted as exchange (otherwise
//! the collapse changes no admitted reading, exactly). The steps chain, so they telescope to the
//! aeon's change of code length, and `close_aeon` returns the aeon's balance with the face against
//! the literal beside it.
//!
//! [definition] **The exposure** ([`Reference::expose`], design (d), campaign 1's protocol): the cut,
//! exactly the field's declared population (so the `n*` guard holds), is read in order, as one
//! stream, into one moment; at each receiving window `refine` runs on the moment and `compare`
//! against the next `A` cells, whose return is deposited on the training part and discarded on the
//! held-out part; then those cells are ingested; the aeon boundary is the joint clock's carry-out,
//! and after it keys are located on the crib that closed the aeon: its last `W_crib` cells, past
//! and already scored, truncated after the last held-out cell so no held-out cell is read (review
//! D1). The budget stop admits no further deposit and the run continues, reported incomplete. Its
//! readout ([`Exposure`]) is design (f)'s measurement, with `Kt` charging the published keys.

use std::collections::BTreeMap;
use std::ops::Range;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::aeon::{ClockLift, EnclosedLedger};
use crate::compression::cost::ceil_log2;
use crate::geometry::RatVec3;
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    CAMPAIGN_ONE_BUDGET, CarrierBits, Constitution, DepositReading, FactorGradient, FactorStep,
    LinearLocus, LinearStep, Locus, Sample, Steps,
};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::keys::{self, KeyLocation};
use crate::hnn::moment::{Ingested, SourceMoment};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{
    Census, ContactPullback, Deposit, ExecutionPort, Handle, MomentId, PendingId, PortReceipt,
    Pullback, ReceiptDetail, RingPullback, StagedId, Transpose, WordReturn, release_width,
    resonance_reading, source_order,
};
use crate::hnn::propagation::{contact_exponent, path_attenuation};
use crate::hnn::ratio::{
    Faces, HolonRatio, PhaseRatio, interval_sum, log2_enclosure, target_phases,
};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::retention::{AeonBoundary, Diamond, aeon_readings, collapse, contained, separator};
use crate::holon::HolonError;
use crate::holon::contact::FeatureCovector;
use crate::navigator::Clock;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::exponentiated::power_of_two;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale};
use crate::ratio::work::ExactWork;
use crate::ratio::{Rat, integer};
use crate::receiver::receipt::{Receipt, RegionChart};
use crate::receiver::reception::{Component, InteractionReturn, SourceOrder};
use crate::receiver::release::{DecisionRule, LawfulOptions, ReleaseReturn, release};

// -------------------------------------------------------------------------------------------
// the resident

#[derive(Clone, Debug)]
struct PendingSlot {
    ratio: PendingRatio,
    emitted: Vec<Vec<Rat>>,
}

impl PendingSlot {
    /// Its exact bits: the pending ratio's and the emitted logits' (the face a delayed compare
    /// returns its residual against), each value by its numerator's and denominator's bits.
    fn bits(&self) -> u64 {
        self.ratio.bits()
            + self
                .emitted
                .iter()
                .flatten()
                .map(|x| x.numer().bits() + x.denom().bits())
                .sum::<u64>()
    }
}

#[derive(Clone, Debug)]
struct StagedSlot {
    deposit: Deposit,
}

/// [definition] **The first law's arrived operand** (design (c), the resident; guard 3's list of
/// what persists names it): the last compared pending ratio (its producing anchor `λ`, its moment
/// copy `M` and its receiving phases) and its `A` target cells. It is the one operand the ledger's
/// next step reads: a deposit re-reads it at the successor (the deposition step), a collapse that
/// releases a locus its diamond reads re-reads it at the collapsed constitution (the release, an
/// exchange step), and the next compare replaces it. It is bounded (one), counted in
/// [`Resident::state_bits`], and no other method reads it. [agent-inferred] It is kept in the
/// resident rather than in a [`StagedSlot`]: the collapse's re-read needs it after the staged deposit
/// is consumed or discarded.
#[derive(Clone, Debug)]
struct Arrived {
    ratio: PendingRatio,
    targets: Vec<usize>,
}

impl Arrived {
    /// The arrived targets' code length at a constitution.
    fn code_length(
        &self,
        field: &Field,
        constitution: &Constitution,
    ) -> Result<ExactInterval, HnnError> {
        let phases = self.ratio.phases();
        let (_, faces) = self.ratio.read(field, constitution)?;
        let anchors = target_phases(field, self.ratio.anchor(), phases.ring(), &self.targets)?;
        HolonRatio::compare(faces, &self.targets, &anchors)?.code_length()
    }

    fn bits(&self) -> u64 {
        self.ratio.bits()
            + self
                .targets
                .iter()
                .map(|target| BigInt::from(*target).bits() + 1)
                .sum::<u64>()
    }
}

#[derive(Clone, Debug)]
struct AeonState {
    awaiting: bool,
    keys_admitted: bool,
    opening: Vec<BigInt>,
    cells: u64,
    /// The cells the last closed aeon ingested: the most a closing crib may read.
    closed: u64,
}

/// [definition] **The resident of the host reference**: the field, the lift point, the
/// constitution, the open moments, pending ratios and staged deposits, the admitted family of the
/// last boundary, the aeon's clock state on the certified Holarchy's parametric orientation, the
/// first law's ledger with the targets it has reached, the bits the collapses released, and the
/// budget stop once it comes.
#[derive(Clone, Debug)]
pub struct Resident {
    field: Field,
    current: Current,
    constitution: Constitution,
    moments: BTreeMap<MomentId, SourceMoment>,
    pending: BTreeMap<PendingId, PendingSlot>,
    staged: BTreeMap<StagedId, StagedSlot>,
    next: u64,
    admitted: Vec<ReceivingPhases>,
    parametric: ClockLift,
    aeon: AeonState,
    ledger: EnclosedLedger,
    arrived: Option<Arrived>,
    released_bits: u64,
    stop: Option<BudgetStop>,
}

/// [definition] **The budget stop** (design (d), R3 §5): the refused successor's exact bits, the
/// budget, the commit the predecessor stays published at, and the loci that grew most. No further
/// deposit is admitted after it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetStop {
    pub bits: u64,
    pub budget: u64,
    pub commit: u64,
    pub loci: Vec<Locus>,
}

impl BudgetStop {
    fn of(refusal: &HnnError) -> Option<Self> {
        match refusal {
            HnnError::ConstitutionBudget {
                bits,
                budget,
                commit,
                loci,
            } => Some(Self {
                bits: *bits,
                budget: *budget,
                commit: *commit,
                loci: loci.clone(),
            }),
            _ => None,
        }
    }
}

impl Resident {
    pub fn field(&self) -> &Field {
        &self.field
    }

    pub fn current(&self) -> &Current {
        &self.current
    }

    /// The published constitution.
    pub fn constitution(&self) -> &Constitution {
        &self.constitution
    }

    /// The admitted family of the last boundary (the declared receivers before the first).
    pub fn admitted(&self) -> &[ReceivingPhases] {
        &self.admitted
    }

    /// The budget refusal that stopped deposition, once it came.
    pub fn stopped(&self) -> Option<&BudgetStop> {
        self.stop.as_ref()
    }

    /// An open moment.
    pub fn moment(&self, id: &MomentId) -> Option<&SourceMoment> {
        self.moments.get(id)
    }

    /// Whether the joint clock has carried out and the aeon awaits `close_aeon`.
    pub fn awaiting_boundary(&self) -> bool {
        self.aeon.awaiting
    }

    /// **The parametric orientation** of the Holarchy the mount certified: the lift of the rings'
    /// joint clock torus, the complex of every aeon the resident reads.
    pub fn parametric(&self) -> &ClockLift {
        &self.parametric
    }

    /// The first law's ledger over the aeon in progress.
    pub fn ledger(&self) -> &EnclosedLedger {
        &self.ledger
    }

    fn fresh(&mut self) -> u64 {
        self.next += 1;
        self.next
    }

    /// The exact bits of the resident's state: the lift point, the open moments, the pending
    /// ratios with their emitted logits, the staged deposits, the first law's arrived operand and
    /// the constitution.
    pub fn state_bits(&self) -> u64 {
        let lift: u64 = self.current.lift().iter().map(|x| x.bits() + 1).sum();
        let moments: u64 = self.moments.values().map(SourceMoment::dense_bits).sum();
        let pending: u64 = self.pending.values().map(PendingSlot::bits).sum();
        let staged: u64 = self.staged.values().map(|slot| slot.deposit.bits()).sum();
        let arrived = self.arrived.as_ref().map_or(0, Arrived::bits);
        lift + moments + pending + staged + arrived + self.constitution.exact_bits()
    }

    /// **The state's bits without the collapse**: the state's bits plus every locus the collapses
    /// released, at its bits when released. A released locus receives no covector, so without the
    /// collapse it would have stayed exactly as it was (Lean `HNN/Retention.deposit_descends`,
    /// `HNN/LatticeDeposit.carry_zero`) and its bits with it.
    pub fn state_bits_without_collapse(&self) -> u64 {
        self.state_bits() + self.released_bits
    }
}

// -------------------------------------------------------------------------------------------
// the reference

/// [definition] **The exact host reference** of the execution port, with its declared pending
/// capacity, steps and constitution budget.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pending_capacity: usize,
    steps: Steps,
    budget: u64,
}

impl Reference {
    /// Campaign 1's declarations: `γ_U = 1`, `η_x = 1/2`, `B_Θ = 2^33`, and a pending capacity of 64.
    pub fn campaign_one() -> Self {
        Self::new(64, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET)
    }

    pub fn new(pending_capacity: usize, steps: Steps, budget: u64) -> Self {
        Self {
            pending_capacity,
            steps,
            budget,
        }
    }

    /// **Mount on a declared constitution** (a transfer, and the resident's declaration): the field
    /// at the constitution is certified a Holarchy that glues (`Field::holon`, refused with its
    /// gluing defect), whose parametric orientation is the field's joint clock lift and carries the
    /// resident's aeons; the admitted family is the field's declared receivers at that
    /// constitution.
    pub fn mount_with(
        &self,
        field: &Field,
        current: &Current,
        constitution: Constitution,
    ) -> Result<Resident, HnnError> {
        let parametric = field.holon(&constitution)?.parametric();
        if parametric != field.parametric() {
            return Err(HnnError::Shape {
                what: "the Holarchy's parametric orientation against the field's joint clock lift",
                expected: field.rings().len(),
                found: parametric.navigators(),
            });
        }
        let admitted = field
            .receivers()
            .iter()
            .map(|receiver| ReceivingPhases::declare(field, &constitution, current, receiver))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Resident {
            field: field.clone(),
            current: current.clone(),
            constitution,
            moments: BTreeMap::new(),
            pending: BTreeMap::new(),
            staged: BTreeMap::new(),
            next: 0,
            admitted,
            parametric,
            aeon: AeonState {
                awaiting: false,
                keys_admitted: false,
                opening: current.lift().to_vec(),
                cells: 0,
                closed: 0,
            },
            ledger: EnclosedLedger::new(),
            arrived: None,
            released_bits: 0,
            stop: None,
        })
    }
}

/// One-hot exterior cells as their codes.
fn codes(cells: &[Vec<(usize, Rat)>], alphabet: usize) -> Result<Vec<usize>, HnnError> {
    cells
        .iter()
        .enumerate()
        .map(|(position, cell)| match cell.as_slice() {
            [(code, value)] if value.is_one() => {
                if *code >= alphabet {
                    Err(HnnError::CellOutside {
                        code: *code,
                        alphabet,
                    })
                } else {
                    Ok(*code)
                }
            }
            _ => Err(HnnError::CellNotOneHot { position }),
        })
        .collect()
}

/// The exterior chart's one-hot cells of codes.
pub fn one_hot(codes: &[usize]) -> Vec<Vec<(usize, Rat)>> {
    codes.iter().map(|code| vec![(*code, Rat::one())]).collect()
}

/// Per-ring regions in their own clocks: each ring's tick count, a count (clock exponent 0) whose
/// clock unit is the ring's step.
fn ring_receipt(ticks: &[u64], unit: &Rat) -> Result<Receipt, HnnError> {
    let charts = ticks
        .iter()
        .map(|_| RegionChart::new(Rat::one(), unit.clone(), 0))
        .collect::<Result<Vec<_>, HolonError>>()?;
    Ok(Receipt::new(
        ticks
            .iter()
            .map(|t| Rat::from_integer(BigInt::from(*t)))
            .collect(),
        charts,
    )?)
}

fn receipt(
    field: &Field,
    ticks: &[u64],
    unit: &Rat,
    work: ExactWork,
    detail: ReceiptDetail,
) -> Result<PortReceipt, HnnError> {
    let _ = field;
    Ok(PortReceipt {
        rings: ring_receipt(ticks, unit)?,
        balances: Vec::new(),
        work,
        unresolved: Vec::new(),
        detail,
    })
}

fn wrote_all<'a>(work: &mut ExactWork, values: impl IntoIterator<Item = &'a Rat>) {
    for value in values {
        work.wrote(value);
    }
}

impl ExecutionPort for Reference {
    type Resident = Resident;

    fn census(&self) -> Census {
        Census {
            pending_capacity: self.pending_capacity,
            budget: self.budget,
            arithmetic: "exact: ℚ, ℚ(θ) at a face; enclosures only at the exterior",
        }
    }

    fn mount(&self, field: &Field, current: &Current) -> Result<Resident, HnnError> {
        let constitution = Constitution::initial(field, self.steps.clone(), self.budget)?;
        self.mount_with(field, current, constitution)
    }

    fn read(&self, resident: &Resident) -> Result<(Field, Current, Vec<(Handle, u64)>), HnnError> {
        let mut handles: Vec<(Handle, u64)> = resident
            .moments
            .iter()
            .map(|(id, moment)| (Handle::Moment(*id), moment.dense_bits()))
            .collect();
        handles.extend(
            resident
                .pending
                .iter()
                .map(|(id, slot)| (Handle::Pending(*id), slot.bits())),
        );
        handles.extend(
            resident
                .staged
                .iter()
                .map(|(id, slot)| (Handle::Staged(*id), slot.deposit.bits())),
        );
        Ok((resident.field.clone(), resident.current.clone(), handles))
    }

    fn ingest(
        &self,
        resident: &mut Resident,
        moment: Option<&MomentId>,
        cells: &[Vec<(usize, Rat)>],
    ) -> Result<
        (
            MomentId,
            InteractionReturn<Ingested, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        if resident.aeon.awaiting {
            return Err(HnnError::AeonAwaitingClose);
        }
        let field = resident.field.clone();
        let codes = codes(cells, field.alphabet())?;
        let id = match moment {
            Some(id) if resident.moments.contains_key(id) => *id,
            Some(id) => {
                return Err(HnnError::UnknownHandle {
                    handle: Handle::Moment(*id),
                });
            }
            None => {
                let id = MomentId(resident.fresh());
                resident
                    .moments
                    .insert(id, SourceMoment::open(&field, &resident.current));
                id
            }
        };
        let before = resident.current.lift().to_vec();
        let open = resident
            .moments
            .get_mut(&id)
            .expect("the moment was checked or opened");
        let ingested = open.ingest(&field, &mut resident.current, &codes)?;
        if ingested.cells > 0 {
            resident.aeon.keys_admitted = false;
        }
        resident.aeon.cells += ingested.cells as u64;
        if ingested.carry_out {
            resident.aeon.awaiting = true;
        }
        let ticks: Vec<u64> = resident
            .current
            .lift()
            .iter()
            .zip(&before)
            .map(|(after, before)| {
                u64::try_from(after - before).expect("a lift only advances at ingest")
            })
            .collect();
        let n = open.cells();
        let capacity = field.capacity();
        let detail = ReceiptDetail::Ingest {
            cells: ingested.cells as u64,
            moment_bits: open.dense_bits(),
            state_bits: capacity.state_bits(n),
            source_bits: n * ceil_log2(&BigUint::from(field.alphabet())),
            n_star: capacity.n_star(),
            carry_out: ingested.carry_out,
        };
        let mut work = ExactWork::nothing();
        work.resident(open.dense_bits());
        for _ in 0..ingested.cells {
            work.stepped();
        }
        let order = source_order(&field, resident.current.lift(), n);
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(ingested),
                pullback: Component::Absent("ingestion produces no covector"),
                deposit: Component::Absent("ingestion deposits nothing"),
                order: Component::Present(order),
                phases: Component::Absent("nothing is read at ingest"),
                receipt: receipt(&field, &ticks, &Rat::one(), work, detail)?,
            },
        ))
    }

    fn locate_keys(
        &self,
        resident: &mut Resident,
        crib: &[Vec<(usize, Rat)>],
        offset: usize,
    ) -> Result<
        InteractionReturn<KeyLocation, (), Vec<Option<Clock>>, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    > {
        if !resident.aeon.keys_admitted {
            return Err(HnnError::KeysNotAdmitted);
        }
        let field = resident.field.clone();
        let codes = codes(crib, field.alphabet())?;
        if codes.len() as u64 > resident.aeon.closed {
            return Err(HnnError::Shape {
                what: "a closing crib's cells against the closed aeon's",
                expected: usize::try_from(resident.aeon.closed).unwrap_or(usize::MAX),
                found: codes.len(),
            });
        }
        let location = keys::locate_closing(&field, &resident.current, &codes, offset)?;
        let jumps = location.rekey(&field, &mut resident.current)?;
        resident.aeon.opening = resident.current.lift().to_vec();
        // The published ring clocks: each published ring's clock at the boundary, its phase class
        // the carried key and its winding kept; none where the ring fell back.
        let published = location
            .rings
            .iter()
            .map(|ring| match ring.carried {
                Some(_) => field
                    .ring(ring.ring)
                    .clock_at(&resident.current.lift()[ring.ring])
                    .map(Some),
                None => Ok(None),
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let detail = ReceiptDetail::Keys {
            fibres: location.rings.iter().map(|ring| ring.fibre.len()).collect(),
            orbits: location.rings.iter().map(|ring| ring.orbits).collect(),
            fell_back: location.rings.iter().map(|ring| ring.fell_back).collect(),
            failing_loops: location
                .rings
                .iter()
                .map(|ring| ring.failing_loop.clone())
                .collect(),
            candidates: location.rings.iter().map(|ring| ring.seeds).collect(),
            work: location.rings.iter().map(|ring| ring.work).collect(),
            jumps,
        };
        let mut work = ExactWork::nothing();
        for ring in &location.rings {
            work.added(ring.work);
        }
        let order = source_order(&field, resident.current.lift(), codes.len() as u64);
        let zero_ticks = vec![0u64; field.rings().len()];
        Ok(InteractionReturn {
            forward: Component::Present(location),
            pullback: Component::Absent("key location is discrete; the key covector is a reading"),
            deposit: Component::Present(published),
            order: Component::Present(order),
            phases: Component::Absent("nothing is read when keys are located"),
            receipt: receipt(&field, &zero_ticks, &Rat::one(), work, detail)?,
        })
    }

    fn refine(
        &self,
        resident: &mut Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
    ) -> Result<
        (
            PendingId,
            InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        if resident.pending.len() >= self.pending_capacity {
            return Err(HnnError::PendingCapacity {
                capacity: self.pending_capacity,
            });
        }
        let source = resident
            .moments
            .get(moment)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Moment(*moment),
            })?;
        let ratio = PendingRatio::produce(
            &resident.current,
            source,
            phases,
            resident.constitution.commit(),
        );
        let field = &resident.field;
        let (word, faces) = ratio.read(field, &resident.constitution)?;
        let released = word.release()?;
        let path = path_attenuation(
            field,
            ratio.anchor(),
            phases.ring(),
            phases.last_epoch(),
            phases.grain(),
        )?;
        let reached: Vec<Locus> = Diamond::of(field, phases)
            .retained(field)
            .into_iter()
            .filter(|locus| !resident.constitution.released().contains(locus))
            .collect();
        let mut work = ExactWork::nothing();
        wrote_all(&mut work, faces.logits.iter().flatten());
        for _ in 0..released.ticks {
            work.stepped();
        }
        let ticks = vec![released.ticks as u64; field.rings().len()];
        let mut receipt = receipt(
            field,
            &ticks,
            field.step(),
            work,
            ReceiptDetail::Refine {
                reached,
                released_power: released.power.clone(),
                peak_bits: released.peak_bits,
                path,
            },
        )?;
        receipt.balances = released.balances;
        receipt.unresolved = faces.faces.iter().map(|face| face.fibres()).collect();
        let order = source_order(field, ratio.anchor(), ratio.moment().cells());
        let id = PendingId(resident.fresh());
        resident.pending.insert(
            id,
            PendingSlot {
                ratio,
                emitted: faces.logits.clone(),
            },
        );
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(faces),
                pullback: Component::Absent("refine is forward only; its word is dropped"),
                deposit: Component::Absent("refine publishes only faces"),
                order: Component::Present(order),
                phases: Component::Present(vec![phases.clone()]),
                receipt,
            },
        ))
    }

    fn compare(
        &self,
        resident: &mut Resident,
        pending: PendingId,
        target: &[Vec<(usize, Rat)>],
    ) -> Result<
        (
            StagedId,
            InteractionReturn<HolonRatio, Pullback, Deposit, Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        // Everything is read from the borrowed pending ratio; it is consumed only once the compare
        // has succeeded, so a refused target or a refused read leaves it open (review S11).
        let field = resident.field.clone();
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        let targets = codes(target, field.alphabet())?;
        let phases = slot.ratio.phases().clone();
        if targets.len() != phases.aperture() {
            return Err(HnnError::Shape {
                what: "targets against the aperture",
                expected: phases.aperture(),
                found: targets.len(),
            });
        }
        let ratio = &slot.ratio;
        let (word, faces) = ratio.read(&field, &resident.constitution)?;
        let residual: Vec<Vec<Rat>> = faces
            .logits
            .iter()
            .zip(&slot.emitted)
            .map(|(now, then)| now.iter().zip(then).map(|(a, b)| a - b).collect())
            .collect();
        let anchors = target_phases(&field, ratio.anchor(), phases.ring(), &targets)?;
        let holon = HolonRatio::compare(faces, &targets, &anchors)?;
        let covector = holon.covector()?;
        let map = resident
            .constitution
            .receiving_map(phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?
            .clone();
        let back = word.pull_back(&covector, &map, &ratio.anchor()[phases.ring()], &phases)?;
        let (pullback, deposit) = compose(&field, &resident.constitution, ratio, &back)?;
        let code_length = holon.code_length()?;
        let order = source_order(&field, ratio.anchor(), ratio.moment().cells());
        let mut work = ExactWork::nothing();
        wrote_all(&mut work, covector.logits().iter().flatten());
        wrote_all(&mut work, back.opening.iter().flatten());
        let detail = ReceiptDetail::Compare {
            code_length: code_length.clone(),
            excess: holon.excess(),
            windings: holon.phases().iter().map(PhaseRatio::winding).collect(),
            residual,
            reached: deposit.loci(),
        };
        let steps = phases.junction_steps() as u64;
        let ticks = vec![steps; field.rings().len()];
        let mut port_receipt = receipt(&field, &ticks, field.step(), work, detail)?;
        port_receipt.unresolved = holon
            .faces()
            .faces
            .iter()
            .map(|face| face.fibres())
            .collect();
        let Some(PendingSlot { ratio, .. }) = resident.pending.remove(&pending) else {
            return Err(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            });
        };
        resident.ledger.arrive(code_length, targets.len() as u64);
        let id = StagedId(resident.fresh());
        resident.staged.insert(
            id,
            StagedSlot {
                deposit: deposit.clone(),
            },
        );
        resident.arrived = Some(Arrived { ratio, targets });
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(holon),
                pullback: Component::Present(pullback),
                deposit: Component::Present(deposit),
                order: Component::Present(order),
                phases: Component::Present(vec![phases]),
                receipt: port_receipt,
            },
        ))
    }

    fn deposit(
        &self,
        resident: &mut Resident,
        staged: StagedId,
    ) -> Result<
        InteractionReturn<(), (), DepositReading, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    > {
        if resident.stop.is_some() {
            return Err(HnnError::DepositsStopped {
                commit: resident.constitution.commit(),
            });
        }
        let slot = resident
            .staged
            .get(&staged)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Staged(staged),
            })?;
        let field = resident.field.clone();
        // The deposition step's operand: the arrived targets, re-read at the successor.
        let arrived = resident.arrived.as_ref().ok_or(HnnError::Shape {
            what: "the arrived targets a staged deposit was compared on",
            expected: 1,
            found: 0,
        })?;
        let (next, reading) = match resident.constitution.deposited(&slot.deposit) {
            Ok(published) => published,
            Err(refusal @ HnnError::ConstitutionBudget { .. }) => {
                resident.staged.remove(&staged);
                resident.stop = BudgetStop::of(&refusal);
                return Err(refusal);
            }
            Err(refusal) => return Err(refusal),
        };
        // Every fallible step is taken on the successor before anything is published, so a refusal
        // leaves the predecessor, the ledger and the staged deposit as they were (review S12).
        let reread = arrived.code_length(&field, &next)?;
        let mut work = ExactWork::nothing();
        work.stepped();
        work.resident(reading.bits);
        let zero_ticks = vec![0u64; field.rings().len()];
        let port_receipt = receipt(
            &field,
            &zero_ticks,
            &Rat::one(),
            work,
            ReceiptDetail::Deposit {
                reading: reading.clone(),
                reread: reread.clone(),
            },
        )?;
        // The ledger's step refuses before it moves (`EnclosedLedger::deposit`).
        resident.ledger.deposit(reread)?;
        resident.staged.remove(&staged);
        resident.constitution = next;
        Ok(InteractionReturn {
            forward: Component::Present(()),
            pullback: Component::Absent("a deposit consumes covectors"),
            deposit: Component::Present(reading),
            order: Component::Absent("a deposit leaves the source order unchanged"),
            phases: Component::Absent("nothing is read by a deposit"),
            receipt: port_receipt,
        })
    }

    fn release(
        &self,
        resident: &mut Resident,
        pending: &PendingId,
        decision: &DecisionRule,
    ) -> Result<InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError> {
        let slot = resident
            .pending
            .get(pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(*pending),
            })?;
        let field = &resident.field;
        let phases = slot.ratio.phases().clone();
        let current = slot.ratio.current(field)?;
        let mut word = slot.ratio.open(field, &resident.constitution)?;
        let anchors = word.forward(&phases)?;
        let reads = anchors
            .iter()
            .map(|anchor| phases.read(field, &resident.constitution, &current, anchor))
            .collect::<Result<Vec<_>, _>>()?;
        let faces = Faces::of_reads(&reads, phases.grain())?;
        // The width is read from the receiving phases' fibres; the tolerance is their grain.
        let width = release_width(&phases, &faces)?;
        let tolerance = Rat::new(BigInt::one(), BigInt::from(phases.grain()));
        let options = LawfulOptions::assemble(&width, tolerance.clone(), None, None, false)?;
        let decided = release(decision, &options)?;
        let released = matches!(decided, ReleaseReturn::Released { .. });
        let split = match anchors.last() {
            Some(anchor) => resonance_reading(field.ring(phases.ring()), anchor)?,
            None => [
                Component::Absent("the window read no anchor"),
                Component::Absent("the window read no anchor"),
            ],
        };
        let order = source_order(field, slot.ratio.anchor(), slot.ratio.moment().cells());
        let ticks = vec![phases.junction_steps() as u64; field.rings().len()];
        let mut port_receipt = receipt(
            field,
            &ticks,
            field.step(),
            ExactWork::nothing(),
            ReceiptDetail::Release {
                width,
                tolerance,
                decision: decided,
                split,
            },
        )?;
        port_receipt.unresolved = faces.faces.iter().map(|face| face.fibres()).collect();
        Ok(InteractionReturn {
            forward: if released {
                Component::Present(faces)
            } else {
                Component::Absent("the declared rule did not release at this receiver")
            },
            pullback: Component::Absent("release is forward only"),
            deposit: Component::Absent("FOUND is campaign 3's; the RIDE/FOUND split is a reading"),
            order: Component::Present(order),
            phases: Component::Present(vec![phases]),
            receipt: port_receipt,
        })
    }

    fn close_aeon(
        &self,
        resident: &mut Resident,
        admitted: &[ReceivingPhases],
    ) -> Result<
        InteractionReturn<
            AeonBoundary,
            Vec<(PendingId, Transpose)>,
            (),
            Vec<ReceivingPhases>,
            PortReceipt,
        >,
        HnnError,
    > {
        if !resident.aeon.awaiting {
            return Err(HnnError::NotAtCarryOut);
        }
        contained(admitted, &resident.admitted)?;
        let before = resident.state_bits();
        let field = resident.field.clone();
        let collapsed = collapse(&field, &mut resident.constitution, admitted)?;
        let mut carried = Vec::new();
        let mut refused = Vec::new();
        let mut transposes = Vec::new();
        let ids: Vec<PendingId> = resident.pending.keys().copied().collect();
        for id in ids {
            let phases = resident.pending[&id].ratio.phases();
            let separating = separator(&field, phases, &collapsed.retained);
            if separating.is_empty() {
                // `Vᵀ` on the carried ratio: the retained loci its diamond reads.
                let reads: Vec<Locus> = Diamond::of(&field, phases)
                    .retained(&field)
                    .into_iter()
                    .filter(|locus| collapsed.retained.contains(locus))
                    .collect();
                transposes.push((id, Transpose::Retained(reads)));
                carried.push(id);
            } else {
                resident.pending.remove(&id);
                transposes.push((id, Transpose::Separator(separating.clone())));
                refused.push((id, separating));
            }
        }
        // A staged deposit that reaches a released locus is refused with the loci it would reach,
        // and discarded; the others are carried (design (c): `close_aeon` carries every open handle
        // or refuses it).
        let mut refused_staged = Vec::new();
        resident.staged.retain(|id, slot| {
            let separating: Vec<Locus> = slot
                .deposit
                .loci()
                .into_iter()
                .filter(|locus| !collapsed.retained.contains(locus))
                .collect();
            if separating.is_empty() {
                true
            } else {
                refused_staged.push((*id, separating));
                false
            }
        });
        resident.released_bits += collapsed.bits[0].saturating_sub(collapsed.bits[1]);
        // The first law across the collapse: it changes no admitted reading, so the arrived
        // targets read alike unless their own diamond reads a locus it newly released; then the
        // released part is an exchange step.
        if let Some(arrived) = &resident.arrived {
            let reads = Diamond::of(&field, arrived.ratio.phases()).retained(&field);
            if collapsed.released.iter().any(|locus| reads.contains(locus)) {
                let reread = arrived.code_length(&field, &resident.constitution)?;
                resident.ledger.release(reread)?;
            }
        }
        let first_law = resident.ledger.close();
        let literal = first_law.against_literal(&log2_enclosure(&Rat::from_integer(
            BigInt::from(field.alphabet()),
        ))?);
        let opening = resident.aeon.opening.clone();
        let carry_out = resident.current.lift().to_vec();
        let (readings, epochs, closing) =
            aeon_readings(&resident.parametric, &opening, &carry_out)?;
        let cells = resident.aeon.cells;
        resident.aeon = AeonState {
            awaiting: false,
            keys_admitted: true,
            opening: carry_out.clone(),
            cells: 0,
            closed: cells,
        };
        resident.admitted = admitted.to_vec();
        let after = resident.state_bits();
        let boundary = AeonBoundary {
            admitted: admitted.to_vec(),
            collapse: collapsed,
            value_kernel: Component::Absent(
                "the value kernel of a frozen aeon is campaign 3's; campaign 1 aeons all learn",
            ),
            opening,
            carry_out,
            readings: readings.clone(),
            epochs,
            closing,
            cells,
            first_law,
            literal,
            view: Component::Absent(
                "the field's Holarchy glues its rings and contacts at their ports, with no glued cell \
                 complex, so no receiver has regions to view or count; owed with the cellular gluing",
            ),
            carried,
            refused,
            refused_staged,
            state_bits: [before, after],
        };
        let zero_ticks = vec![0u64; field.rings().len()];
        Ok(InteractionReturn {
            forward: Component::Present(boundary),
            pullback: Component::Present(transposes),
            deposit: Component::Absent("the released loci are the boundary's collapse"),
            order: Component::Present(SourceOrder {
                rings: readings,
                cells,
            }),
            phases: Component::Present(admitted.to_vec()),
            receipt: receipt(
                &field,
                &zero_ticks,
                &Rat::one(),
                ExactWork::nothing(),
                ReceiptDetail::Boundary,
            )?,
        })
    }

    fn discard(
        &self,
        resident: &mut Resident,
        handle: Handle,
    ) -> Result<InteractionReturn<(), (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError> {
        let bits = match handle {
            Handle::Moment(id) => resident.moments.remove(&id).map(|m| m.dense_bits()),
            Handle::Pending(id) => resident.pending.remove(&id).map(|s| s.bits()),
            Handle::Staged(id) => resident.staged.remove(&id).map(|s| s.deposit.bits()),
        }
        .ok_or(HnnError::UnknownHandle { handle })?;
        let zero_ticks = vec![0u64; resident.field.rings().len()];
        Ok(InteractionReturn {
            forward: Component::Present(()),
            pullback: Component::Absent("a discard returns nothing"),
            deposit: Component::Absent("a discard deposits nothing"),
            order: Component::Absent("a discard leaves the source order unchanged"),
            phases: Component::Absent("nothing is read by a discard"),
            receipt: receipt(
                &resident.field,
                &zero_ticks,
                &Rat::one(),
                ExactWork::nothing(),
                ReceiptDetail::Discard { bits },
            )?,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the compare's composition

fn negated(values: &[Rat]) -> Vec<Rat> {
    values.iter().map(|x| -x).collect()
}

fn matrix_of(rows: Vec<Vec<Rat>>, columns: usize) -> Result<ExactRatMatrix, HnnError> {
    Ok(ExactRatMatrix::shaped(rows.len(), columns, rows)?)
}

/// **The compare's composition** (module header): the complete pullback and the deposit staged
/// inside the pending ratio's causal diamond.
///
/// [definition; agent-inferred] **Its exact chart.** Each gradient is a sum of rank-one terms over
/// the word's ticks (`Σ_t u_t x̄_tᵀ`, `Σ_t 2 r̄_t (w − ω)_tᵀ`, the slices' `σ[(x̄·v)u − (u·v)x̄]`, …)
/// whose vectors carry the word's large common denominators. Each tick's vectors are read once in
/// the integral chart (integers over their least common denominator), the sums are formed over
/// integers on one common denominator, and each entry is normalized once
/// ([`crate::ratio::linear::vector::IntegralMatrix`]). A reduced ratio is canonical, so every entry
/// equals the termwise rational sum. The offset counts enter the pair port through their nonzero
/// slots only, summed over the small counts as `C_c b_ρ`, `C_cᵀ a_ρ` and `a_ρᵀ C_c b_ρ` before the
/// word's `e_ρ·h_c` and `h_c` multiply them (distributivity over ℚ).
pub fn compose(
    field: &Field,
    constitution: &Constitution,
    ratio: &PendingRatio,
    back: &WordReturn,
) -> Result<(Pullback, Deposit), HnnError> {
    use crate::ratio::linear::vector::{
        Chart, IntegralMatrix, combination, integer_dot, integral, lcm,
    };
    let phases = ratio.phases();
    let diamond = Diamond::of(field, phases);
    let released = constitution.released();
    let retained = |locus: Locus| diamond.retains(field, locus) && !released.contains(&locus);
    let anchor = ratio.anchor();
    let current = ratio.current(field)?;
    let moment = ratio.moment();
    let alphabet = field.alphabet();
    let h = field.step().clone();
    let mut linear: Vec<LinearStep> = Vec::new();
    let mut factors: Vec<FactorStep> = Vec::new();
    let one = Rat::one();

    // The receiving map: Σ_j g_j ⊗ P_R^(τ_R) v_R(e_j).
    let receiving = phases.ring();
    let width_r = field.ring(receiving).width();
    let read_charts: Vec<[Chart; 2]> = back
        .reads
        .iter()
        .map(|(feature, gradient)| [integral(gradient), integral(feature)])
        .collect();
    let map_gradient = IntegralMatrix::outer_sum(
        2 * alphabet,
        width_r,
        read_charts
            .iter()
            .map(|[gradient, feature]| (&one, gradient, feature)),
    )
    .to_rows();
    let samples = back
        .reads
        .iter()
        .map(|(feature, gradient)| Sample {
            weight: one.clone(),
            feature: feature.clone(),
            covector: negated(gradient),
        })
        .collect();
    linear.push(LinearStep {
        locus: LinearLocus::Receiving(receiving),
        samples,
    });

    // The rings' element material and class covectors.
    let mut ring_pullbacks = Vec::with_capacity(field.rings().len());
    let mut classes_all: Vec<Vec<Rat>> = Vec::with_capacity(field.rings().len());
    let mut midpoint_energy: Vec<Rat> = Vec::with_capacity(field.rings().len());
    for g in 0..field.rings().len() {
        let n = field.ring(g).width();
        let passive = constitution.passive_factor(g);
        let slices = constitution.slices(g);
        let ticks = &back.elements[g];
        // The sheet classes this word read.
        let sheets = sheet_classes(field, constitution, g)?;
        // Each tick's adjoint `u`, midpoint `x̄` and contrast `c`, read once in the integral chart.
        let charts: Vec<[Chart; 3]> = ticks
            .iter()
            .map(|tick| {
                [
                    integral(&tick.adjoint),
                    integral(&tick.midpoint),
                    integral(&tick.contrast),
                ]
            })
            .collect();
        // K̄ = Σ_t u_t x̄_tᵀ and the contrast port's Σ_t u_t c_tᵀ.
        let element_gradient =
            IntegralMatrix::outer_sum(n, n, charts.iter().map(|[u, x, _]| (&one, u, x)));
        let contrast_gradient =
            IntegralMatrix::outer_sum(n, n, charts.iter().map(|[u, _, c]| (&one, u, c))).to_rows();
        // The classes `Σ_t (u·s)(x̄·v) − (u·v)(x̄·s)` and the slices' gradients
        // `σ Σ_t [(x̄·v)u − (u·v)x̄]`, `σ Σ_t [(u·s)x̄ − (x̄·s)u]`, on the common denominator
        // `D = lcm_t(d_u d_x̄)` of the ticks' `u x̄ᵀ`.
        let common = charts
            .iter()
            .fold(BigInt::one(), |d, [u, x, _]| lcm(&d, &(&u.1 * &x.1)));
        let lifted: Vec<(Vec<BigInt>, Vec<BigInt>)> = charts
            .iter()
            .map(|[u, x, _]| {
                let factor = &common / (&u.1 * &x.1);
                (
                    u.0.iter().map(|value| value * &factor).collect(),
                    x.0.iter().map(|value| value * &factor).collect(),
                )
            })
            .collect();
        let mut classes = vec![Rat::zero(); n];
        let mut slice_gradient = Vec::with_capacity(slices.len());
        for (rho, (su, sv)) in slices.iter().enumerate() {
            let ((su, d_su), (sv, d_sv)) = (integral(su), integral(sv));
            let mut du = vec![BigInt::zero(); n];
            let mut dv = vec![BigInt::zero(); n];
            for ([u, x, _], (u_lift, x_lift)) in charts.iter().zip(&lifted) {
                let (u_su, x_sv, u_sv, x_su) = (
                    integer_dot(&u.0, &su),
                    integer_dot(&x.0, &sv),
                    integer_dot(&u.0, &sv),
                    integer_dot(&x.0, &su),
                );
                classes[rho] +=
                    Rat::new(&u_su * &x_sv - &u_sv * &x_su, &u.1 * &x.1 * &d_su * &d_sv);
                if !(x_sv.is_zero() && u_sv.is_zero()) {
                    for (entry, (ui, xi)) in du.iter_mut().zip(u_lift.iter().zip(x_lift)) {
                        *entry += &x_sv * ui - &u_sv * xi;
                    }
                }
                if !(u_su.is_zero() && x_su.is_zero()) {
                    for (entry, (ui, xi)) in dv.iter_mut().zip(u_lift.iter().zip(x_lift)) {
                        *entry += &u_su * xi - &x_su * ui;
                    }
                }
            }
            let signed = |value: BigInt| if sheets[rho] { value } else { -value };
            slice_gradient.push((
                du.into_iter()
                    .map(|value| Rat::new(signed(value), &common * &d_sv))
                    .collect::<Vec<Rat>>(),
                dv.into_iter()
                    .map(|value| Rat::new(signed(value), &common * &d_su))
                    .collect::<Vec<Rat>>(),
            ));
        }
        let mut energy = Rat::zero();
        let mut contrast_samples = Vec::new();
        for tick in ticks {
            if diamond.element_window(g, tick.tick) {
                energy += dot(&tick.midpoint, &tick.midpoint);
                contrast_samples.push(Sample {
                    weight: one.clone(),
                    feature: tick.contrast.clone(),
                    covector: negated(&tick.adjoint),
                });
            }
        }
        // K = −f fᵀ + …: ∂ℓ/∂f = −(K̄ + K̄ᵀ) f.
        let passive_gradient = element_gradient.symmetric_times(passive, true)?;
        let window = ticks
            .iter()
            .any(|tick| diamond.element_window(g, tick.tick));
        if retained(Locus::Element(g)) && window {
            linear.push(LinearStep {
                locus: LinearLocus::Contrast(g),
                samples: contrast_samples,
            });
            factors.push(FactorStep {
                gradient: FactorGradient::Passive {
                    ring: g,
                    gradient: matrix_of(
                        passive_gradient.iter().map(|row| negated(row)).collect(),
                        passive.columns(),
                    )?,
                },
                energy: energy.clone(),
            });
            factors.push(FactorStep {
                gradient: FactorGradient::Slices {
                    ring: g,
                    gradient: slice_gradient
                        .iter()
                        .map(|(du, dv)| (negated(du), negated(dv)))
                        .collect(),
                },
                energy: energy.clone(),
            });
        }
        ring_pullbacks.push(RingPullback {
            ring: g,
            passive: matrix_of(passive_gradient, passive.columns())?,
            contrast: matrix_of(contrast_gradient, n)?,
            slices: slice_gradient,
            classes: classes.clone(),
            standing: Vec::new(),
            source: None,
            pair: Vec::new(),
            moment: None,
        });
        classes_all.push(classes);
        midpoint_energy.push(energy);
    }

    // The standing, through the declared lock chart: Δ = M q with the contrast map `M`, which is
    // symmetric, so ∂ℓ/∂q = Mᵀ g_σ = M g_σ ([`Field::contrast`]).
    let class_fields: Vec<&[Rat]> = classes_all.iter().map(Vec::as_slice).collect();
    for g in 0..field.rings().len() {
        let standing = field.contrast(g, &class_fields)?;
        if retained(Locus::Standing(g)) {
            factors.push(FactorStep {
                gradient: FactorGradient::Standing {
                    ring: g,
                    gradient: negated(&standing),
                },
                energy: midpoint_energy[g].clone(),
            });
        }
        ring_pullbacks[g].standing = standing;
    }

    // The source rings: E_g, E_g^(δ) and the moment's covector.
    for &g in field.sources() {
        let ring = field.ring(g);
        let n = ring.width();
        let d = ring.placements().len();
        let opening = &back.opening[g];
        let turned: Vec<Vec<Rat>> = (0..d)
            .map(|c| ring.rotate(opening, &(BigInt::from(c) - &anchor[g])))
            .collect();
        let turned_charts: Vec<Chart> = turned.iter().map(|h| integral(h)).collect();
        let source = constitution
            .source_port(g)
            .ok_or(HnnError::MissingSourcePort { ring: g })?;
        let gradient = moment.encoder_covector(field, &current, g, opening)?;
        let source_t = source.transpose()?;
        let moment_covector = turned
            .iter()
            .map(|h| source_t.apply(h))
            .collect::<Result<Vec<_>, _>>()?;
        let mut source_samples = Vec::new();
        for (c, h) in turned.iter().enumerate() {
            let counts = moment.phase_counts(g, c)?;
            if counts.iter().all(|x| *x == 0) {
                continue;
            }
            source_samples.push(Sample {
                weight: one.clone(),
                feature: counts
                    .iter()
                    .map(|x| Rat::from_integer(BigInt::from(*x)))
                    .collect(),
                covector: negated(h),
            });
        }
        let mut pair_pullbacks = Vec::new();
        let mut pair_steps = Vec::new();
        for &offset in field.offsets() {
            let pair = constitution
                .pair_port(g, offset)
                .ok_or(HnnError::MissingSourcePort { ring: g })?;
            let rank = pair.rank();
            // The nonzero offset counts of each phase `(x, y, C_c[x, y])`, read once.
            let mut nonzero: Vec<Vec<(usize, usize, Rat)>> = Vec::with_capacity(d);
            let mut squares = BigInt::zero();
            for c in 0..d {
                let counts = moment.offset_counts(g, offset, c)?;
                let mut slots = Vec::new();
                for (slot, &count) in counts.iter().enumerate() {
                    if count == 0 {
                        continue;
                    }
                    let count = BigInt::from(count);
                    squares += &count * &count;
                    slots.push((slot / alphabet, slot % alphabet, Rat::from_integer(count)));
                }
                nonzero.push(slots);
            }
            let energy = Rat::from_integer(squares);
            let mut outputs = Vec::with_capacity(rank);
            let mut current_reads = Vec::with_capacity(rank);
            let mut earlier_reads = Vec::with_capacity(rank);
            for rho in 0..rank {
                let (a_rho, b_rho, e_rho) = (
                    &pair.current_reads()[rho],
                    &pair.earlier_reads()[rho],
                    &pair.outputs()[rho],
                );
                // Per phase: w_ρc = a_ρᵀ C_c b_ρ, C_c b_ρ (by the current cell) and C_cᵀ a_ρ (by
                // the earlier cell), over the small counts.
                let mut weights = Vec::with_capacity(d);
                let mut by_current: Vec<(Rat, Chart)> = Vec::with_capacity(d);
                let mut by_earlier: Vec<(Rat, Chart)> = Vec::with_capacity(d);
                for (slots, h) in nonzero.iter().zip(&turned) {
                    let mut weight = Rat::zero();
                    let e_h = dot(e_rho, h);
                    let mut current_row = vec![Rat::zero(); alphabet];
                    let mut earlier_row = vec![Rat::zero(); alphabet];
                    for (x, y, count) in slots {
                        weight += count * &a_rho[*x] * &b_rho[*y];
                        if !e_h.is_zero() {
                            current_row[*x] += count * &b_rho[*y];
                            earlier_row[*y] += count * &a_rho[*x];
                        }
                    }
                    weights.push(weight);
                    if !e_h.is_zero() {
                        by_current.push((e_h.clone(), integral(&current_row)));
                        by_earlier.push((e_h, integral(&earlier_row)));
                    }
                }
                current_reads.push(combination(
                    alphabet,
                    by_current.iter().map(|(weight, chart)| (weight, chart)),
                ));
                earlier_reads.push(combination(
                    alphabet,
                    by_earlier.iter().map(|(weight, chart)| (weight, chart)),
                ));
                outputs.push(combination(n, weights.iter().zip(&turned_charts)));
            }
            pair_steps.push(FactorStep {
                gradient: FactorGradient::PairPort {
                    ring: g,
                    offset,
                    outputs: outputs.iter().map(|x| negated(x)).collect(),
                    current: current_reads.iter().map(|x| negated(x)).collect(),
                    earlier: earlier_reads.iter().map(|x| negated(x)).collect(),
                },
                energy,
            });
            pair_pullbacks.push((offset, [outputs, current_reads, earlier_reads]));
        }
        if retained(Locus::SourcePort(g)) {
            linear.push(LinearStep {
                locus: LinearLocus::SourcePort(g),
                samples: source_samples,
            });
            factors.extend(pair_steps);
        }
        ring_pullbacks[g].source = Some(gradient);
        ring_pullbacks[g].pair = pair_pullbacks;
        ring_pullbacks[g].moment = Some(moment_covector);
    }

    // The contacts: their channel factors, conductance and pair geometry.
    let mut contact_pullbacks = Vec::with_capacity(field.contacts().len());
    let (two, minus_h, half_h) = (integer(2), -h.clone(), &h / integer(2));
    for (a, contact) in field.contacts().iter().enumerate() {
        let k = contact.width();
        let mut energies = [Rat::zero(), Rat::zero(), Rat::zero()];
        let mut window = false;
        // Each tick's r̄, slip w − ω, strain u + ½hω and ω, read once in the integral chart.
        let mut charts: Vec<[Chart; 4]> = Vec::with_capacity(back.transits[a].len());
        for tick in &back.transits[a] {
            let (r, u, w, omega) = (&tick.solved, &tick.displacement, &tick.rate, &tick.midpoint);
            let slip: Vec<Rat> = w.iter().zip(omega).map(|(w, o)| w - o).collect();
            let strain = add(u, &scale(&half_h, omega));
            if diamond.channel_window(field, a, tick.tick) {
                window = true;
                energies[0] += dot(&slip, &slip);
                energies[1] += dot(&strain, &strain);
                energies[2] += dot(omega, omega);
            }
            charts.push([
                integral(r),
                integral(&slip),
                integral(&strain),
                integral(omega),
            ]);
        }
        // C̄ = Σ 2 r̄ (w − ω)ᵀ,  K̄ = −h Σ r̄ (u + ½hω)ᵀ,  D̄ = −h Σ r̄ ωᵀ.
        let storage =
            IntegralMatrix::outer_sum(k, k, charts.iter().map(|[r, slip, ..]| (&two, r, slip)));
        let stiffness = IntegralMatrix::outer_sum(
            k,
            k,
            charts.iter().map(|[r, _, strain, _]| (&minus_h, r, strain)),
        );
        let dissipation = IntegralMatrix::outer_sum(
            k,
            k,
            charts.iter().map(|[r, .., omega]| (&minus_h, r, omega)),
        );
        let pulled = [
            storage.symmetric_times(constitution.contact_storage(a), false)?,
            stiffness.symmetric_times(constitution.contact_stiffness(a), false)?,
            dissipation.symmetric_times(constitution.contact_dissipation(a), false)?,
        ];
        if retained(Locus::Channel(a)) && window {
            let columns = [
                constitution.contact_storage(a).columns(),
                constitution.contact_stiffness(a).columns(),
                constitution.contact_dissipation(a).columns(),
            ];
            let descent = |index: usize| {
                matrix_of(
                    pulled[index].iter().map(|row| negated(row)).collect(),
                    columns[index],
                )
            };
            factors.push(FactorStep {
                gradient: FactorGradient::Storage {
                    contact: a,
                    gradient: descent(0)?,
                },
                energy: energies[0].clone(),
            });
            factors.push(FactorStep {
                gradient: FactorGradient::Stiffness {
                    contact: a,
                    gradient: descent(1)?,
                },
                energy: energies[1].clone(),
            });
            factors.push(FactorStep {
                gradient: FactorGradient::Dissipation {
                    contact: a,
                    gradient: descent(2)?,
                },
                energy: energies[2].clone(),
            });
        }
        // λ_Q: G_a = 2^(−β Q / 2) Y_a, so ∂ℓ/∂Q = −(β/2) G_a λ_G in units of ln 2.
        let exponent = contact_exponent(field, a, anchor)?;
        let conductance = power_of_two(&exponent.carry)? * contact.admittance();
        let quadrance = -(contact.exponent() / integer(2)) * &conductance * &back.conductance[a];
        let feature = FeatureCovector {
            delta: RatVec3::zero(),
            quadrance,
            gradient: [Rat::zero(), Rat::zero()],
        };
        let key = contact.pair(field, anchor).feature_pullback(&feature)?;
        let [storage, stiffness, dissipation] = pulled;
        contact_pullbacks.push(ContactPullback {
            contact: a,
            feature,
            conductance: back.conductance[a].clone(),
            storage: matrix_of(storage, constitution.contact_storage(a).columns())?,
            stiffness: matrix_of(stiffness, constitution.contact_stiffness(a).columns())?,
            dissipation: matrix_of(dissipation, constitution.contact_dissipation(a).columns())?,
            key,
        });
    }

    let reached: Vec<Locus> = crate::hnn::retention::loci(field)
        .into_iter()
        .filter(|locus| retained(*locus))
        .collect();
    let pullback = Pullback {
        rings: ring_pullbacks,
        contacts: contact_pullbacks,
        receiving: (receiving, matrix_of(map_gradient, width_r)?),
    };
    Ok((
        pullback,
        Deposit::new(constitution.commit(), linear, factors, reached),
    ))
}

/// The sheet classes `σ_ρ = sign(Δ_r[ρ])` (`sign 0 = +1`) of ring `g`'s standing contrast
/// ([`Field::standing_contrast`]).
fn sheet_classes(
    field: &Field,
    constitution: &impl ConstitutionRead,
    g: usize,
) -> Result<Vec<bool>, HnnError> {
    Ok(field
        .standing_contrast(constitution, g)?
        .iter()
        .map(|x| *x >= Rat::zero())
        .collect())
}

// -------------------------------------------------------------------------------------------
// the exposure

/// [definition] **A cut**: the exterior stream's codes in order, and its pinned held-out positions
/// (compared and reported, never deposited).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cut {
    pub cells: Vec<usize>,
    pub held_out: Vec<Range<usize>>,
}

impl Cut {
    fn held_out(&self, position: usize) -> bool {
        self.held_out.iter().any(|range| range.contains(&position))
    }

    /// **The crib that closed an aeon at cell `at`**: at most `window` cells before `at`, none
    /// before the aeon's opening `start`, and none at or before a held-out cell, so the crib holds
    /// only cells already read and never a held-out one (review D1).
    pub(crate) fn closing_crib(&self, start: usize, at: usize, window: usize) -> Range<usize> {
        let mut from = at.saturating_sub(window).max(start);
        for range in &self.held_out {
            if range.start < at && range.end > from {
                from = from.max(range.end.min(at));
            }
        }
        from..at
    }
}

/// [definition] **Bits on a population of targets**: the model's code length on its committed
/// faces and the online baselines' (uniform; order-0 and order-1 with the Krichevsky–Trofimov prior;
/// PPM of order [`PPM_ORDER`] with escape rule C), each an enclosure, over `cells` targets. xz and
/// zstd, with their description cost, are exterior codecs: the crate runs no process, so they are
/// owed to the application, computed there on the same cut and joined to this report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bits {
    pub model: ExactInterval,
    pub uniform: ExactInterval,
    pub order_zero: ExactInterval,
    pub order_one: ExactInterval,
    pub ppm: ExactInterval,
    pub cells: u64,
}

impl Bits {
    fn empty() -> Self {
        let zero = ExactInterval::point(Rat::zero());
        Self {
            model: zero.clone(),
            uniform: zero.clone(),
            order_zero: zero.clone(),
            order_one: zero.clone(),
            ppm: zero,
            cells: 0,
        }
    }
}

/// [definition] **One key location of the exposure**: the cell it ran at, and per ring the fibre's
/// size, orbits, failing loop and fallback, with each ring's re-keying jump.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyReport {
    pub cell: u64,
    pub detail: ReceiptDetail,
}

/// [definition] **The state against the source, in bits**: the lift point, the open moment, the
/// constitution, and the whole resident with and without the collapse
/// ([`Resident::state_bits_without_collapse`]: equal on a field inside one diamond, review D6); the
/// moment's `⌈log₂N(n)⌉` and dense bits against the source's `n ⌈log₂|A|⌉`, with `n*`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateReport {
    pub lift_bits: u64,
    pub moment_bits: u64,
    pub moment_state_bits: u64,
    pub constitution_bits: u64,
    pub resident_bits: u64,
    pub resident_bits_without_collapse: u64,
    pub source_bits: u64,
    pub n_star: u64,
}

/// [definition] **One point of the constitution's curve** (design (f) item 4): the commit reached,
/// the constitution's exact bits by carrier (lattice entries, carried remainders, solved charts),
/// and what the deposit that reached it released (its residuals' exact bits) and stepped (the
/// entries whose lattice coordinate moved). The mount's point releases and steps nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurvePoint {
    pub commit: u64,
    pub bits: CarrierBits,
    pub released_bits: u64,
    pub stepped: u64,
}

/// [definition] **The exposure's readout** (design (f)): bits on the training and held-out targets
/// against the baselines, the key reports, each aeon boundary (its length, collapse, readings,
/// first law and the face against the literal), the constitution's bits per deposit by carrier with
/// each deposit's released and stepped entries, the receiving windows whose source-to-receiver path
/// was open at their cut against all windows read (the refine receipt's located cause, review C2),
/// the peak bits of the change inside any word, the budget stop, the description bits (`Field::describe`, the constitution's declared steps, budget and
/// the pending capacity included), the located keys' bits (`⌈log₂ d_g⌉` per published key: the
/// model pays for what learning located) and `Kt = |describe| + key bits + L_target|model +
/// ⌈log₂ work⌉` against the literal, the work counted and the state against the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exposure {
    pub training: Bits,
    pub held_out: Bits,
    pub keys: Vec<KeyReport>,
    pub aeons: Vec<AeonBoundary>,
    pub constitution_curve: Vec<CurvePoint>,
    pub windows: u64,
    pub open_windows: u64,
    pub peak_word_bits: u64,
    pub stop: Option<(BudgetStop, u64)>,
    pub complete: bool,
    pub description_bits: u64,
    pub key_bits: u64,
    pub kt: ExactInterval,
    pub literal_bits: u64,
    pub work: ExactWork,
    pub state: StateReport,
    pub compares: u64,
    pub deposits: u64,
}

/// The online Krichevsky–Trofimov code length of one cell, `−log₂((count + ½)/(total + |A|/2))`.
fn kt_bits(count: u64, total: u64, alphabet: usize) -> Result<ExactInterval, HnnError> {
    let probability = Rat::new(
        BigInt::from(2 * count + 1),
        BigInt::from(2 * total) + BigInt::from(alphabet),
    );
    log2_enclosure(&probability.recip())
}

/// [definition; agent-inferred] **The PPM baseline's declared order**: two context cells, the
/// least order above the order-1 baseline beside it.
pub const PPM_ORDER: usize = 2;

/// [definition] **Prediction by partial matching, exact and online** (Cleary and Witten; escape
/// rule C of Moffat): the counts of each symbol after each context of up to `order` cells, all
/// orders updated after each cell. A cell is coded from the longest context down: at a context
/// with counts `n_s` over the symbols not yet excluded, total `n` and `d` distinct, a seen symbol
/// has mass `n_s/(n + d)` and the escape `d/(n + d)`, which excludes those symbols below; a context
/// never seen escapes with mass one; below order 0 the declared prior is uniform over the symbols
/// not excluded. The cell's mass is the exact rational product, and its code length is enclosed.
#[derive(Clone, Debug)]
pub struct Ppm {
    order: usize,
    alphabet: usize,
    tables: Vec<BTreeMap<Vec<usize>, BTreeMap<usize, u64>>>,
    history: Vec<usize>,
}

impl Ppm {
    pub fn new(order: usize, alphabet: usize) -> Self {
        Self {
            order,
            alphabet,
            tables: vec![BTreeMap::new(); order + 1],
            history: Vec::new(),
        }
    }

    /// **The exact mass of the next cell** under the counts so far.
    pub fn mass(&self, symbol: usize) -> Rat {
        let mut mass = Rat::one();
        let mut excluded: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        for k in (0..=self.order.min(self.history.len())).rev() {
            let context = &self.history[self.history.len() - k..];
            let Some(counts) = self.tables[k].get(context) else {
                continue;
            };
            let (mut total, mut distinct) = (0u64, 0u64);
            for (seen, count) in counts {
                if !excluded.contains(seen) {
                    total += count;
                    distinct += 1;
                }
            }
            if total == 0 {
                continue;
            }
            let denominator = BigInt::from(total + distinct);
            if let Some(count) = counts.get(&symbol).filter(|_| !excluded.contains(&symbol)) {
                return mass * Rat::new(BigInt::from(*count), denominator);
            }
            mass *= Rat::new(BigInt::from(distinct), denominator);
            excluded.extend(counts.keys().copied());
        }
        mass * Rat::new(
            BigInt::one(),
            BigInt::from(self.alphabet.saturating_sub(excluded.len()).max(1)),
        )
    }

    /// Count one cell at every order and extend the history.
    pub fn update(&mut self, symbol: usize) {
        for k in 0..=self.order.min(self.history.len()) {
            let context = self.history[self.history.len() - k..].to_vec();
            *self.tables[k]
                .entry(context)
                .or_default()
                .entry(symbol)
                .or_insert(0) += 1;
        }
        self.history.push(symbol);
        if self.history.len() > self.order {
            self.history.remove(0);
        }
    }

    /// **The cell's code length** `−log₂ P`, enclosed, then its count.
    pub fn code(&mut self, symbol: usize) -> Result<ExactInterval, HnnError> {
        let bits = log2_enclosure(&self.mass(symbol).recip())?;
        self.update(symbol);
        Ok(bits)
    }
}

/// The exposure's online baselines, fitted on the same stream in the same order.
struct Baselines {
    alphabet: usize,
    uniform: ExactInterval,
    order_zero: Vec<u64>,
    order_one: BTreeMap<(usize, usize), u64>,
    order_one_totals: Vec<u64>,
    previous: Option<usize>,
    seen: u64,
    ppm: Ppm,
}

impl Baselines {
    fn new(alphabet: usize) -> Result<Self, HnnError> {
        Ok(Self {
            alphabet,
            uniform: log2_enclosure(&Rat::from_integer(BigInt::from(alphabet)))?,
            order_zero: vec![0; alphabet],
            order_one: BTreeMap::new(),
            order_one_totals: vec![0; alphabet],
            previous: None,
            seen: 0,
            ppm: Ppm::new(PPM_ORDER, alphabet),
        })
    }

    /// Count one cell in the Krichevsky–Trofimov baselines.
    fn count(&mut self, code: usize) {
        let context = self.previous.unwrap_or(0);
        self.order_zero[code] += 1;
        *self.order_one.entry((context, code)).or_insert(0) += 1;
        self.order_one_totals[context] += 1;
        self.previous = Some(code);
        self.seen += 1;
    }

    /// Count one cell in every baseline.
    fn update(&mut self, code: usize) {
        self.count(code);
        self.ppm.update(code);
    }

    /// Code one cell in every baseline into `bits`, then count it.
    fn code(&mut self, bits: &mut Bits, code: usize) -> Result<(), HnnError> {
        let context = self.previous.unwrap_or(0);
        bits.uniform = interval_sum(&bits.uniform, &self.uniform)?;
        bits.order_zero = interval_sum(
            &bits.order_zero,
            &kt_bits(self.order_zero[code], self.seen, self.alphabet)?,
        )?;
        bits.order_one = interval_sum(
            &bits.order_one,
            &kt_bits(
                self.order_one.get(&(context, code)).copied().unwrap_or(0),
                self.order_one_totals[context],
                self.alphabet,
            )?,
        )?;
        bits.ppm = interval_sum(&bits.ppm, &self.ppm.code(code)?)?;
        bits.cells += 1;
        self.count(code);
        Ok(())
    }
}

impl Reference {
    /// **Run campaign 1's exposure protocol on a cut** and read its measurement (module header).
    /// The admitted family is the field's declared receivers throughout. Refused unless the cut is
    /// exactly the field's declared population, which `Field::declare` checked against `n*`.
    pub fn expose(&self, field: &Field, cut: &Cut) -> Result<Exposure, HnnError> {
        if cut.cells.len() as u64 != field.population() {
            return Err(HnnError::Shape {
                what: "the cut's cells against the declared population",
                expected: usize::try_from(field.population()).unwrap_or(usize::MAX),
                found: cut.cells.len(),
            });
        }
        let mut resident = self.mount(field, &Current::at_rest(field))?;
        let phases = resident
            .admitted()
            .first()
            .cloned()
            .ok_or(HnnError::Shape {
                what: "a declared receiver for the exposure",
                expected: 1,
                found: 0,
            })?;
        let family = resident.admitted().to_vec();
        let aperture = phases.aperture();
        let alphabet = field.alphabet();
        let crib = field.crib();
        let cells = &cut.cells;
        let mut keys = Vec::new();
        let mut locate = |resident: &mut Resident, span: Range<usize>| -> Result<(), HnnError> {
            if span.len() > crib.offset {
                let at = span.end as u64;
                let located = self.locate_keys(resident, &one_hot(&cells[span]), crib.offset)?;
                keys.push(KeyReport {
                    cell: at,
                    detail: located.receipt.detail,
                });
            }
            Ok(())
        };
        let (moment, _) = self.ingest(&mut resident, None, &[])?;
        let mut aeon_start = 0usize;
        let mut training = Bits::empty();
        let mut held_out = Bits::empty();
        let mut baselines = Baselines::new(alphabet)?;
        let mut aeons = Vec::new();
        let mut curve = vec![CurvePoint {
            commit: resident.constitution().commit(),
            bits: resident.constitution().carrier_bits(),
            released_bits: 0,
            stepped: 0,
        }];
        let (mut windows, mut open_windows, mut peak_word_bits) = (0u64, 0u64, 0u64);
        let mut stop = None;
        let mut work = ExactWork::nothing();
        let (mut compares, mut deposits) = (0u64, 0u64);
        let mut position = 0usize;
        while position < cells.len() {
            let end = (position + aperture).min(cells.len());
            let window = &cells[position..end];
            if window.len() == aperture {
                let (pending, refined) = self.refine(&mut resident, &moment, &phases)?;
                work = work.then(&refined.receipt.work);
                if let ReceiptDetail::Refine {
                    path, peak_bits, ..
                } = &refined.receipt.detail
                {
                    windows += 1;
                    open_windows += u64::from(path.open);
                    peak_word_bits = peak_word_bits.max(*peak_bits);
                }
                let (staged, compared) = self.compare(&mut resident, pending, &one_hot(window))?;
                work = work.then(&compared.receipt.work);
                compares += 1;
                let holon = compared
                    .forward
                    .into_present()
                    .expect("a compare returns its ratio");
                let windowed = window
                    .iter()
                    .enumerate()
                    .any(|(offset, _)| cut.held_out(position + offset));
                for (offset, (phase, &code)) in holon.phases().iter().zip(window).enumerate() {
                    let bits = if cut.held_out(position + offset) {
                        &mut held_out
                    } else {
                        &mut training
                    };
                    bits.model = interval_sum(&bits.model, &phase.code_length)?;
                    baselines.code(bits, code)?;
                }
                if windowed || resident.stopped().is_some() {
                    self.discard(&mut resident, Handle::Staged(staged))?;
                } else {
                    match self.deposit(&mut resident, staged) {
                        Ok(returned) => {
                            work = work.then(&returned.receipt.work);
                            deposits += 1;
                            let (released_bits, stepped) = returned
                                .deposit
                                .present()
                                .map_or((0, 0), |reading| (reading.released_bits, reading.stepped));
                            curve.push(CurvePoint {
                                commit: resident.constitution().commit(),
                                bits: resident.constitution().carrier_bits(),
                                released_bits,
                                stepped,
                            });
                        }
                        Err(refusal @ HnnError::ConstitutionBudget { .. }) => {
                            stop = BudgetStop::of(&refusal).map(|stop| (stop, position as u64));
                        }
                        Err(other) => return Err(other),
                    }
                }
            } else {
                for &code in window {
                    baselines.update(code);
                }
            }
            let mut fed = 0;
            while fed < window.len() {
                let (_, ingested) =
                    self.ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))?;
                let ingested = ingested.forward.into_present().expect("ingest returns");
                fed += ingested.cells;
                if ingested.carry_out {
                    let closed = self.close_aeon(&mut resident, &family)?;
                    aeons.push(closed.forward.into_present().expect("a boundary"));
                    let at = position + fed;
                    locate(&mut resident, cut.closing_crib(aeon_start, at, crib.window))?;
                    aeon_start = at;
                }
            }
            position = end;
        }
        let description_bits = field
            .describe(&self.steps, self.budget, self.pending_capacity)
            .len() as u64;
        let key_bits: u64 = keys
            .iter()
            .map(|report| match &report.detail {
                ReceiptDetail::Keys { fell_back, .. } => field
                    .rings()
                    .iter()
                    .zip(fell_back)
                    .filter(|(_, fell)| !**fell)
                    .map(|(ring, _)| ceil_log2(&BigUint::from(ring.period())))
                    .sum(),
                _ => 0,
            })
            .sum();
        let model_bits = interval_sum(&training.model, &held_out.model)?;
        let counted = work.entries_written.clone().max(BigUint::one());
        let kt = interval_sum(
            &model_bits,
            &ExactInterval::point(Rat::from_integer(BigInt::from(
                description_bits + key_bits + ceil_log2(&counted),
            ))),
        )?;
        let open = resident.moment(&moment).expect("the exposure's moment");
        let n = open.cells();
        let symbol = ceil_log2(&BigUint::from(alphabet));
        let state = StateReport {
            lift_bits: resident.current().lift().iter().map(|x| x.bits() + 1).sum(),
            moment_bits: open.dense_bits(),
            moment_state_bits: field.capacity().state_bits(n),
            constitution_bits: resident.constitution().exact_bits(),
            resident_bits: resident.state_bits(),
            resident_bits_without_collapse: resident.state_bits_without_collapse(),
            source_bits: n * symbol,
            n_star: field.capacity().n_star(),
        };
        Ok(Exposure {
            training,
            held_out,
            keys,
            aeons,
            constitution_curve: curve,
            windows,
            open_windows,
            peak_word_bits,
            complete: stop.is_none(),
            stop,
            description_bits,
            key_bits,
            kt,
            literal_bits: symbol * cells.len() as u64,
            work,
            state,
            compares,
            deposits,
        })
    }
}
