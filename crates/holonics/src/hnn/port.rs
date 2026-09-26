//! **The execution port: the verbs every backend implements, and the word's return.**
//!
//! [definition] [`ExecutionPort`] is the trait the host reference ([`crate::hnn::Reference`]) and,
//! in step 5, the CUDA and Apple backends implement (design (c)). Its resident owns the field, the
//! lift point, the open moments, the open pending ratios and the staged deposits; the caller holds
//! only handles ([`MomentId`], [`PendingId`], [`StagedId`], [`Handle`]). `refine` and `release`
//! borrow a pending ratio; `compare` and `deposit` consume their handle when they succeed (a
//! refusal leaves it open and the resident as it was, except the budget stop, which consumes the
//! refused deposit), and `discard` consumes it; `close_aeon` carries every open handle or refuses
//! it (a pending ratio with its separator, a staged deposit with the released loci it reaches).
//!
//! [definition] **Every method returns the owner's [`InteractionReturn`]** (design addition 6,
//! review F1), with the six components #73 requires: the forward field, the complete geometry and
//! feature pullback, the material return, the source order, the receiving phase and the receipt
//! ([`PortReceipt`]). A component a method does not produce is a declared
//! [`Component::Absent`] with its reason, never a default value.
//!
//! | Method | Forward | Pullback | Material return | Source order | Receiving phase | Receipt |
//! |---|---|---|---|---|---|---|
//! | `ingest` | the moment extended; `λ` stepped | absent | absent | the lift, `n` | absent | cells, moment bits against `n*`, the carry-out |
//! | `locate_keys` | the fibres per ring, from the crib that closed the aeon | absent (discrete; the key covector is a reading) | the published ring clocks ([`Clock`] at the boundary, winding kept; none where a ring fell back) | the crib's edges | absent | fibres, orbits, failing loops, work |
//! | `refine` | the faces `p̂_j` | absent (forward only) | absent | the moment's lift | the binding read | ticks, balances (each with its residual and certified bound), diamond, the released change, the charts' certificates, the released remainders |
//! | `compare` | the [`HolonRatio`] | the complete [`Pullback`] | a [`Deposit`] | the anchor's | the pending binding | KL, excess, winding, residual, loci, the return's released remainders |
//! | `deposit` | the successor constitution | absent | the applied [`DepositReading`] | unchanged | absent | work, `ε_k` product, commit, bits against `B_Θ` |
//! | `release` | the released face, or a declared absence when the rule holds | absent | absent (FOUND is campaign 3's) | the anchor's | the pending binding | the width read from the receiving phases' fibres against the grain, the rule's decision, the RIDE/FOUND split |
//! | `close_aeon` | the [`AeonBoundary`] (its collapse names the released loci and their remainders; the staged deposits it refuses) | the transpose of `V` per pending ratio, or its separator ([`Transpose`]) | absent (the released loci are the boundary's collapse) | the aeon readings | the admitted family | the boundary |
//! | `discard` | the handle removed | absent | absent | unchanged | absent | bits freed |
//!
//! [definition; agent-inferred] **The release's width is read from its receiving phases**
//! ([`release_width`]): the receiver reads each class's exponent at its grain `L_R`, and reading
//! every exponent within its cell moves each code length by at most the largest fibre `ε_c`
//! (Lean `HNN/Ratio.face_code_length_within_grain`), so the certified width of the released code
//! lengths over the receiver's fibre is `max_(j, c) ε_c < 1/L_R`, the tolerance its grain declares.
//! It is zero exactly when every logit sits on its cell's representative. The RIDE/FOUND split of
//! the receiving ring's last anchor against the ring's parametron is a reading
//! ([`resonance_reading`], `compression::resonance_split`); campaign 1's unit-weight rings have a
//! singular capacity (their cycle Laplacian), so the split is a declared absence until campaign 2
//! declares `C_g`.

//! [definition] **The word's return** ([`Word::pull_back`]): the ratio's covector `R⁻¹dR` on the
//! logits pulled back through `R` and `P_R^(τ_R)` to the receiving anchors, then through the ticks
//! in reverse over the word's own per-tick waves, to the opening storage. It claims no inverse of a
//! step (design R2 H2): each reverse step is the transpose of the linear map that tick executed at
//! its fixed operands (the junctions' executed weights, the lattice charts of `(I − ½K_r)⁻¹` and
//! `m_a⁻¹`: the executed adjoint, Lean `HNN/LatticeWord.executed_adjoint_unique`, never an exact
//! inverse), composed in reverse order, its own transients carried on the word's lattice with error
//! feedback and their remainders released at the open ([`WordReturn::released`]; Decision 24) (Lean
//! `HolonicAdjointNormalization.dualMap_comp_reverse_order`, `HNN/Word.reaction_stage_adjoint`,
//! `HNN/Propagation.{trajectory_pairing, word_variation_exact, covector_causal_cone}`, proved on the
//! abstract block operator; the concrete-tick bridge is owed in #62).
//! It accepts only a [`RatioCovector`], which only a [`HolonRatio`] constructs (guard 10):
//!
//! ```compile_fail,E0308
//! use holonics::hnn::{ReceivingPhases, Word};
//! use holonics::ratio::Rat;
//! use holonics::ratio::linear::ExactRatMatrix;
//! use num_bigint::BigInt;
//! // A scalar loss or a bare vector is not an operand of the return (guard 10).
//! fn scalar(word: Word<'_>, loss: Vec<Vec<Rat>>, map: &ExactRatMatrix, phases: &ReceivingPhases) {
//!     let _ = word.pull_back(&loss, map, &BigInt::from(0), phases);
//! }
//! ```
//!
//! The per-tick samples it returns are indexed by tick, not by occurrence, and live only in the
//! return that consumes the word.

use num_bigint::BigInt;
use num_traits::Zero;

use crate::aeon::Reading;
use crate::compression::{CompressionError, ResonanceSplit, resonance_split};
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartReading, Remainders, carry};
use crate::hnn::constitution::{DepositReading, FactorStep, Lattice, LinearStep, Locus};
use crate::hnn::field::{Current, Field, Ring};
use crate::hnn::keys::KeyLocation;
use crate::hnn::moment::Ingested;
use crate::hnn::propagation::{PathAttenuation, TickBalance, swing_about};
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector};
use crate::hnn::realization::{apply_rows, entries, indexed};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::retention::AeonBoundary;
use crate::hnn::word::Word;
use crate::holon::contact::FeatureCovector;
use crate::navigator::Clock;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{dot, scale, sub};
use crate::ratio::work::ExactWork;
use crate::ratio::{Rat, integer};
use crate::receiver::face::{DiameterNorm, ReceiverWidth, WidthWitness};
use crate::receiver::receipt::Receipt;
use crate::receiver::reception::{InteractionReturn, SourceOrder};
use crate::receiver::release::{DecisionRule, ReleaseReturn};

use crate::receiver::reception::Component;

// -------------------------------------------------------------------------------------------
// handles

/// A handle to an open [`crate::hnn::SourceMoment`] in the resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MomentId(pub(crate) u64);

/// A handle to an open [`crate::hnn::PendingRatio`] in the resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PendingId(pub(crate) u64);

/// A handle to a staged [`Deposit`] in the resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StagedId(pub(crate) u64);

/// Any handle the resident holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Handle {
    Moment(MomentId),
    Pending(PendingId),
    Staged(StagedId),
}

// -------------------------------------------------------------------------------------------
// the return

/// **The source order of a lift point** after `cells` cells: each ring's lift read in turns of its
/// period, the owner's split into windings and open phase (`aeon::Reading`, Lean
/// `Aeon/Clock/Winding.reading_split`). It is the reading of the ring's own clock over the aeon
/// from the lift's origin (`reading_navigatorClock`); the word is not built, since the reading is
/// the displacement.
pub fn source_order(field: &Field, lift: &[BigInt], cells: u64) -> SourceOrder {
    SourceOrder {
        rings: field
            .rings()
            .iter()
            .zip(lift)
            .map(|(ring, tau)| {
                Reading::of_turns(&Rat::new(tau.clone(), BigInt::from(ring.period())))
            })
            .collect(),
        cells,
    }
}

/// [definition] **What a method's receipt reads beyond the common fields**, one arm per method.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptDetail {
    /// `ingest`: cells accessed, the moment's dense bits and its source-state bits `⌈log₂N(n)⌉`
    /// against the source's `n ⌈log₂|A|⌉`, `n*`, and whether the joint clock carried out.
    Ingest {
        cells: u64,
        moment_bits: u64,
        state_bits: u64,
        source_bits: u64,
        n_star: u64,
        carry_out: bool,
    },
    /// `locate_keys`: per ring the fibre's size, its orbits, whether it fell back, its minimal
    /// failing loop, the candidates checked and the propagation work; and each ring's jump.
    Keys {
        fibres: Vec<usize>,
        orbits: Vec<usize>,
        fell_back: Vec<bool>,
        failing_loops: Vec<Option<Vec<usize>>>,
        candidates: Vec<u64>,
        work: Vec<u64>,
        jumps: Vec<i64>,
    },
    /// `refine`: the diamond's retained loci, the change's power released at the word's end, its
    /// peak bits inside the word, the source-to-receiver path attenuation at the cut (review C2), so
    /// a shielded receiver is reported as a located cause; and (Decision 24) every executed chart's
    /// reading (its certificate against the target, its refinement's steps and seed), the carried
    /// remainders the word released at its end, and the last junction's residual.
    Refine {
        reached: Vec<Locus>,
        released_power: Rat,
        peak_bits: u64,
        path: PathAttenuation,
        charts: Vec<ChartReading>,
        remainders: Remainders,
        last: Rat,
    },
    /// `compare`: the window's code length (the KL part, enclosed), phase excess, each phase's
    /// winding, the residual against the emitted logits, the loci reached, and the remainders the
    /// return's carried adjoint released at the open (Decision 24).
    Compare {
        code_length: crate::ratio::algebraic::ExactInterval,
        excess: Rat,
        windings: Vec<BigInt>,
        residual: Vec<Vec<Rat>>,
        reached: Vec<Locus>,
        released: Remainders,
    },
    /// `deposit`: the applied reading and the re-read code length of the deposit's own targets at
    /// the successor (the first law's deposition term).
    Deposit {
        reading: DepositReading,
        reread: crate::ratio::algebraic::ExactInterval,
    },
    /// `release`: the width read from the receiving phases' fibres against the grain, the declared
    /// rule's decision, and the RIDE/FOUND split of the receiving ring's last anchor, its real and
    /// imaginary parts (a reading; a declared absence where the ring's capacity is singular).
    Release {
        width: ReceiverWidth,
        tolerance: Rat,
        decision: ReleaseReturn,
        split: [Component<ResonanceSplit>; 2],
    },
    /// `close_aeon`: the boundary is the forward component.
    Boundary,
    /// `discard`: the bits freed.
    Discard { bits: u64 },
}

/// [definition] **A method's receipt**: per-ring regions in their own clocks (each ring's tick count
/// as a count, its clock unit the ring's step), each full tick's power balance, the work counted,
/// the receivers' fibres, and the method's detail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortReceipt {
    pub rings: Receipt,
    pub balances: Vec<TickBalance>,
    pub work: ExactWork,
    pub unresolved: Vec<Vec<Rat>>,
    pub detail: ReceiptDetail,
}

/// [definition] **The boundary's pullback of one pending ratio** (design (c), `close_aeon`): the
/// transpose of `V` on it, the retained loci its diamond reads, onto which its covectors pull back
/// by `Vᵀ` (the inclusion of the retained loci); or, when it reads a released locus, its separator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transpose {
    Retained(Vec<Locus>),
    Separator(Vec<Locus>),
}

/// **The release's width, read from its receiving phases** (module header): over the window's
/// faces, the largest fibre `ε_c`, the certified bound on how far any code length moves over the
/// receiver's fibre (Lean `HNN/Ratio.face_code_length_within_grain`), in the supremum norm and
/// attained at the widest `(phase, class)` coordinate; zero, attained at a point, when every logit
/// sits on its cell's representative.
pub fn release_width(phases: &ReceivingPhases, faces: &Faces) -> Result<ReceiverWidth, HnnError> {
    let mut widest: Option<(usize, Rat)> = None;
    let mut coordinate = 0;
    for face in &faces.faces {
        for fibre in face.fibres() {
            if widest.as_ref().is_none_or(|(_, width)| &fibre > width) {
                widest = Some((coordinate, fibre));
            }
            coordinate += 1;
        }
    }
    let (diameter, attaining) = match widest {
        Some((coordinate, width)) if !width.is_zero() => {
            (width, WidthWitness::Coordinate { coordinate })
        }
        _ => (Rat::zero(), WidthWitness::Point),
    };
    ReceiverWidth::declared(
        format!("receiving ring {}", phases.ring()),
        "the code lengths of the pending ratio's faces over the receiver's fibre at its grain",
        DiameterNorm::Supremum,
        diameter,
        attaining,
        coordinate.max(1),
    )
    .map_err(HnnError::from)
}

/// **The RIDE/FOUND split of a ring's anchor, as a reading** (design (a), "Release through modes";
/// `compression::resonance_split`): the anchor's real and imaginary node parts, each split against
/// the ring's parametron at its exchange eigenvalue `ω² = W_K / W_C` (declared by proportional
/// branch weights). A singular capacity, or weights with no single exchange eigenvalue, is a
/// declared absence; nothing is pseudo-inverted.
pub fn resonance_reading(
    ring: &Ring,
    anchor: &[Rat],
) -> Result<[Component<ResonanceSplit>; 2], HnnError> {
    if anchor.len() != ring.width() {
        return Err(HnnError::Shape {
            what: "a ring's anchor",
            expected: ring.width(),
            found: anchor.len(),
        });
    }
    let parametron = ring.parametron();
    let (capacity, stiffness) = (parametron.capacity(), parametron.inverse_inductance());
    let eigenvalue = match (capacity.first(), stiffness.first()) {
        (Some(c), Some(k)) if !c.is_zero() => {
            let ratio = k / c;
            capacity
                .iter()
                .zip(stiffness)
                .all(|(c, k)| k == &(&ratio * c))
                .then_some(ratio)
        }
        _ => None,
    };
    let Some(eigenvalue) = eigenvalue else {
        return Ok([
            Component::Absent("the ring's weights declare no single exchange eigenvalue"),
            Component::Absent("the ring's weights declare no single exchange eigenvalue"),
        ]);
    };
    let part = |offset: usize| -> Result<Component<ResonanceSplit>, HnnError> {
        let drive: Vec<Rat> = anchor.iter().skip(offset).step_by(2).cloned().collect();
        match resonance_split(parametron, &drive, &eigenvalue) {
            Ok(split) => Ok(Component::Present(split)),
            Err(CompressionError::SingularCapacity) => Ok(Component::Absent(
                "the ring's capacity C_g = Bᵀ W_C B is singular (campaign 1's unit-weight cycle); \
                 the split is refused, not pseudo-inverted, until campaign 2 declares C_g",
            )),
            Err(refusal) => Err(refusal.into()),
        }
    };
    Ok([part(0)?, part(1)?])
}

/// [definition] **The backend's own census**: the pending capacity it admits, the declared
/// constitution budget, and its arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Census {
    pub pending_capacity: usize,
    pub budget: u64,
    pub arithmetic: &'static str,
}

// -------------------------------------------------------------------------------------------
// the pullback and the deposit

/// [definition] **One ring's pullback**: the gradients of the ratio's log on its element material
/// (the passive factor, the contrast port, the slices), its sheet-class covector
/// `g_σρ = Σ_t Re⟨u_t, A_ρ x̄_t⟩`, its standing through the declared lock chart, and on a source
/// ring its source ports and the covector on its moment `M_g[c]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingPullback {
    pub ring: usize,
    pub passive: ExactRatMatrix,
    pub contrast: ExactRatMatrix,
    pub slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub classes: Vec<Rat>,
    pub standing: Vec<Rat>,
    pub source: Option<ExactRatMatrix>,
    pub pair: Vec<(usize, [Vec<Vec<Rat>>; 3])>,
    pub moment: Option<Vec<Vec<Rat>>>,
}

/// [definition] **One contact's pullback**: its feature covector `(λ_Δ, λ_Q, λ_DQ)` (campaign 1's
/// word reads the pair only through `Q`, so `λ_Δ = 0` and `λ_DQ = 0`; `λ_Q` is carried in units of
/// `ln 2`, a declared factor), the conductance covector `λ_G`, the gradients on its channel factors,
/// and the key covector's reading: the pair's return to its two screws' parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactPullback {
    pub contact: usize,
    pub feature: FeatureCovector,
    pub conductance: Rat,
    pub storage: ExactRatMatrix,
    pub stiffness: ExactRatMatrix,
    pub dissipation: ExactRatMatrix,
    pub key: [Rat; 2],
}

/// [definition] **The complete geometry and feature pullback** of a compare (design (c),
/// `Pullback`): per ring, per contact, and the receiving map `R`. Gradients of the ratio's log
/// (`∂ℓ/∂·`); the key covector is a reading only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pullback {
    pub rings: Vec<RingPullback>,
    pub contacts: Vec<ContactPullback>,
    pub receiving: (usize, ExactRatMatrix),
}

/// [definition] **The staged material return** (design (c), `Deposit`): keyed by locus, inside the
/// causal diamond of the source rings and the receiver, at the constitution commit it was computed
/// at. Only a compare builds one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deposit {
    commit: u64,
    linear: Vec<LinearStep>,
    factors: Vec<FactorStep>,
    reached: Vec<Locus>,
}

impl Deposit {
    pub(crate) fn new(
        commit: u64,
        linear: Vec<LinearStep>,
        factors: Vec<FactorStep>,
        reached: Vec<Locus>,
    ) -> Self {
        Self {
            commit,
            linear,
            factors,
            reached,
        }
    }

    /// The constitution commit the deposit was computed at.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// The linear loci's windows.
    pub fn linear(&self) -> &[LinearStep] {
        &self.linear
    }

    /// The factor families' steps.
    pub fn factors(&self) -> &[FactorStep] {
        &self.factors
    }

    /// The loci the deposit reaches: the causal diamond.
    pub fn loci(&self) -> Vec<Locus> {
        self.reached.clone()
    }

    /// Its exact bits, a reading: every entry of every linear sample (its weight, feature and
    /// covector) and of every factor step (its descent direction and feature energy), each by its
    /// numerator's and denominator's bits.
    pub fn bits(&self) -> u64 {
        let bits = |x: &Rat| x.numer().bits() + x.denom().bits();
        let linear: u64 = self
            .linear
            .iter()
            .flat_map(|step| &step.samples)
            .flat_map(|sample| {
                std::iter::once(&sample.weight)
                    .chain(&sample.feature)
                    .chain(&sample.covector)
            })
            .map(bits)
            .sum();
        let factors: u64 = self
            .factors
            .iter()
            .map(|step| step.gradient.entries().map(bits).sum::<u64>() + bits(&step.energy))
            .sum();
        linear + factors
    }
}

// -------------------------------------------------------------------------------------------
// the port

/// [definition] **The execution port** (design (c)). See the module header for each method's six
/// components and consumption. A return holds faces, ratios, readings and handles, never the
/// resident's state, and has no lifetime parameter (guard 2):
///
/// ```compile_fail,E0107
/// fn borrowed(returned: holonics::receiver::reception::InteractionReturn<'static>) {}
/// ```
pub trait ExecutionPort {
    /// The field, its lift point, the constitution, the open moments, the open pending ratios and
    /// the staged deposits: on the card for a device.
    type Resident;

    /// The backend's own capacity census.
    fn census(&self) -> Census;

    /// Mounts the field at the lift point with the declared initial constitution (a transfer).
    fn mount(&self, field: &Field, current: &Current) -> Result<Self::Resident, HnnError>;

    /// The field, the lift point, and every open handle with its exact bits (a transfer).
    fn read(
        &self,
        resident: &Self::Resident,
    ) -> Result<(Field, Current, Vec<(Handle, u64)>), HnnError>;

    /// Opens (`None`) or extends a moment; stops at a carry-out of the joint clock.
    fn ingest(
        &self,
        resident: &mut Self::Resident,
        moment: Option<&MomentId>,
        cells: &[Vec<(usize, Rat)>],
    ) -> Result<
        (
            MomentId,
            InteractionReturn<Ingested, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    >;

    /// Locates the ring keys, per ring in carry order, from the crib that closed the aeon (at most
    /// its last cells, already ingested and read), at one offset, and re-keys `λ` with each
    /// published key carried to the boundary. Admitted only between `close_aeon` and the next
    /// ingest (review D1).
    fn locate_keys(
        &self,
        resident: &mut Self::Resident,
        crib: &[Vec<(usize, Rat)>],
        offset: usize,
    ) -> Result<
        InteractionReturn<KeyLocation, (), Vec<Option<Clock>>, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    >;

    /// Borrows the moment and publishes only faces; refused beyond the pending capacity.
    fn refine(
        &self,
        resident: &mut Self::Resident,
        moment: &MomentId,
        phases: &ReceivingPhases,
    ) -> Result<
        (
            PendingId,
            InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    >;

    /// Consumes the pending ratio once the compare succeeds; a refusal leaves it open.
    fn compare(
        &self,
        resident: &mut Self::Resident,
        pending: PendingId,
        target: &[Vec<(usize, Rat)>],
    ) -> Result<
        (
            StagedId,
            InteractionReturn<HolonRatio, Pullback, Deposit, Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    >;

    /// Consumes the staged deposit once its successor and the first law's re-read are computed,
    /// then publishes both; any other refusal leaves the deposit staged and the resident unchanged.
    /// Refused with `HnnError::ConstitutionBudget` when the successor's exact bits exceed the
    /// declared budget, which consumes the deposit and stops deposition; nothing is rounded.
    fn deposit(
        &self,
        resident: &mut Self::Resident,
        staged: StagedId,
    ) -> Result<
        InteractionReturn<(), (), DepositReading, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    >;

    /// Borrows the pending ratio; the width is read from its receiving phases' fibres and the
    /// tolerance is their grain, never an argument; the decision is a declared rule, as data.
    fn release(
        &self,
        resident: &mut Self::Resident,
        pending: &PendingId,
        decision: &DecisionRule,
    ) -> Result<InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError>;

    /// Refused unless the joint clock has carried out since the last boundary, and unless
    /// `admitted` is contained in the previous boundary's family.
    fn close_aeon(
        &self,
        resident: &mut Self::Resident,
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
    >;

    /// Drops an open moment, pending ratio or staged deposit.
    fn discard(
        &self,
        resident: &mut Self::Resident,
        handle: Handle,
    ) -> Result<InteractionReturn<(), (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError>;
}

// -------------------------------------------------------------------------------------------
// the word's return

/// [definition] **One element tick of the return**: the tick, the element's executed midpoint
/// `x̄_t`, its adjoint `u_t = X̂ᵀ s̄_(t+1)` through the executed solve (the exact
/// `(I − ½K)^(−ᵀ) s̄_(t+1)` under the exact law) and the contrast `c_t` it was driven by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElementTick {
    pub tick: usize,
    pub midpoint: Vec<Rat>,
    pub adjoint: Vec<Rat>,
    pub contrast: Vec<Rat>,
}

/// [definition] **One transit tick of the return**: the tick, the solved adjoint
/// `r̄_t = m̂ᵀ ζ̄_t = M_a^(−ᵀ) ω̄_t` through the executed solve, the contact state `(u_t, w_t)` before
/// it and its executed midpoint rate `ω_t`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransitTick {
    pub tick: usize,
    pub solved: Vec<Rat>,
    pub displacement: Vec<Rat>,
    pub rate: Vec<Rat>,
    pub midpoint: Vec<Rat>,
}

/// [definition] **What the word's return yields**: the covector on the opening storage of every
/// ring, the element and transit ticks with their adjoints, the conductance covector `∂ℓ/∂G_a`, per
/// receiving phase the receiving map's feature `P_R^(τ_R) v_R(e_j)` with the logit gradient, and the
/// adjoint's carried remainders, released at the open ([`Remainders`]; none under the exact law).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordReturn {
    pub opening: Vec<Vec<Rat>>,
    pub elements: Vec<Vec<ElementTick>>,
    pub transits: Vec<Vec<TransitTick>>,
    pub conductance: Vec<Rat>,
    pub reads: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub released: Remainders,
}

impl<'c> Word<'c> {
    /// **The word's return over its own per-tick waves** (module header). `map` is the receiving
    /// map `R` and `lift` the receiving ring's lift `τ_R` the read used.
    pub fn pull_back(
        self,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        lift: &BigInt,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        reverse(&self, covector, map, lift, phases)
    }
}

fn zeros(n: usize) -> Vec<Rat> {
    vec![Rat::zero(); n]
}

/// **Split at the transients' lattice with error feedback**, or leave the image under the exact
/// law: the carried covector and the next remainders (Lean `HNN/LatticeWord.feedback_tick`).
fn split(lattice: Option<&Lattice>, image: Vec<Rat>, remainder: &[Rat]) -> (Vec<Rat>, Vec<Rat>) {
    match lattice {
        Some(lattice) => {
            let mut next = remainder.to_vec();
            let carried = carry(lattice, &image, &mut next);
            (carried, next)
        }
        None => (image, remainder.to_vec()),
    }
}

/// The adjoint's carried remainders, one per covector coordinate it carries.
struct Adjoint {
    storage: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    displacement: Vec<Vec<Rat>>,
    rate: Vec<Vec<Rat>>,
    elements: Vec<Vec<Rat>>,
    zetas: Vec<Vec<Rat>>,
    solved: Vec<Vec<Rat>>,
    /// The receiving anchor's covector `P^(−τ)Rᵀg_j`, the return's source, carried from epoch to
    /// epoch in reverse.
    reads: Vec<Rat>,
}

impl Adjoint {
    fn released(&self) -> Remainders {
        Remainders::of(
            self.storage
                .iter()
                .chain(&self.displacement)
                .chain(&self.rate)
                .chain(&self.elements)
                .chain(&self.zetas)
                .chain(&self.solved)
                .chain(std::iter::once(&self.reads))
                .flatten()
                .chain(self.arrivals.iter().flatten().flatten()),
        )
    }
}

/// One element's reverse step: its wave and contrast covectors, its tick, and its adjoint's next
/// remainder.
type ElementReverse = (Vec<Rat>, Vec<Rat>, ElementTick, Vec<Rat>);

/// One transit's reverse step: its two ends' outgoing covectors, its previous state covectors, its
/// conductance term, its tick and its three next remainders (`ζ̄`, `r̄`, and the state's pair).
type TransitReverse = (
    [(usize, usize, Vec<Rat>); 2],
    Vec<Rat>,
    Vec<Rat>,
    Rat,
    TransitTick,
    (Vec<Rat>, Vec<Rat>, [Vec<Rat>; 2]),
);

/// One incident contact's part of a junction's reverse Swing: the contact, its slot, the arriving
/// covector, its remainder and the conductance term.
type Arriving = (usize, usize, Vec<Rat>, Vec<Rat>, Rat);

/// One junction's reverse Swing: its storage covector with its remainder, and each incident
/// contact's part.
type JunctionReverse = (Vec<Rat>, Vec<Rat>, Vec<Arriving>);

fn reverse(
    word: &Word<'_>,
    covector: &RatioCovector,
    map: &ExactRatMatrix,
    lift: &BigInt,
    phases: &ReceivingPhases,
) -> Result<WordReturn, HnnError> {
    let field = word.field();
    let operands = word.operands();
    let records = word.recorded();
    let steps = records.len();
    if steps != phases.junction_steps() {
        return Err(HnnError::Shape {
            what: "the word's junction steps against its receiving window",
            expected: phases.junction_steps(),
            found: steps,
        });
    }
    if covector.logits().len() != phases.aperture() {
        return Err(HnnError::Shape {
            what: "covector phases against the aperture",
            expected: phases.aperture(),
            found: covector.logits().len(),
        });
    }
    let lattice = operands.lattice().map(|word| word.transient());
    let receiving = phases.ring();
    let receiving_ring = field.ring(receiving);
    let map_t = map.transpose()?;
    // The anchor covector of each receiving epoch: P^(−τ) Rᵀ g_j.
    let mut reads = Vec::with_capacity(phases.aperture());
    let mut read_covector: Vec<Option<Vec<Rat>>> = vec![None; steps];
    for (j, epoch) in phases.epochs().enumerate() {
        let gradient = covector.logits()[j].clone();
        let pulled = apply_rows(&map_t, &gradient)?;
        read_covector[epoch] = Some(receiving_ring.rotate(&pulled, &-lift));
        let anchor = word
            .anchor(epoch, receiving)
            .ok_or(HnnError::WordEnded { ticks: steps })?;
        reads.push((receiving_ring.rotate(anchor, lift), gradient));
    }
    let h = operands.step().clone();
    let rings = operands.rings();
    let contacts = operands.contacts();
    let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
    let mut storage_bar: Vec<Vec<Rat>> = widths.iter().map(|n| zeros(*n)).collect();
    let mut arrival_bar: Vec<[Vec<Rat>; 2]> = contacts
        .iter()
        .map(|contact| {
            let (from, to) = contact.ends();
            [zeros(widths[from]), zeros(widths[to])]
        })
        .collect();
    let mut displacement_bar: Vec<Vec<Rat>> = contacts
        .iter()
        .map(|contact| zeros(contact.width()))
        .collect();
    let mut rate_bar = displacement_bar.clone();
    let mut carried = Adjoint {
        storage: storage_bar.clone(),
        arrivals: arrival_bar.clone(),
        displacement: displacement_bar.clone(),
        rate: rate_bar.clone(),
        elements: storage_bar.clone(),
        zetas: displacement_bar.clone(),
        solved: displacement_bar.clone(),
        reads: zeros(widths[receiving]),
    };
    let mut conductance = vec![Rat::zero(); contacts.len()];
    let mut elements: Vec<Vec<ElementTick>> = vec![Vec::new(); rings.len()];
    let mut transits: Vec<Vec<TransitTick>> = vec![Vec::new(); contacts.len()];
    for t in (0..steps).rev() {
        let record = &records[t];
        // The step's junctions, read from its own record at the anchors the word carried: the
        // rings run together.
        let junctions: Vec<_> = indexed(rings.len(), |r| {
            let incoming: Vec<&[Rat]> = operands
                .incident(r)
                .iter()
                .map(|&a| record.arrivals[a][operands.end_slot(a, r)].as_slice())
                .collect();
            Ok::<_, HnnError>(swing_about(
                record.anchors[r].clone(),
                &record.storage[r],
                &incoming,
            ))
        })?;
        let mut wave_bar: Vec<Vec<Rat>> = widths.iter().map(|n| zeros(*n)).collect();
        let mut contrast_bar = wave_bar.clone();
        let mut outgoing_bar: Vec<Vec<Vec<Rat>>> = (0..rings.len())
            .map(|r| {
                operands
                    .incident(r)
                    .iter()
                    .map(|_| zeros(widths[r]))
                    .collect()
            })
            .collect();
        let (mut displacement_prev, mut rate_prev) = (displacement_bar.clone(), rate_bar.clone());
        if t + 1 < steps {
            // Each element's reverse step reads only its own storage covector and remainder
            // through its executed solve's transpose, and writes only its own slot: the rings run
            // together.
            let reversed = indexed(rings.len(), |r| {
                let image = rings[r].solve_transpose(&storage_bar[r])?;
                let (adjoint, remainder) = split(lattice.as_ref(), image, &carried.elements[r]);
                let wave = sub(&scale(&integer(2), &adjoint), &storage_bar[r]);
                let contrast = rings[r].contrast_transpose(&adjoint);
                Ok::<ElementReverse, HnnError>((
                    wave,
                    contrast,
                    ElementTick {
                        tick: t,
                        midpoint: record.midpoints[r].clone(),
                        adjoint,
                        contrast: junctions[r].contrast.clone(),
                    },
                    remainder,
                ))
            })?;
            for (r, (wave, contrast, tick, remainder)) in reversed.into_iter().enumerate() {
                wave_bar[r] = wave;
                contrast_bar[r] = contrast;
                elements[r].push(tick);
                carried.elements[r] = remainder;
            }
            // Each transit's reverse step reads its own covectors, record and remainders through
            // its executed solve's transpose, and writes only its own slots (its two outgoing
            // covectors, its previous state covectors, its conductance term, its remainders): the
            // contacts run together, and the conductance terms are added afterwards in contact
            // order.
            let transited = indexed(contacts.len(), |a| {
                let contact = &contacts[a];
                let (from, to) = contact.ends();
                let position = |ring: usize| {
                    operands
                        .incident(ring)
                        .iter()
                        .position(|&b| b == a)
                        .expect("a contact is incident to its ends")
                };
                let (from_position, to_position) = (position(from), position(to));
                let (select_from, select_to) = contact.selection();
                let channel = select_from.len().min(select_to.len());
                let g = contact.conductance();
                let midpoint = &record.rates[a];
                // ζ̄ = (G/h) w̄′ + (G/2) ū′ + (ā′_h − ā′_g)/h on the channel: the transpose of
                // w′ = (G/h)ζ − w, u′ = u + (G/2)ζ, a′ = α ∓ ζ/h.
                let exchange_bar: Vec<Rat> = entries(channel, |k| {
                    &arrival_bar[a][1][select_to[k]] - &arrival_bar[a][0][select_from[k]]
                });
                let (rate_gain, shift_gain) = (g / &h, g / integer(2));
                let zeta_image = entries(channel, |k| {
                    &rate_gain * &rate_bar[a][k]
                        + &shift_gain * &displacement_bar[a][k]
                        + &exchange_bar[k] / &h
                });
                let (zeta_bar, zeta_remainder) =
                    split(lattice.as_ref(), zeta_image, &carried.zetas[a]);
                let (solved, solved_remainder) = split(
                    lattice.as_ref(),
                    contact.solve_transpose(&zeta_bar)?,
                    &carried.solved[a],
                );
                let pushed = entries(solved.len(), |k| &h * &solved[k]);
                let pushed_at = |selection: &[usize], width: usize| {
                    let mut at = vec![None; width];
                    let paired = channel.min(pushed.len());
                    for (k, &coordinate) in selection.iter().enumerate().take(paired) {
                        at[coordinate] = Some(k);
                    }
                    at
                };
                let (from_at, to_at) = (
                    pushed_at(select_from, arrival_bar[a][0].len()),
                    pushed_at(select_to, arrival_bar[a][1].len()),
                );
                let from_bar = entries(from_at.len(), |i| match from_at[i] {
                    Some(k) => &arrival_bar[a][0][i] + &pushed[k],
                    None => arrival_bar[a][0][i].clone(),
                });
                let to_bar = entries(to_at.len(), |j| match to_at[j] {
                    Some(k) => &arrival_bar[a][1][j] - &pushed[k],
                    None => arrival_bar[a][1][j].clone(),
                });
                let (storage_form, stiffness_form, _) = contact.forms();
                let (stored, stiffened) = (
                    apply_rows(storage_form, &solved)?,
                    apply_rows(stiffness_form, &solved)?,
                );
                let rate_image = entries(rate_bar[a].len().min(stored.len()), |k| {
                    -&rate_bar[a][k] + integer(2) * &stored[k]
                });
                let displacement_image =
                    entries(displacement_bar[a].len().min(stiffened.len()), |k| {
                        &displacement_bar[a][k] - &h * &stiffened[k]
                    });
                let (rate, rate_remainder) = split(lattice.as_ref(), rate_image, &carried.rate[a]);
                let (displacement, displacement_remainder) = split(
                    lattice.as_ref(),
                    displacement_image,
                    &carried.displacement[a],
                );
                let square = g * g;
                let term = integer(2) * &h / &square * dot(&solved, midpoint)
                    - integer(2) / &square * dot(&exchange_bar, midpoint);
                Ok::<TransitReverse, HnnError>((
                    [(from, from_position, from_bar), (to, to_position, to_bar)],
                    rate,
                    displacement,
                    term,
                    TransitTick {
                        tick: t,
                        solved,
                        displacement: record.states[a][0].clone(),
                        rate: record.states[a][1].clone(),
                        midpoint: midpoint.clone(),
                    },
                    (
                        zeta_remainder,
                        solved_remainder,
                        [displacement_remainder, rate_remainder],
                    ),
                ))
            })?;
            for (a, (ends, rate, displacement, term, tick, remainders)) in
                transited.into_iter().enumerate()
            {
                for (ring, position, covector) in ends {
                    outgoing_bar[ring][position] = covector;
                }
                rate_prev[a] = rate;
                displacement_prev[a] = displacement;
                conductance[a] += term;
                transits[a].push(tick);
                let (zeta, solved, [displacement_remainder, rate_remainder]) = remainders;
                carried.zetas[a] = zeta;
                carried.solved[a] = solved;
                carried.displacement[a] = displacement_remainder;
                carried.rate[a] = rate_remainder;
            }
        }
        // Each junction's reverse Swing reads only its own covectors, record and remainders
        // through its executed weights, and writes only its own storage covector, its own arriving
        // slots, its remainders and its conductance terms: the rings run together, and the
        // conductance terms are added afterwards in ring, then incidence, order.
        // The return's source enters at the receiving anchor on the transients' lattice.
        let read_carried = match read_covector[t].take() {
            Some(image) => {
                let (read, remainder) = split(lattice.as_ref(), image, &carried.reads);
                carried.reads = remainder;
                Some(read)
            }
            None => None,
        };
        let (arrival_carried, storage_carried) = (&carried.arrivals, &carried.storage);
        let swung = indexed(rings.len(), |r| {
            let junction = &junctions[r];
            let read = if r == receiving {
                read_carried.as_ref()
            } else {
                None
            };
            let incident = operands.incident(r);
            let weights = operands.weights(r);
            let total = incident
                .iter()
                .fold(rings[r].admittance().clone(), |sum, &a| {
                    sum + contacts[a].conductance()
                });
            // Each coordinate of the junction's reverse Swing reads only that coordinate of its
            // covectors: the coordinates run together.
            let coordinates = entries(widths[r], |i| {
                let mut anchor = integer(2) * &wave_bar[r][i] + &contrast_bar[r][i];
                for outgoing in &outgoing_bar[r] {
                    anchor += integer(2) * &outgoing[i];
                }
                if let Some(read) = read {
                    anchor += &read[i];
                }
                let storage = &weights[0] * &anchor - (&wave_bar[r][i] + &contrast_bar[r][i]);
                let arriving: Vec<Rat> = weights[1..]
                    .iter()
                    .zip(&outgoing_bar[r])
                    .map(|(gain, outgoing)| gain * &anchor - &outgoing[i])
                    .collect();
                (anchor, storage, arriving)
            });
            let mut anchor_bar = Vec::with_capacity(coordinates.len());
            let mut storage = Vec::with_capacity(coordinates.len());
            let mut covectors: Vec<Vec<Rat>> = vec![Vec::with_capacity(widths[r]); incident.len()];
            for (anchor, stored, arriving) in coordinates {
                anchor_bar.push(anchor);
                storage.push(stored);
                for (covector, value) in covectors.iter_mut().zip(arriving) {
                    covector.push(value);
                }
            }
            let (storage, storage_remainder) =
                split(lattice.as_ref(), storage, &storage_carried[r]);
            let arriving: Vec<Arriving> = incident
                .iter()
                .zip(covectors)
                .map(|(&a, covector)| {
                    let slot = operands.end_slot(a, r);
                    let (covector, remainder) =
                        split(lattice.as_ref(), covector, &arrival_carried[a][slot]);
                    let offset = entries(widths[r], |i| {
                        &record.arrivals[a][slot][i] - &junction.anchor[i]
                    });
                    (
                        a,
                        slot,
                        covector,
                        remainder,
                        dot(&anchor_bar, &offset) / &total,
                    )
                })
                .collect();
            Ok::<JunctionReverse, HnnError>((storage, storage_remainder, arriving))
        })?;
        let mut storage_next: Vec<Vec<Rat>> = Vec::with_capacity(rings.len());
        let mut arrival_next = arrival_bar.clone();
        for (r, (storage, storage_remainder, arriving)) in swung.into_iter().enumerate() {
            storage_next.push(storage);
            carried.storage[r] = storage_remainder;
            for (a, slot, covector, remainder, term) in arriving {
                arrival_next[a][slot] = covector;
                carried.arrivals[a][slot] = remainder;
                conductance[a] += term;
            }
        }
        storage_bar = storage_next;
        arrival_bar = arrival_next;
        displacement_bar = displacement_prev;
        rate_bar = rate_prev;
    }
    for ticks in &mut elements {
        ticks.reverse();
    }
    for ticks in &mut transits {
        ticks.reverse();
    }
    Ok(WordReturn {
        opening: storage_bar,
        elements,
        transits,
        conductance,
        reads,
        released: carried.released(),
    })
}
