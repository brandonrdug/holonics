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
//! | `refine` | the wave's faces (the tree part needs each phase's address, read at compare) | absent (forward only) | absent | the moment's lift | the binding read | ticks, balances (each with its residual and certified bound), diamond, the released change, the charts' certificates, the released remainders |
//! | `compare` | the [`HolonRatio`] on the combined faces (the tree's at each phase's causal address plus the wave's) | the complete [`Pullback`] | a [`Deposit`] (its landmark steps included) | the anchor's | the pending binding | KL, excess, winding, residual, loci, the return's released remainders, the tree face alone's code lengths |
//! | `deposit` | the successor constitution | absent | the applied [`DepositReading`] | unchanged | absent | each linear locus's certified step, the certified storage growth `ε_k` and its product, the successor's per-tick amplitude growth, commit, bits against `B_Θ` |
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
//! feedback and their remainders released at the open ([`WordReturn::released`]; the lattice word) (Lean
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
use num_traits::{One, Zero};

use crate::aeon::Reading;
use crate::compression::{CompressionError, ResonanceSplit, resonance_split};
use crate::hnn::HnnError;
use crate::hnn::encoding::Encoded;
use crate::hnn::chart::{ChartReading, Remainders, carry};
use crate::hnn::constitution::{
    DepositReading, FactorStep, LandmarkStep, Lattice, LinearStep, Locus, Reach,
};
use crate::hnn::field::{Current, Field, Ring};
use crate::hnn::keys::KeyLocation;
use crate::hnn::moment::{Ingested, SourceCapacity};
use crate::hnn::propagation::{
    PathAttenuation, TickBalance, conductance_covector, scattering_about,
};
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector};
use crate::hnn::realization::{apply_rows, entries, indexed};
use crate::hnn::receiving::{ReceivingPhases, ReceivingStep};
use crate::hnn::retention::AeonBoundary;
use crate::hnn::word::Word;
use crate::holon::HolonError;
use crate::holon::contact::FeatureCovector;
use crate::navigator::Clock;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::work::ExactWork;
use crate::ratio::{Rat, integer};
use crate::receiver::face::{DiameterNorm, ReceiverWidth, WidthWitness};
use crate::receiver::receipt::{Receipt, RegionChart};
use crate::receiver::reception::{InteractionReturn, SourceOrder};
use crate::receiver::release::{DecisionRule, ReleaseReturn};

use crate::receiver::reception::Component;

// -------------------------------------------------------------------------------------------
// handles

/// A handle to an open [`crate::hnn::SourceMoment`] in the resident. Its number is public so that
/// every backend's resident issues handles as the host reference does (one counter per resident).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MomentId(pub u64);

/// A handle to an open [`crate::hnn::PendingRatio`] in the resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PendingId(pub u64);

/// A handle to a staged [`Deposit`] in the resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StagedId(pub u64);

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
    /// `ingest`: cells accessed, the moment's dense bits, its source-state capacity (the checked
    /// reading on its admitted clock, with the retained leaky coordinates where carried:
    /// `hnn::moment::SourceCapacity::checked_of`) against the source's `n ⌈log₂|A|⌉`, and whether the
    /// joint clock carried out.
    Ingest {
        cells: u64,
        moment_bits: u64,
        capacity: SourceCapacity,
        source_bits: u64,
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
    /// a shielded receiver is reported as a located cause; and (the lattice word) every executed chart's
    /// reading (its certificate against the target, its refinement's steps and seed), the carried
    /// remainders the word released at its end, the last junction's residual, and each declared
    /// resonator's balance over the word and the word's whole balance (campaign 2).
    Refine {
        reached: Vec<Locus>,
        released_power: Rat,
        peak_bits: u64,
        path: PathAttenuation,
        charts: Vec<ChartReading>,
        remainders: Remainders,
        last: Rat,
        /// Each declared ring resonator's balance over the word (campaign 2,
        /// `hnn::word::ResonatorBalance`), in ring order; empty where none is declared.
        resonators: Vec<crate::hnn::word::ResonatorBalance>,
        /// The whole word's balance (campaign 2, `hnn::word::WordBalance::of` its release), which
        /// the exposure carries across the commit that follows and checks at every word.
        word: Box<crate::hnn::word::WordBalance>,
    },
    /// `compare`: the epoch's code length (the KL part, enclosed), phase excess, each phase's
    /// winding, the residual of the wave's logits against the emitted ones, the loci reached, the
    /// remainders the return's carried adjoint released at the open (the lattice word); each
    /// phase's code length under the landmark tree's executed face alone (`tree`: `−log₂ q_T(t_j)`,
    /// the face the population weighs; `hnn::receiving::Scored::tree`) and under the face of its
    /// grain logits alone (`tree_grain`: `hnn::receiving::tree_code_length`, the face the combined
    /// read opens at when the wave reads zero), each at the same standing and address as the
    /// combined face (the landmark tree, the epoch read in cell order); and each phase's code
    /// length under the receiver's scored face, its population over the tree's and the combined
    /// face (ruling A; `hnn::receiving::receiving_population`), whose sum is the epoch's code
    /// length. The Holon ratio (its phases' code lengths, excess and windings) is the combined
    /// face's, whose covector the wave learns from.
    Compare {
        code_length: crate::ratio::algebraic::ExactInterval,
        excess: Rat,
        windings: Vec<BigInt>,
        residual: Vec<Vec<Rat>>,
        reached: Vec<Locus>,
        released: Remainders,
        tree: Vec<crate::ratio::algebraic::ExactInterval>,
        tree_grain: Vec<crate::ratio::algebraic::ExactInterval>,
        model: Vec<crate::ratio::algebraic::ExactInterval>,
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

/// **Per-ring regions in their own clocks**: each ring's tick count, a count (clock exponent 0)
/// whose clock unit is the ring's step.
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

/// [definition] **A method's receipt in the port's one form**, for every backend: the rings' tick
/// counts in their own clocks (unit the ring's step), the counted work and the method's detail;
/// the balances and the receivers' fibres are filled by the methods that read them.
pub fn port_receipt(
    ticks: &[u64],
    unit: &Rat,
    work: ExactWork,
    detail: ReceiptDetail,
) -> Result<PortReceipt, HnnError> {
    Ok(PortReceipt {
        rings: ring_receipt(ticks, unit)?,
        balances: Vec::new(),
        work,
        unresolved: Vec::new(),
        detail,
    })
}

/// **Count the entries a method wrote** in its work (`ExactWork`'s own counting: each entry's
/// numerator and denominator bits), for every backend's receipt.
pub fn wrote_all<'a>(work: &mut ExactWork, values: impl IntoIterator<Item = &'a Rat>) {
    for value in values {
        work.wrote(value);
    }
}

/// **Count `steps` steps in sequence** in a method's work (its dependency span).
pub fn stepped(work: &mut ExactWork, steps: u64) {
    for _ in 0..steps {
        work.stepped();
    }
}

/// **Widen a method's resident reading** to `entries`.
pub fn resident(work: &mut ExactWork, entries: u64) {
    work.resident(entries);
}

/// **Count `count` additions** in a method's work.
pub fn added(work: &mut ExactWork, count: u64) {
    work.added(count);
}

/// [definition] **The boundary's pullback of one pending ratio** (design (c), `close_aeon`): the
/// transpose of `V` on it, the retained loci its diamond reads, onto which its covectors pull back
/// by `Vᵀ` (the inclusion of the retained loci); or, when it reads a released locus, its separator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transpose {
    Retained(Vec<Locus>),
    Separator(Vec<Locus>),
}

/// **The release's width, read from its receiving phases** (module header): over the epoch's
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
    pub resonators: Vec<ResonatorPullback>,
    pub receiving: (usize, ExactRatMatrix),
}

/// [definition] **The staged material return** (design (c), `Deposit`): keyed by locus, inside the
/// causal diamond of the source rings and the receiver, at the constitution commit it was computed
/// at: what reached each linear locus inside its diamond, the factor families' steps and the
/// receiving parametron's landmark steps (the landmark tree), one per reached comparison in cell
/// order; and its reach (`hnn::constitution::Reach`: the stations, re-entries and phases its
/// covectors summed), which the certified step reads. Only a compare builds one (`hnn::reference`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Deposit {
    commit: u64,
    linear: Vec<LinearStep>,
    factors: Vec<FactorStep>,
    landmarks: Vec<LandmarkStep>,
    receiving: Vec<ReceivingStep>,
    reached: Vec<Locus>,
    reach: Option<Reach>,
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
            landmarks: Vec::new(),
            receiving: Vec::new(),
            reached,
            reach: None,
        }
    }

    /// The deposit with its reach (the certified step's reading of its covectors' sums).
    pub(crate) fn with_reach(self, reach: Reach) -> Self {
        Self {
            reach: Some(reach),
            ..self
        }
    }

    /// Its reach, when declared.
    pub fn reach(&self) -> Option<&Reach> {
        self.reach.as_ref()
    }

    /// The deposit with the receiving face's steps (ruling A; THE_REBUILD U1).
    pub(crate) fn with_receiving(self, receiving: Vec<ReceivingStep>) -> Self {
        Self { receiving, ..self }
    }

    /// The receiving face's steps (`hnn::receiving::ReceivingStep`), in cell order.
    pub fn receiving(&self) -> &[ReceivingStep] {
        &self.receiving
    }

    /// The deposit with the receiving parametron's landmark steps (the landmark tree).
    pub(crate) fn with_landmarks(self, landmarks: Vec<LandmarkStep>) -> Self {
        Self { landmarks, ..self }
    }

    /// The receiving parametron's landmark steps (the landmark tree), in cell order.
    pub fn landmarks(&self) -> &[LandmarkStep] {
        &self.landmarks
    }

    /// The constitution commit the deposit was computed at.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// What reached each linear locus inside its diamond.
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
    /// covector), of every factor step (its descent direction and feature energy), each by its
    /// numerator's and denominator's bits, and of every landmark step (its address letters' codes
    /// and its class, as naturals).
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
        let natural = |x: usize| u64::from(usize::BITS - x.leading_zeros()).max(1);
        let landmarks: u64 = self
            .landmarks
            .iter()
            .map(|step| {
                step.address
                    .iter()
                    .map(|letter| natural(letter.code() as usize))
                    .sum::<u64>()
                    + natural(step.class)
            })
            .sum();
        let receiving: u64 = self
            .receiving
            .iter()
            .map(|step| bits(&step.tree) + bits(&step.combined.lower) + bits(&step.combined.upper))
            .sum();
        linear + factors + landmarks + receiving
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
///
/// A source enters only encoded (THE_MACHINE guard 9): `ingest`, `locate_keys` and `compare` take
/// an `hnn::encoding::Encoded`, never exterior codes or one-hot cells (structural, `E0308`):
///
/// ```compile_fail,E0308
/// use holonics::hnn::port::ExecutionPort;
/// fn bytes<P: ExecutionPort>(port: &P, resident: &mut P::Resident, codes: &[usize]) {
///     let _ = port.ingest(resident, None, codes);
/// }
/// ```
///
/// ```compile_fail,E0308
/// use holonics::hnn::port::ExecutionPort;
/// use holonics::ratio::Rat;
/// fn one_hot<P: ExecutionPort>(port: &P, resident: &mut P::Resident, cells: &[Vec<(usize, Rat)>]) {
///     let _ = port.ingest(resident, None, cells);
/// }
/// ```
///
/// ```compile_fail,E0308
/// use holonics::hnn::port::{ExecutionPort, PendingId};
/// fn target<P: ExecutionPort>(port: &P, resident: &mut P::Resident, pending: PendingId, codes: &[usize]) {
///     let _ = port.compare(resident, pending, codes);
/// }
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

    /// Opens (`None`) or extends a moment with an encoded passage (an empty `Encoded::part` opens
    /// one with nothing taken); stops at a carry-out of the joint clock.
    fn ingest(
        &self,
        resident: &mut Self::Resident,
        moment: Option<&MomentId>,
        cells: &Encoded,
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
        crib: &Encoded,
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
        target: &Encoded,
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
/// ring, the element and transit ticks with their adjoints, the conductance covector `∂ℓ/∂G_a` (at
/// each junction read at the executed node potential,
/// [`crate::hnn::propagation::conductance_covector`]), per receiving phase the receiving map's
/// feature `P_R^(τ_R) v_R(e_j)` with the logit gradient, and the adjoint's carried remainders,
/// released at the open ([`Remainders`]; none under the exact law).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordReturn {
    pub opening: Vec<Vec<Rat>>,
    pub elements: Vec<Vec<ElementTick>>,
    pub transits: Vec<Vec<TransitTick>>,
    /// Loaded resonator ticks, indexed by ring and ordered chronologically.
    pub resonators: Vec<Vec<ResonatorTick>>,
    pub conductance: Vec<Rat>,
    pub reads: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub released: Remainders,
}

/// One loaded resonator tick's material-free adjoint operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorTick {
    pub ring: usize,
    pub tick: usize,
    pub phase: usize,
    pub drive: Vec<Rat>,
    pub displacement: Vec<Rat>,
    pub velocity: Vec<Rat>,
    pub rate: Vec<Rat>,
    /// The transpose solve's RHS covector `r̄ = X̂ᵀ z̄`, carried on the word lattice.
    pub solved: Vec<Rat>,
    pub output: Vec<Rat>,
}

/// One resonator's declared gain covectors, accumulated in its declared basis family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorPullback {
    pub ring: usize,
    /// Loss gradients with respect to `(g_C,g_K,g_D,g_pump[,g_beta])`.
    pub gains: Vec<Rat>,
    /// Exact feature energies used by the factor law.
    pub energy: Vec<Rat>,
}

/// [definition; agent-inferred] **A covector on a word's change** (U6's native generation, whose
/// linear readout consumed it until its retirement, batch H; `hnn::word`'s "Continuing motion
/// within a refinement"): one covector per part of the change a continuing word opens on, in the
/// change's own shape (the storage waves per ring, the arriving waves per contact
/// `[at from, at to]`, the contact states `[u, w]`, and each declared resonator's state `[u, w]`). A
/// continuing word's return reads the covector on its end change (the next word's opening covector)
/// and returns the covector on its opening change.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChangeCovector {
    pub storage: Vec<Vec<Rat>>,
    pub arrivals: Vec<[Vec<Rat>; 2]>,
    pub states: Vec<[Vec<Rat>; 2]>,
    pub resonators: Vec<Option<[Vec<Rat>; 2]>>,
}

impl ChangeCovector {
    /// **The pairing** `⟨μ, x⟩` of the covector with a change of the same shape, every part summed.
    pub fn pairing(&self, change: &crate::hnn::word::EndChange) -> Rat {
        let mut total = Rat::zero();
        for (covector, wave) in self.storage.iter().zip(&change.storage) {
            total += dot(covector, wave);
        }
        for (covector, pair) in self.arrivals.iter().zip(&change.arrivals) {
            total += dot(&covector[0], &pair[0]) + dot(&covector[1], &pair[1]);
        }
        for (covector, state) in self.states.iter().zip(&change.states) {
            total += dot(&covector[0], &state[0]) + dot(&covector[1], &state[1]);
        }
        for (covector, state) in self.resonators.iter().zip(&change.resonators) {
            if let (Some(covector), Some(state)) = (covector, state) {
                total += dot(&covector[0], &state[0]) + dot(&covector[1], &state[1]);
            }
        }
        total
    }
}

impl<'c> Word<'c> {
    /// The exact differential of one receiving anchor through this word's producing operands.
    /// This declaration-time reading borrows the zero-motion word; it publishes no learned
    /// covector and retains no word. A nonlinear receiving declaration uses these rows only
    /// as a tangent at rest, never as a global linear response map.
    pub(crate) fn anchor_differential(
        &self,
        anchors: Vec<Option<Vec<Rat>>>,
        receiving: usize,
    ) -> Result<ChangeCovector, HnnError> {
        if self.operands().lattice().is_some() {
            return Err(HnnError::Shape {
                what: "an exact word for a declaration-time anchor differential",
                expected: 0,
                found: 1,
            });
        }
        if anchors.len() != self.recorded().len() {
            return Err(HnnError::Shape {
                what: "one anchor covector slot per junction step of the word",
                expected: self.recorded().len(),
                found: anchors.len(),
            });
        }
        Ok(reverse_core(self, anchors, receiving, None)?.1)
    }

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

    /// [definition; agent-inferred] **A continuing word's return** (U6's native generation; its
    /// consumer, the linear readout, retired September 30, batch H): the same reverse sweep over
    /// the word's own per-tick waves, the transpose of the linear map each tick executed at its
    /// fixed operands, read from two sources. `anchors` holds, per junction step, the covector on
    /// the receiving ring `receiving`'s anchor at that step (a section's station reads, already
    /// pulled back through its receiving map and phase bindings); `end` is the covector on the
    /// change the word ends with, which a word that ended at a last junction does not continue
    /// (refused there). It returns the word's return (its
    /// `reads` empty: the caller holds the stations' reads) and the covector on the word's opening
    /// change, which the previous word of the refinement reads as its `end`. The word is consumed
    /// (guard 2).
    pub fn pull_back_continuing(
        self,
        anchors: Vec<Option<Vec<Rat>>>,
        receiving: usize,
        end: Option<&ChangeCovector>,
    ) -> Result<(WordReturn, ChangeCovector), HnnError> {
        if anchors.len() != self.recorded().len() {
            return Err(HnnError::Shape {
                what: "one anchor covector slot per junction step of the word",
                expected: self.recorded().len(),
                found: anchors.len(),
            });
        }
        reverse_core(&self, anchors, receiving, end)
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
    resonator_drive: Vec<Vec<Rat>>,
    resonator_rate: Vec<Vec<Rat>>,
    resonator_solve: Vec<Vec<Rat>>,
    resonator_state: Vec<Option<[Vec<Rat>; 2]>>,
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
                .chain(&self.resonator_drive)
                .chain(&self.resonator_rate)
                .chain(&self.resonator_solve)
                .chain(
                    self.resonator_state
                        .iter()
                        .filter_map(Option::as_ref)
                        .flatten(),
                )
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

/// A loaded resonator's return to its element drive and preceding mode state.
type ResonatorReverse = (Vec<Rat>, [Vec<Rat>; 2], ResonatorTick, [Vec<Rat>; 5]);

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
    let steps = word.recorded().len();
    if steps != phases.junction_steps() {
        return Err(HnnError::Shape {
            what: "the word's junction steps against its receiving phases",
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
    let (mut back, _) = reverse_core(word, read_covector, receiving, None)?;
    back.reads = reads;
    Ok(back)
}

/// **The reverse sweep** over a word's own per-tick waves (module header, "The word's return"):
/// from the covector on the receiving ring's anchor at each junction step (`read_covector`, carried
/// on the transients' lattice as it enters) and, for a word that did not end at a last junction,
/// the covector on its end change (`end`, a continuing word's). Every step of a
/// word that ended at its last junction but that last one reverses its element, loaded resonator
/// and transit; every step of a continuing word does. Returns the word's return (its `reads`
/// empty) and the covector on the word's opening change.
fn reverse_core(
    word: &Word<'_>,
    mut read_covector: Vec<Option<Vec<Rat>>>,
    receiving: usize,
    end: Option<&ChangeCovector>,
) -> Result<(WordReturn, ChangeCovector), HnnError> {
    let field = word.field();
    let operands = word.operands();
    let records = word.recorded();
    let steps = records.len();
    if receiving >= field.rings().len() {
        return Err(HnnError::RingOutside {
            ring: receiving,
            rings: field.rings().len(),
        });
    }
    if end.is_some() && word.is_ended() {
        return Err(HnnError::WordEnded { ticks: steps });
    }
    let lattice = operands.lattice().map(|word| word.transient());
    let h = operands.step().clone();
    let rings = operands.rings();
    let contacts = operands.contacts();
    let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
    let rest_storage: Vec<Vec<Rat>> = widths.iter().map(|n| zeros(*n)).collect();
    let rest_arrivals: Vec<[Vec<Rat>; 2]> = contacts
        .iter()
        .map(|contact| {
            let (from, to) = contact.ends();
            [zeros(widths[from]), zeros(widths[to])]
        })
        .collect();
    let rest_states: Vec<Vec<Rat>> = contacts
        .iter()
        .map(|contact| zeros(contact.width()))
        .collect();
    let rest_resonators: Vec<Option<[Vec<Rat>; 2]>> = operands
        .resonators()
        .iter()
        .map(|resonator| {
            resonator
                .as_ref()
                .map(|r| [zeros(r.width()), zeros(r.width())])
        })
        .collect();
    // The covector on the end change seeds the sweep; a word that ended opens it at zero.
    let (mut storage_bar, mut arrival_bar, mut displacement_bar, mut rate_bar) = match end {
        Some(end) => {
            let shaped = end.storage.len() == widths.len()
                && end.storage.iter().zip(&widths).all(|(x, n)| x.len() == *n)
                && end.arrivals.len() == contacts.len()
                && end.states.len() == contacts.len()
                && end.resonators.len() == widths.len();
            if !shaped {
                return Err(HnnError::Shape {
                    what: "a covector on a word's end change",
                    expected: widths.len(),
                    found: end.storage.len(),
                });
            }
            (
                end.storage.clone(),
                end.arrivals.clone(),
                end.states.iter().map(|state| state[0].clone()).collect(),
                end.states.iter().map(|state| state[1].clone()).collect(),
            )
        }
        None => (
            rest_storage.clone(),
            rest_arrivals.clone(),
            rest_states.clone(),
            rest_states.clone(),
        ),
    };
    let mut carried = Adjoint {
        storage: rest_storage.clone(),
        arrivals: rest_arrivals.clone(),
        displacement: rest_states.clone(),
        rate: rest_states.clone(),
        elements: rest_storage.clone(),
        resonator_drive: rest_storage.clone(),
        resonator_rate: rest_storage.clone(),
        resonator_solve: rest_storage.clone(),
        resonator_state: rest_resonators.clone(),
        zetas: rest_states.clone(),
        solved: rest_states.clone(),
        reads: zeros(widths[receiving]),
    };
    let mut conductance = vec![Rat::zero(); contacts.len()];
    let mut elements: Vec<Vec<ElementTick>> = vec![Vec::new(); rings.len()];
    let mut resonator_ticks: Vec<Vec<ResonatorTick>> = vec![Vec::new(); rings.len()];
    let mut transits: Vec<Vec<TransitTick>> = vec![Vec::new(); contacts.len()];
    let mut resonator_state_bar: Vec<Option<[Vec<Rat>; 2]>> = match end {
        Some(end) => end
            .resonators
            .iter()
            .zip(&rest_resonators)
            .map(|(covector, rest)| match (covector, rest) {
                (Some(covector), Some(_)) => Some(covector.clone()),
                (_, rest) => rest.clone(),
            })
            .collect(),
        None => rest_resonators.clone(),
    };
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
            Ok::<_, HnnError>(scattering_about(
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
        let mut resonator_state_prev = resonator_state_bar.clone();
        // A word that ended stopped after its last junction; a continuing word's every step is a
        // full tick.
        if t + 1 < steps || !word.is_ended() {
            // Reverse the loaded storage-port stage first. Its drive covector then enters the
            // element transpose, so the junction and contact receive the complete loaded path.
            let loaded = indexed(rings.len(), |r| {
                let Some(resonator) = operands.resonators()[r].as_ref() else {
                    return Ok::<Option<ResonatorReverse>, HnnError>(None);
                };
                let trajectory = word.resonances()[r].as_ref().ok_or(HnnError::Realization {
                    what: "a declared resonator trajectory in the word",
                })?;
                let step = trajectory
                    .steps
                    .get(t)
                    .ok_or(HnnError::WordEnded { ticks: steps })?;
                let state_bar = resonator_state_prev[r].as_ref().ok_or(HnnError::Shape {
                    what: "loaded resonator state covectors",
                    expected: 1,
                    found: 0,
                })?;
                let nonlinear = resonator.material().saturation().is_some();
                let velocity_factor = if nonlinear { integer(1) } else { integer(2) };
                let z_image = entries(widths[r], |i| {
                    &h * &state_bar[0][i] + &velocity_factor * &state_bar[1][i]
                        - integer(2) / resonator.admittance() * &storage_bar[r][i]
                });
                let (zbar, zbar_remainder) =
                    split(lattice.as_ref(), z_image, &carried.resonator_rate[r]);
                let image = resonator.solve_transpose(step.phase, &zbar)?;
                let (solved, solved_remainder) =
                    split(lattice.as_ref(), image, &carried.resonator_solve[r]);
                let drive_image = entries(widths[r], |i| &storage_bar[r][i] + &h * &solved[i]);
                let (drive, drive_remainder) =
                    split(lattice.as_ref(), drive_image, &carried.resonator_drive[r]);
                let capacity = resonator.material().forms().0;
                // The Hessian is read at the displacement that produced this tick, with its
                // own executed transpose solve. The nonlinear kick has w'=omega, not 2omega-w.
                let hessian = resonator.force_hessian(step.phase, &step.input[0])?;
                let u_image = sub(&state_bar[0], &scale(&h, &apply_rows(&hessian, &solved)?));
                let capacity_return = apply_rows(capacity, &solved)?;
                let w_image = if nonlinear {
                    capacity_return
                } else {
                    add(
                        &scale(&integer(-1), &state_bar[1]),
                        &scale(&integer(2), &capacity_return),
                    )
                };
                let (u_bar, u_remainder) = split(
                    lattice.as_ref(),
                    u_image,
                    &carried.resonator_state[r].as_ref().expect("declared state")[0],
                );
                let (w_bar, w_remainder) = split(
                    lattice.as_ref(),
                    w_image,
                    &carried.resonator_state[r].as_ref().expect("declared state")[1],
                );
                Ok(Some((
                    drive,
                    [u_bar, w_bar],
                    ResonatorTick {
                        ring: r,
                        tick: t,
                        phase: step.phase,
                        drive: step.drive.clone(),
                        displacement: step.input[0].clone(),
                        velocity: step.input[1].clone(),
                        rate: step.rate.clone(),
                        solved: solved.clone(),
                        output: step.output.clone(),
                    },
                    [
                        zbar_remainder,
                        solved_remainder,
                        drive_remainder,
                        u_remainder,
                        w_remainder,
                    ],
                )))
            })?;
            let mut element_output_bar = storage_bar.clone();
            for (r, item) in loaded.into_iter().enumerate() {
                if let Some((drive, state, tick, [z, solved, drive_rem, u, w])) = item {
                    element_output_bar[r] = drive;
                    resonator_state_prev[r] = Some(state);
                    resonator_ticks[r].push(tick);
                    carried.resonator_rate[r] = z;
                    carried.resonator_solve[r] = solved;
                    carried.resonator_drive[r] = drive_rem;
                    carried.resonator_state[r] = Some([u, w]);
                }
            }
            resonator_state_bar = resonator_state_prev.clone();
            // Each element's reverse step reads the covector on its executed output and remainder
            // through its chart transpose, then writes only its own junction slot.
            let reversed = indexed(rings.len(), |r| {
                let image = rings[r].solve_transpose(&element_output_bar[r])?;
                let (adjoint, remainder) = split(lattice.as_ref(), image, &carried.elements[r]);
                let wave = sub(&scale(&integer(2), &adjoint), &element_output_bar[r]);
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
                    // The conductance's covector at the executed node potential (Lean
                    // `HNN/Word.executed_conductance_return`).
                    let term = conductance_covector(
                        &anchor_bar,
                        &record.arrivals[a][slot],
                        &junction.anchor,
                        &total,
                    );
                    (a, slot, covector, remainder, term)
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
    for ticks in &mut resonator_ticks {
        ticks.reverse();
    }
    let opening = ChangeCovector {
        storage: storage_bar.clone(),
        arrivals: arrival_bar,
        states: displacement_bar
            .into_iter()
            .zip(rate_bar)
            .map(|(displacement, rate)| [displacement, rate])
            .collect(),
        resonators: resonator_state_bar,
    };
    Ok((
        WordReturn {
            opening: storage_bar,
            elements,
            transits,
            resonators: resonator_ticks,
            conductance,
            reads: Vec::new(),
            released: carried.released(),
        },
        opening,
    ))
}
