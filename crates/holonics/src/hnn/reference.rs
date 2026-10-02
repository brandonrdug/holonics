//! **The host reference: the exact implementation of the execution port, and the exposure.**
//!
//! [definition] [`Reference`] implements [`ExecutionPort`] exactly (design (c), "The host
//! reference"). Its [`Resident`] holds the field, the lift point, the receiving parametron's active
//! suffix address ([`ActiveAddress`], shifted at every ingested cell as the lift point is), the
//! constitution, the open moments, the open pending ratios, the staged deposits and the executed
//! charts ([`Charts`]).
//! Every value is in ℚ, in `ℚ(θ)` at a face, or an enclosure read at the exterior, and no float
//! exists. A word carries its inverses as certified lattice charts and its transients on the
//! field's declared lattice with error feedback (the lattice word; [`crate::hnn::chart`]): nothing is
//! rounded away unreported, since every chart's certificate and every released remainder is in the
//! receipts, and every tick's balance closes up to its reported residual within its certified bound.
//!
//! [definition; agent-inferred] **The word's declared precisions** ([`crate::hnn::WordLattice`],
//! coded in [`Field::describe`]), by rule from the finest receiver grain `L_R`, the receiving fan-in
//! `X_w = 2d_R`, the widest local solve `w` and the junction steps `e_max`: the certificate's target
//! `δ = 2^(−D_c)`, `D_c = ⌈log₂(8 L_R X_w w e_max)⌉`; the charts' lattice `L_c = 2D_c`; the
//! transients' lattice `L_w = ⌈log₂(4 L_R X_w e_max s)⌉`, `s = 3` splits a tick. A chart moves one
//! read by at most `1/(4L_R)` over a word (`inverse_chart_deviation`, `executed_adjoint_deviation`
//! with `‖A⁻¹‖∞ ≤ w` by passivity), and the transients by less than `1/(4L_R)`
//! (`feedback_tick_deviation`, at most three splits a tick), so a read moves by less than
//! `1/(2L_R)`, below the grain; the assumptions are `L_ℓ`'s (unit-scale waves) and a non-expansive
//! propagation through the later ticks (the counterfactual bound owed in #62). Campaign 1: `D_c = 19`, `L_c = 38`, `L_w = 15`. Each window
//! warm-starts every chart from the one the resident kept for its operator (a ring's `I − ½K_r`, a
//! contact's `m_a` per conductance carry), refines it by rounded Newton–Schulz steps while its
//! certificate is above the target, and starts cold from the scaled transpose where the warm
//! certificate is above `1/2` (a deposit moves campaign 1's ring elements by 1.4 to 2.3 in the
//! certificate's norm); a chart at an unchanged operator is read again with no step, so a word is a
//! function of the pending ratio's operands, the published constitution and the kept charts.
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
//! tree     each target t_j on the paths its address a_j opens, in cell order        landmark tree (`compression::landmark::context`)
//! W_c,g    sample (c_t, −u_t) at each tick of the element's window                  normal law
//! E_g      sample (M_g[c] ν̂(n_g), −P^(c−τ_g) s̄_g(0)) per phase with counts           normal law (ruling B's normalized marginal)
//! f_g      G = (K̄ + K̄ᵀ) f,  K̄ = Σ_t u_t x̄_tᵀ;   slices ∂/∂u_ρ = σ_ρ[(x̄·v)u − (u·v)x̄], ∂/∂v_ρ likewise
//! q_g      the class covector g_σρ = Σ_t Re⟨u_t, A_ρ x̄_t⟩ carried to q by the transpose of q ↦ Δ
//! E_g^(δ)  ∂/∂e_ρ = Σ_c w_ρc h_c,  ∂/∂a_ρ = Σ_c (e_ρ·h_c) Ĉ_c b_ρ, ∂/∂b_ρ likewise, h_c = P^(c−τ) s̄(0),
//!          Ĉ_c = C_g(δ)[c, ·, a_δ] ν̂(N_a) ⊗ e_(a_δ), the indexed normalized column (ruling B)
//! c,b,F    C̄ = Σ 2 r̄ (w − ω)ᵀ,  K̄ = −h Σ r̄ (u + ½hω)ᵀ,  D̄ = −h Σ r̄ ωᵀ;  ∂/∂c = (C̄ + C̄ᵀ) c, …
//! ```
//!
//! each only at loci inside the causal diamond of the source rings and the pending ratio's
//! receiver, and each statistic only over the locus's time-indexed window
//! ([`crate::hnn::retention::Diamond`]).
//!
//! [definition] **The Holarchy and its aeon at the mount.** A mount is the resident's
//! declaration: it certifies that the field at the mounted constitution is a Holarchy that glues
//! (`Field::holarchy`, `Holon::interconnect`'s typed gluing, refused with its defect), and it keeps
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
//! [definition] **The exposure** ([`Reference::expose`], design (d), campaign 1's protocol under
//! prequential scoring): the cut, exactly the field's declared population (so the `n*` guard holds), is
//! read in order, as one stream, into one moment; at each receiving window (an epoch of the cut's
//! cell clock at the receiver's section, `hnn::receiving::ReceivingPhases::windows`; U5) `refine`
//! runs on the moment and `compare` against the window's `A` cells, whose return is then deposited, held-out
//! windows included (prequential: every comparison is scored at the standing before its own
//! deposit, as the online baselines are); then those cells are ingested; the aeon boundary is the joint clock's carry-out,
//! and after it keys are located on the crib that closed the aeon: its last `W_crib` cells, past
//! and already scored, truncated after the last held-out cell so no held-out cell is read (review
//! D1). The budget stop admits no further deposit and the run continues, reported incomplete. A
//! deadline ([`Reference::with_deadline`]) ends the reading after its windows, reported incomplete
//! at the cell it stopped at. Its readout ([`Exposure`]) is design (f)'s measurement, with `Kt`
//! charging the published keys, and beside it, exterior, the host's wall time by phase
//! ([`WallTimes`]).
//!
//! [definition; agent-inferred] **The kept read.** `refine` keeps the word it ran (its operands and
//! per-tick waves without the borrow of its field, `hnn::word::KeptWord`) and the wave's faces it
//! read, in the pending slot, tagged with the commit of the constitution it read them at. `compare`
//! takes them when that commit is still the published one and reads again otherwise (a comparison
//! observed after an update is read through the contemporary constitution); a deposit and a
//! collapse publish a constitution and drop every kept read. A word is a function of the pending
//! ratio's operands, the published constitution and the resident's kept charts (a chart at an
//! unchanged operator is read again with no step), so the kept read is that function's value and
//! the compare returns the same either way (the test
//! `a_compare_returns_the_same_with_and_without_the_refines_kept_read`). The tree part of the
//! combined face is read at compare in either case, at the published constitution and each phase's
//! causal address (the landmark tree, `PendingRatio::against`). The pending ratio still holds operands
//! only (guard 3), the kept word is consumed by its own return (guard 2), and the
//! kept read is not state: the state bits do not count it, and a clone of the resident drops it.
//!
//! [definition; agent-inferred] **The host realization** (CLAUDE.md, the hardware law;
//! `hnn::realization`). Within a method the host runs these regions together on its cores:
//! the work-stealing pool of the `rayon` crate, one task per region, regions nested in regions, each
//! region's own arithmetic on one worker. Every region reads operands no region writes and writes
//! only its own slot; the slots are collected in index order and every reduction runs afterwards in
//! that order, so every value is the serial realization's, which is the same code on one worker
//! (the test `one_worker_and_many_return_the_same_values`).
//!
//! | Where | Regions that run together | Why they commute |
//! |---|---|---|
//! | a word's open (`refine`, `compare`'s read, the deposit's re-read) | the rings' operands, then the contacts', each refining its own chart from its own kept chart; within them, a Gram's rows | each reads its own material (the standings, its own screws) and its own kept chart, and writes its own operands; the refined charts are kept afterwards, by key |
//! | a tick of the word | the junctions, then the elements, then the transits; the rings' and contacts' power terms | a junction reads its own storage, arrivals and anchor remainder, an element its own junction and storage remainder, a transit its two ends' outgoing waves, its own state and its own remainders; the balance terms and the power are summed afterwards in ring, then contact, order |
//! | the receiving read | the receiving epochs; within each, the map's `2\|A\|` rows, then the classes' grain cells | each row and class reads the shared anchor and writes its own logit or cell |
//! | the tree read at compare | the receiving phases, each reading the published tree at its own address through its own working overlay (the window's earlier phases' deposits, built first in cell order by `compression::landmark::context::Landmarks::window`; run together by `hnn::receiving::window_faces`) | the published tree and every overlay are read, never written, until the deposit |
//! | the faces and the Holon ratio | the receiving phases' faces, then their ratios and code lengths | each reads its own read and target |
//! | the compare phase ([`compare_phase`], campaign 2) | the tree face at the grain's code lengths (its phases together), beside the receiver's population's score, the target phases, the Holon ratio and its covector (the population's steps in cell order inside) | both read the shared immutable faces and targets and write their own readings |
//! | `pull_back` | per step in reverse, the junctions at their recorded anchors, then the elements (each through its executed chart's transpose), then the transits (each through its executed chart's transpose, and each channel coordinate), then the junctions' reverse Swings at their executed weights (and each coordinate) | each reads its step's record, its own covectors and its own adjoint remainders, and writes its own; the conductance terms are added afterwards, in contact, then ring and incidence, order |
//! | [`compose`] | the receiving map's gradient by row blocks; the rings (their ticks' charts, slices and contrast port's rows); the standings; the source ring's phases and pair-port ranks; the contacts (their ticks' charts and three forms) | each reads the word's return and its own material; the parts are joined in ring and contact order, so the deposit's steps stand in the serial order |
//! | `deposit` ([`Constitution::deposited`]) | the loci the deposit names, each running its own steps in the deposit's order with its own budgeted carry; within a normal law, its samples' terms, its map update's row blocks, its Gram's rows and its carried entries | loci share no material, remainder or budgeted carry, and entries share nothing; the refusal returned is the first in the deposit's order |
//!
//! The regions stay serial where their arithmetic is one owner's integer loop: a chart's
//! refinement and product (`crate::hnn::chart`, 64-bit words and 128-bit sums under the ℓ1
//! certificate) and `IntegralMatrix::{outer_sum, symmetric_times}` (`crate::ratio::linear`) run on
//! one worker each; the exact inversion runs only where a chart's cold start fails (never on the
//! standing real cut's first 24 windows) and in the observability rank at the mount. The receipts
//! (24 windows of the standing real cut: the host realization's, serial against parallel with
//! identical readouts; and the lattice word's, before and after it landed) are the notebook's
//! (`research/notebook/hnn_design/README.md`).
//!
//! [open] **`ExactWork`'s operation counts.** The exposure's work counts the entries written, their
//! bits, the peak, the resident entries and the span; its additions, multiplications and divisions
//! stay zero. They are the integer multiply-adds and the normalizations (one `gcd` each) of
//! `ratio::linear::vector::{integer_dot, row_dot, IntegralMatrix::{outer_sum, to_rows,
//! symmetric_times}, combination}`, `ExactRatMatrix::{apply, inverse}`, the ticks'
//! `propagation::{Rows::apply, junction_scattering, element_step, transit, global_power}`, the return,
//! [`compose`], and the deposit's `gram_sum`, normal law and carry; counting them needs an
//! `ExactWork` threaded through each of those owners' loops (most outside `hnn`), so they are left
//! uncounted rather than estimated from shapes.

use std::collections::BTreeMap;
use std::ops::Range;
use std::time::{Duration, Instant};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use crate::aeon::{ClockLift, EnclosedLedger};
use crate::compression::cost::ceil_log2;
use crate::compression::landmark::context::baseline::{BaselineCodes, Baselines};
use crate::compression::landmark::context::{
    ChartReport, LandmarkDeclaration, Landmarks, Letter, PassageCode, Widths, code_length,
    letter_address,
};
use crate::geometry::RatVec3;
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartReading, ChartStart, Charts, Remainders};
use crate::hnn::constitution::{
    CAMPAIGN_ONE_BUDGET, Carrier, CarrierBits, Constitution, DepositReading, FactorGradient, FactorStep,
    Family, LandmarkStep, LinearLocus, LinearStep, Locus, Reach, Sample,
};
use crate::hnn::contact::{SiteReading, site_readings};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::keys::{self, KeyLocation};
use crate::hnn::moment::{Ingested, PopulationChart, SourceMoment};
use crate::hnn::pending::{Against, PendingRatio};
use crate::hnn::port::{
    Census, ContactPullback, Deposit, ExecutionPort, Handle, MomentId, PendingId, PortReceipt,
    Pullback, ReceiptDetail, ResonatorPullback, RingPullback, StagedId, Transpose, WordReturn,
    port_receipt, release_width, resonance_reading, source_order, wrote_all,
};
use crate::hnn::propagation::{Operands, contact_exponent, path_attenuation};
use crate::hnn::ratio::{Faces, HolonRatio, PhaseRatio, RatioCovector, target_phases};
use crate::hnn::realization::{apply_rows, indexed, outer_rows};
use crate::hnn::receiving::{
    ActiveAddress, ReceivingPhases, ReceivingStep, Scored, tree_code_length,
};
use crate::hnn::retention::{AeonBoundary, Diamond, aeon_readings, collapse, contained, separator};
use crate::hnn::word::{KeptWord, PowerForm, Word, WordBalance};
use crate::holon::contact::FeatureCovector;
use crate::navigator::Clock;
use crate::ratio::algebraic::{ExactInterval, interval_difference, interval_sum};
use crate::ratio::exponentiated::power_of_two;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::work::ExactWork;
use crate::ratio::{Rat, integer};
use crate::receiver::population::PortPopulation;
use crate::receiver::reception::{Component, InteractionReturn, SourceOrder};
use crate::receiver::release::{DecisionRule, LawfulOptions, ReleaseReturn, release};

// -------------------------------------------------------------------------------------------
// the resident

#[derive(Debug)]
struct PendingSlot {
    ratio: PendingRatio,
    emitted: Vec<Vec<Rat>>,
    kept: Option<KeptRead>,
}

/// [definition; agent-inferred] **The refine's read, kept for its compare** (module header, "The
/// kept read"): the word the refine ran, without the borrow of its field, and the faces it read,
/// tagged with the commit of the constitution it read them at.
#[derive(Debug)]
struct KeptRead {
    commit: u64,
    word: KeptWord,
    faces: Faces,
}

/// A clone of a slot drops its kept read: a word is not `Clone` (guard 2), and the clone's compare
/// reads again, to the same values.
impl Clone for PendingSlot {
    fn clone(&self) -> Self {
        Self {
            ratio: self.ratio.clone(),
            emitted: self.emitted.clone(),
            kept: None,
        }
    }
}

impl PendingSlot {
    /// Its exact bits: the pending ratio's and the emitted logits' (the face a delayed compare
    /// returns its residual against), each value by its numerator's and denominator's bits. The
    /// kept read is not counted: it is a function of these operands at the published constitution,
    /// and dropping it changes no value.
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
    /// The arrived targets' code length at a constitution under its receiver's population (ruling
    /// A), read from the executed faces (the resident's charts warm-started and refined), the
    /// constitution's tree at the targets' addresses and its population's likelihoods, with the
    /// charts' readings.
    fn code_length(
        &self,
        field: &Field,
        constitution: &Constitution,
        charts: &mut Charts,
    ) -> Result<(ExactInterval, Vec<ChartReading>), HnnError> {
        let (word, against) =
            self.ratio
                .read_against(field, constitution, charts, &self.targets)?;
        let scored = self.ratio.scored(constitution, &against, &self.targets)?;
        Ok((window_code_length(&scored.model)?, word.operands().charts()))
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

/// **A window's code length under the receiver's population**: the phases' enclosures summed on
/// the grid.
pub fn window_code_length(model: &[ExactInterval]) -> Result<ExactInterval, HnnError> {
    model
        .iter()
        .try_fold(ExactInterval::point(Rat::zero()), |sum, phase| {
            Ok(interval_sum(&sum, phase)?)
        })
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

/// [definition] **The resident of the host reference**: the field, the lift point, the receiving
/// parametron's active suffix address, the constitution, the open moments, pending ratios and
/// staged deposits, the admitted family of the
/// last boundary, the aeon's clock state on the certified Holarchy's parametric orientation, the
/// first law's ledger with the targets it has reached, the bits the collapses released, and the
/// budget stop once it comes.
#[derive(Clone, Debug)]
pub struct Resident {
    field: Field,
    current: Current,
    address: ActiveAddress,
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
    charts: Charts,
    tally: ChartTally,
    wall: WallTimes,
}

/// [definition] **The executed charts' tally** over a resident's words (the lattice word): the chart
/// refinements read, how many started cold (from the scaled transpose) and how many from one exact
/// inverse, the rounded Newton–Schulz steps they took, and the largest certificate read against the
/// declared target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartTally {
    pub reads: u64,
    pub cold: u64,
    pub seeded: u64,
    pub steps: u64,
    pub largest: Rat,
    pub target: Rat,
}

impl ChartTally {
    /// No chart read yet, against the field's declared target.
    pub fn new(field: &Field) -> Self {
        Self {
            reads: 0,
            cold: 0,
            seeded: 0,
            steps: 0,
            largest: Rat::zero(),
            target: field
                .word_lattice()
                .map_or_else(Rat::zero, |word| word.target()),
        }
    }

    /// Count one word's chart readings.
    pub fn read(&mut self, readings: &[ChartReading]) {
        for reading in readings {
            self.reads += 1;
            match reading.start {
                ChartStart::Warm => {}
                ChartStart::Transpose => self.cold += 1,
                ChartStart::Exact => self.seeded += 1,
            }
            self.steps += u64::from(reading.steps);
            if reading.certificate > self.largest {
                self.largest = reading.certificate.clone();
            }
        }
    }
}

/// [definition; agent-inferred] **The host's wall time by phase**, summed over the resident's
/// methods: the host's wall clock read around each phase, in the exterior chart of a person
/// (milliseconds when printed). No law, receipt, state bits or description reads it, and it holds
/// no clock of the machine (guard 6 names those): two runs with identical exact readouts differ
/// here. Each phase is timed only when it completes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WallTimes {
    /// `refine`: the word opened at the cut, run over its window and read at the grain.
    pub refine_read: Duration,
    /// `refine`: the word's end read (the released change), the path at the cut and the loci
    /// reached.
    pub release: Duration,
    /// `refine`: a card's resident resonator ticks and the host's reading of their balance
    /// (campaign 2, `hnn::ring`); zero on the host, whose resonators tick inside the word.
    pub resonators: Duration,
    /// `compare`: the contemporary read, when the refine's kept read is not at the published
    /// commit.
    pub compare_read: Duration,
    /// `compare`: the landmark tree read at each phase's causal address and added to the wave's
    /// faces (the landmark tree; `PendingRatio::against`); on a card, its launches and the host's
    /// completion of the class faces, the transfers apart.
    pub tree_read: Duration,
    /// `compare`: a card's transfers of the tree read (the letters and digits up, the splits
    /// down); zero on the host.
    pub tree_transfer: Duration,
    /// `compare`: the residual, the target phases, the Holon ratio and its covector, and the tree
    /// face alone's code lengths.
    pub holon: Duration,
    /// `compare`: the word's return.
    pub pull_back: Duration,
    /// `compare`: the composition onto the loci ([`compose`]).
    pub compose: Duration,
    /// `deposit`: the successor constitution ([`Constitution::deposited`]).
    pub deposited: Duration,
    /// `deposit`: a card's mirror of the landmark tree moved by the deposit's steps (the
    /// opened-path update, its transfers included); zero on the host, whose tree moves inside
    /// `deposited`.
    pub tree_deposit: Duration,
    /// `deposit`: a card's normal-law mirror (the Gram's and the map's outer updates, their
    /// budgeted splits and the reaches, campaign 2), read against the successor's, when the mirror
    /// runs (the GPU suite's parity tests); zero on the exposure's path and on the host.
    pub normal_deposit: Duration,
    /// `deposit`: the arrived targets re-read at the successor.
    pub reread: Duration,
    /// `ingest`: the cells taken into the moment.
    pub ingest: Duration,
}

impl WallTimes {
    /// The phases by name, in the order the methods run them.
    pub fn phases(&self) -> [(&'static str, Duration); 14] {
        [
            ("refine read", self.refine_read),
            ("release", self.release),
            ("resonators", self.resonators),
            ("compare read", self.compare_read),
            ("tree transfer", self.tree_transfer),
            ("tree read", self.tree_read),
            ("holon and covector", self.holon),
            ("pull_back", self.pull_back),
            ("compose", self.compose),
            ("deposited", self.deposited),
            ("tree deposit", self.tree_deposit),
            ("normal deposit", self.normal_deposit),
            ("re-read", self.reread),
            ("ingest", self.ingest),
        ]
    }

    /// The phases' sum.
    pub fn total(&self) -> Duration {
        self.phases().iter().map(|(_, time)| *time).sum()
    }
}

impl std::ops::AddAssign for WallTimes {
    fn add_assign(&mut self, other: Self) {
        self.refine_read += other.refine_read;
        self.release += other.release;
        self.resonators += other.resonators;
        self.compare_read += other.compare_read;
        self.tree_read += other.tree_read;
        self.tree_transfer += other.tree_transfer;
        self.holon += other.holon;
        self.pull_back += other.pull_back;
        self.compose += other.compose;
        self.deposited += other.deposited;
        self.tree_deposit += other.tree_deposit;
        self.normal_deposit += other.normal_deposit;
        self.reread += other.reread;
        self.ingest += other.ingest;
    }
}

/// [definition] **The compare phase's readings** ([`compare_phase`]): the tree face at the grain's
/// code lengths, the window scored by the receiver's population, the Holon ratio and its covector.
#[derive(Clone, Debug)]
pub struct ComparePhase {
    pub tree_grain: Vec<ExactInterval>,
    pub scored: Scored,
    pub holon: HolonRatio,
    pub covector: RatioCovector,
}

/// [definition; agent-inferred] **The compare phase under the hardware law** (CLAUDE.md; campaign
/// 2): the tree face at the grain's code length of each phase (`tree_code_length`, a reading of the
/// exposure), and, beside it, the receiver's population's score, the target phases, the Holon ratio
/// and its covector. The two regions read the shared immutable faces and targets and write their
/// own readings, so they run together (`rayon::join`), and the phases of the first run together
/// (`hnn::realization`); the population's steps stay in cell order inside the second. Every value is
/// the serial realization's. The host reference and every device realization call it.
pub fn compare_phase(
    field: &Field,
    constitution: &impl ConstitutionRead,
    ratio: &PendingRatio,
    against: Against,
    targets: &[usize],
) -> Result<ComparePhase, HnnError> {
    if against.trees.len() != targets.len() {
        return Err(HnnError::Shape {
            what: "one tree face per target",
            expected: targets.len(),
            found: against.trees.len(),
        });
    }
    let phases = ratio.phases();
    let (tree_grain, rest) = rayon::join(
        || {
            indexed(against.trees.len(), |j| {
                tree_code_length(&against.trees[j], targets[j])
            })
        },
        || -> Result<(Scored, HolonRatio, RatioCovector), HnnError> {
            let scored = ratio.scored(constitution, &against, targets)?;
            let anchors = target_phases(field, ratio.anchor(), phases.ring(), targets)?;
            let holon = HolonRatio::compare(against.faces.clone(), targets, &anchors)?;
            let covector = holon.covector()?;
            Ok((scored, holon, covector))
        },
    );
    let (scored, holon, covector) = rest?;
    Ok(ComparePhase {
        tree_grain: tree_grain?,
        scored,
        holon,
        covector,
    })
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

    /// The receiving parametron's active suffix address (the landmark tree): the last cells ingested,
    /// newest first, at the deepest declared receiver's depth.
    pub fn address(&self) -> &ActiveAddress {
        &self.address
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
    #[cfg(test)]
    pub(crate) fn awaiting_boundary(&self) -> bool {
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

    /// The host's wall time by phase since the mount (exterior; [`WallTimes`]).
    pub fn wall(&self) -> &WallTimes {
        &self.wall
    }

    fn fresh(&mut self) -> u64 {
        self.next += 1;
        self.next
    }

    /// **Drop every kept read** when a constitution is published (a deposit's successor, a
    /// collapse's descent): each was read at the constitution published before, so each pending
    /// ratio's compare reads again at the contemporary one (module header, "The kept read").
    fn forget_kept_reads(&mut self) {
        for slot in self.pending.values_mut() {
            slot.kept = None;
        }
    }

    /// Whether a pending ratio holds its refine's kept read (the tests' view of the reuse).
    #[cfg(test)]
    pub(crate) fn holds_kept_read(&self, pending: &PendingId) -> bool {
        self.pending
            .get(pending)
            .is_some_and(|slot| slot.kept.is_some())
    }

    /// The exact bits of the resident's state: the lift point, the active suffix address, the open
    /// moments, the pending ratios with their emitted logits, the staged deposits, the first law's
    /// arrived operand, the constitution and the executed charts ([`Charts`], the representation
    /// of the solves the words execute).
    pub fn state_bits(&self) -> u64 {
        let lift: u64 = self
            .current
            .lift()
            .iter()
            .map(|x| x.bits() + 1)
            .sum::<u64>()
            + self.address.bits(self.field.alphabet());
        let moments: u64 = self.moments.values().map(SourceMoment::dense_bits).sum();
        let pending: u64 = self.pending.values().map(PendingSlot::bits).sum();
        let staged: u64 = self.staged.values().map(|slot| slot.deposit.bits()).sum();
        let arrived = self.arrived.as_ref().map_or(0, Arrived::bits);
        lift + moments
            + pending
            + staged
            + arrived
            + self.constitution.exact_bits()
            + self.charts.bits()
    }

    /// **The executed charts** the resident keeps between windows (the lattice word).
    pub fn charts(&self) -> &Charts {
        &self.charts
    }

    /// The executed charts' tally since the mount.
    pub fn tally(&self) -> &ChartTally {
        &self.tally
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
/// capacity and constitution budget, and an exposure's deadline if one is set. No step is declared:
/// every locus's step is certified at its deposit (`hnn::constitution`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pending_capacity: usize,
    budget: u64,
    deadline: Option<u64>,
}

impl Reference {
    /// Campaign 1's declarations: `B_Θ = 2^33` and a pending capacity of 64 (every locus's step
    /// certified at every deposit).
    pub fn campaign_one() -> Self {
        Self::new(64, CAMPAIGN_ONE_BUDGET)
    }

    pub fn new(pending_capacity: usize, budget: u64) -> Self {
        Self {
            pending_capacity,
            budget,
            deadline: None,
        }
    }

    /// [definition; agent-inferred] **An exposure's deadline** (design (d), the budget and stop
    /// rule: "a timeout is reported the same way: an unfinished run at its deadline"). With one set,
    /// [`Reference::expose`] reads at most `windows` receiving windows of its cut, then stops and
    /// reports the run incomplete at the cell it stopped at ([`Exposure::deadline`]). The cut is
    /// still exactly the declared population, so the `n*` guard holds; the deadline only cuts the
    /// reading short and changes nothing it reads. The deadline is counted in the exposure's own
    /// windows, not in wall time. It limits one run from outside: it enters no law of the port and
    /// no description (`Field::describe`). [agent-inferred: a smoke run on campaign 1's field needs
    /// a limit below `n*`, which a shorter cut cannot give, since the field refuses any population
    /// shorter than `n*`.]
    pub fn with_deadline(self, windows: u64) -> Self {
        Self {
            deadline: Some(windows),
            ..self
        }
    }

    /// **Mount on a declared constitution** (a transfer, and the resident's declaration): the field
    /// at the constitution is certified a Holarchy that glues (`Field::holarchy`, refused with its
    /// gluing defect), whose parametric orientation is the field's joint clock lift and carries the
    /// resident's aeons; the admitted family is the field's declared receivers at that
    /// constitution.
    pub fn mount_with(
        &self,
        field: &Field,
        current: &Current,
        constitution: Constitution,
    ) -> Result<Resident, HnnError> {
        let parametric = field.holarchy(&constitution)?.parametric();
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
            address: ActiveAddress::of_field(field, current, &constitution)?,
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
            charts: Charts::new(),
            tally: ChartTally::new(field),
            wall: WallTimes::default(),
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
fn receipt(
    field: &Field,
    ticks: &[u64],
    unit: &Rat,
    work: ExactWork,
    detail: ReceiptDetail,
) -> Result<PortReceipt, HnnError> {
    let _ = field;
    port_receipt(ticks, unit, work, detail)
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
        let constitution = Constitution::initial(field, self.budget)?;
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
        let start = Instant::now();
        let ingested = open.ingest(&field, &mut resident.current, &codes)?;
        // The receiving parametron's active suffix address receives the cells the moment took, each
        // tick's letter read by its register's clock, which stays the lift point's (its windings
        // since the aeon's opening, which the carry-out moves to its own lift point), and its
        // contact letters' site kinds then refresh from the published constitution, after the
        // ingest and never inside it (`hnn::receiving::LetterReader`).
        for &code in &codes[..ingested.cells] {
            resident.address.receive(code)?;
        }
        let opening = if ingested.carry_out {
            resident.current.lift()
        } else {
            &resident.aeon.opening
        };
        if !resident
            .address
            .reader()
            .agrees(&field, &resident.current, opening)
        {
            return Err(HnnError::Shape {
                what: "the address register's clock against the lift point",
                expected: field.rings().len(),
                found: 0,
            });
        }
        resident.address.refresh(&field, &resident.constitution)?;
        resident.wall.ingest += start.elapsed();
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
        resident.address.synchronize(&field, &resident.current)?;
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
            &resident.address,
            phases,
            resident.constitution.commit(),
        )?;
        let field = &resident.field;
        let start = Instant::now();
        let (word, faces) =
            ratio.read_charted(field, &resident.constitution, &mut resident.charts)?;
        let read = start.elapsed();
        let start = Instant::now();
        let released = word.released()?;
        resident.tally.read(&released.charts);
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
                charts: released.charts.clone(),
                remainders: released.remainders.clone(),
                last: released.last.clone(),
                resonators: released.resonators.clone(),
                word: Box::new(WordBalance::of(&released)),
            },
        )?;
        receipt.balances = released.balances;
        receipt.unresolved = faces.faces.iter().map(|face| face.fibres()).collect();
        let order = source_order(field, ratio.anchor(), ratio.moment().cells());
        let kept = KeptRead {
            commit: resident.constitution.commit(),
            word: word.keep(),
            faces: faces.clone(),
        };
        resident.wall.refine_read += read;
        resident.wall.release += start.elapsed();
        let id = PendingId(resident.fresh());
        resident.pending.insert(
            id,
            PendingSlot {
                ratio,
                emitted: faces.logits.clone(),
                kept: Some(kept),
            },
        );
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(faces),
                pullback: Component::Absent(
                    "refine is forward only; its word is kept for the compare at its commit",
                ),
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
        let commit = resident.constitution.commit();
        let slot = resident
            .pending
            .get_mut(&pending)
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
        // The kept read is the contemporary read when the constitution is still the one it was
        // read at; otherwise the word is read again at the published constitution (module header,
        // "The kept read").
        let kept = slot.kept.take().filter(|kept| kept.commit == commit);
        let slot = &*slot;
        let ratio = &slot.ratio;
        let mut wall = WallTimes::default();
        let (word, faces) = match kept {
            Some(KeptRead { word, faces, .. }) => (word.resume(&field), faces),
            None => {
                let start = Instant::now();
                let read =
                    ratio.read_charted(&field, &resident.constitution, &mut resident.charts)?;
                resident.tally.read(&read.0.operands().charts());
                wall.compare_read = start.elapsed();
                read
            }
        };
        // The tree part of the combined face at each phase's causal address (the landmark tree).
        let start = Instant::now();
        let against = ratio.against(&resident.constitution, &faces, &targets)?;
        wall.tree_read = start.elapsed();
        let start = Instant::now();
        let residual: Vec<Vec<Rat>> = faces
            .logits
            .iter()
            .zip(&slot.emitted)
            .map(|(now, then)| now.iter().zip(then).map(|(a, b)| a - b).collect())
            .collect();
        // The tree face at the grain, the receiver's scored face (its population over the tree's
        // and the combined face, ruling A, received phase by phase; beside it the tree's executed
        // face alone), the Holon ratio and its covector ([`compare_phase`]).
        let ComparePhase {
            tree_grain,
            scored,
            holon,
            covector,
        } = compare_phase(&field, &resident.constitution, ratio, against, &targets)?;
        let map = resident
            .constitution
            .receiving_map(phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?
            .clone();
        wall.holon = start.elapsed();
        let start = Instant::now();
        let back = word.pull_back(&covector, &map, &ratio.anchor()[phases.ring()], &phases)?;
        wall.pull_back = start.elapsed();
        let start = Instant::now();
        let (pullback, deposit) = compose(
            &field,
            &resident.constitution,
            ratio,
            &back,
            &targets,
            &scored.steps,
        )?;
        wall.compose = start.elapsed();
        let code_length = window_code_length(&scored.model)?;
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
            released: back.released.clone(),
            tree: scored.tree,
            tree_grain,
            model: scored.model,
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
        resident.wall += wall;
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
        let start = Instant::now();
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
        let deposited = start.elapsed();
        let start = Instant::now();
        // The successor re-read can refuse late (for example, a newly certified loaded resonator
        // chart). Keep its chart and tally writes private until the receipt and first-law ledger
        // also accept the same reread.
        let mut next_charts = resident.charts.clone();
        let (reread, readings) = arrived.code_length(&field, &next, &mut next_charts)?;
        let mut next_tally = resident.tally.clone();
        next_tally.read(&readings);
        let reread_time = start.elapsed();
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
        let mut next_ledger = resident.ledger.clone();
        next_ledger.deposit(reread)?;
        resident.staged.remove(&staged);
        resident.constitution = next;
        resident.charts = next_charts;
        resident.tally = next_tally;
        resident.ledger = next_ledger;
        resident.forget_kept_reads();
        resident.wall.deposited += deposited;
        resident.wall.reread += reread_time;
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
        let mut word =
            slot.ratio
                .open_charted(field, &resident.constitution, &mut resident.charts)?;
        resident.tally.read(&word.operands().charts());
        let anchors = word.forward(&phases)?;
        let reads = anchors
            .iter()
            .map(|anchor| phases.read(field, &resident.constitution, &current, anchor))
            .collect::<Result<Vec<_>, _>>()?;
        // No cell of the window is released yet: every phase reads the tree at the window's
        // opening address (`ActiveAddress::phase`).
        let wave = Faces::of_reads(&reads, phases.grain())?;
        let faces = slot
            .ratio
            .against(&resident.constitution, &wave, &[])?
            .faces;
        // The width is read from the receiving phases' fibres; the tolerance is their grain.
        let width = release_width(&phases, &faces)?;
        let tolerance = Rat::new(BigInt::one(), BigInt::from(phases.grain()));
        let options = LawfulOptions::assemble(&width, tolerance.clone(), None, false)?;
        let decided = release(decision, &options)?;
        let released = matches!(decided, ReleaseReturn::Released { .. });
        let split = if resident
            .constitution
            .ring_resonator(phases.ring())
            .is_some()
        {
            [
                Component::Absent("the loaded resonator has no campaign-3 RIDE/FOUND read"),
                Component::Absent("the loaded resonator has no campaign-3 RIDE/FOUND read"),
            ]
        } else {
            match anchors.last() {
                Some(anchor) => resonance_reading(field.ring(phases.ring()), anchor)?,
                None => [
                    Component::Absent("the window read no anchor"),
                    Component::Absent("the window read no anchor"),
                ],
            }
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
        // The collapse publishes the descended constitution at the same commit.
        resident.forget_kept_reads();
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
                let (reread, readings) =
                    arrived.code_length(&field, &resident.constitution, &mut resident.charts)?;
                resident.tally.read(&readings);
                resident.ledger.release(reread)?;
            }
        }
        let first_law = resident.ledger.close();
        let literal = first_law.against_literal(&code_length(&Rat::new(
            BigInt::one(),
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

/// **The base pump form at one phase**, before the learned squared amplitude `g_P²` scales its
/// strength. Its node blocks are assembled on the ring's declared realified coordinates.
fn resonator_pump_base_form(
    pump: &crate::hnn::ring::PumpDeclaration,
    phase: usize,
    width: usize,
) -> Result<ExactRatMatrix, HnnError> {
    let unit = pump.with_strength(Rat::one())?;
    let block = unit.block(phase);
    let mut rows = vec![vec![Rat::zero(); width]; width];
    for node in 0..(width / 2) {
        for i in 0..2 {
            for j in 0..2 {
                rows[2 * node + i][2 * node + j] = block[i][j].clone();
            }
        }
    }
    matrix_of(rows, width)
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
///
/// [definition; agent-inferred] **Its realization** (module header, "The host realization"): the
/// receiving map's gradient by row blocks, then the rings (each reading only its own ticks and
/// material, the slices of a ring each reading only their own pair), the standings, the source
/// rings (the pair port's ranks each reading only their own reads) and the contacts (each reading
/// only its own ticks and factors) run together, each writing only its own part; the parts are
/// joined afterwards in ring and contact order, so the deposit's steps stand in the serial order.
pub fn compose(
    field: &Field,
    constitution: &Constitution,
    ratio: &PendingRatio,
    back: &WordReturn,
    targets: &[usize],
    steps: &[ReceivingStep],
) -> Result<(Pullback, Deposit), HnnError> {
    let phases = ratio.phases();
    let diamond = Diamond::of(field, phases);
    let released = constitution.released();
    let retained = |locus: Locus| diamond.retains(field, locus) && !released.contains(&locus);
    let receiving = phases.ring();
    let composed = compose_return(
        field,
        constitution,
        &diamond,
        ratio.anchor(),
        &ratio.current(field)?,
        ratio.moment(),
        back,
    )?;
    // The receiving parametron's landmark tree (`compression::landmark::context`): each compared target deposits on
    // the paths its phase's causal address opens, in cell order, when the comparison reached the
    // receiving locus.
    if targets.len() != back.reads.len() {
        return Err(HnnError::Shape {
            what: "the compared targets against the receiving reads",
            expected: back.reads.len(),
            found: targets.len(),
        });
    }
    let landmarks: Vec<LandmarkStep> = if retained(Locus::ReceivingMap(receiving)) {
        ratio
            .addresses(targets)?
            .into_iter()
            .zip(targets)
            .map(|(address, &class)| LandmarkStep {
                ring: receiving,
                address,
                class,
            })
            .collect()
    } else {
        Vec::new()
    };
    // The word's reach (the certified step's reading): the receiver reads its anchor at each
    // receiving epoch `e_j`, after `e_j` full ticks, and the moment enters once, at the open.
    let reach = Reach {
        receiver: receiving,
        stations: phases.epochs().map(|epoch| epoch as u64).collect(),
        entries: vec![0],
        phases: composed.phases,
    };
    Ok((
        composed.pullback,
        Deposit::new(
            constitution.commit(),
            composed.linear,
            composed.factors,
            composed.reached,
        )
        .with_reach(reach)
        .with_landmarks(landmarks)
        .with_receiving(if retained(Locus::ReceivingMap(receiving)) {
            steps.to_vec()
        } else {
            Vec::new()
        }),
    ))
}

/// [definition; agent-inferred] **A word return composed onto the loci** ([`compose_return`]): the
/// complete pullback, the linear loci's windows, the factor families' steps, the loci reached, and
/// the most phases one source moment occupied (the phase-binned counts one injection sums, which
/// the certified step's reach reads), before any landmark tree or receiving face is joined to them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedReturn {
    pub pullback: Pullback,
    pub linear: Vec<LinearStep>,
    pub factors: Vec<FactorStep>,
    pub reached: Vec<Locus>,
    pub phases: u64,
}

/// **A word return composed onto every locus inside a causal diamond** ([`compose`]'s law, read
/// from its operands directly): the receiving map `R` of the diamond's receiver from the return's
/// reads, every ring's element and standing, the source rings' ports and moment from the return's
/// opening covector against the moment's counts at the lift `anchor`, the loaded resonators and
/// the contacts, each only at loci the diamond retains and the constitution has not released.
/// The compare composes a word's return in its pending ratio's diamond and joins the landmark tree
/// to it; U6's retired linear readout (batch H) composed a refinement's joined return in the
/// refinement's diamond and joined nothing else.
pub fn compose_return(
    field: &Field,
    constitution: &Constitution,
    diamond: &Diamond,
    anchor: &[BigInt],
    current: &Current,
    moment: &SourceMoment,
    back: &WordReturn,
) -> Result<ComposedReturn, HnnError> {
    use crate::ratio::linear::vector::{Chart, combination, integral};
    let released = constitution.released();
    let retained = |locus: Locus| diamond.retains(field, locus) && !released.contains(&locus);
    let alphabet = field.alphabet();
    let h = field.step().clone();
    let mut linear: Vec<LinearStep> = Vec::new();
    let mut factors: Vec<FactorStep> = Vec::new();
    let mut phases = 0u64;
    let one = Rat::one();

    // The receiving map: Σ_j g_j ⊗ P_R^(τ_R) v_R(e_j), by row blocks.
    let receiving = diamond.receiver();
    let width_r = field.ring(receiving).width();
    let read_charts: Vec<[Chart; 2]> = back
        .reads
        .iter()
        .map(|(feature, gradient)| [integral(gradient), integral(feature)])
        .collect();
    let map_gradient = outer_rows(
        2 * alphabet,
        width_r,
        &read_charts
            .iter()
            .map(|[gradient, feature]| (&one, gradient, feature))
            .collect::<Vec<_>>(),
    );
    let samples = back
        .reads
        .iter()
        .map(|(feature, gradient)| Sample {
            weight: one.clone(),
            feature: feature.clone(),
            covector: negated(gradient),
        })
        .collect();
    if retained(Locus::ReceivingMap(receiving)) {
        linear.push(LinearStep {
            locus: LinearLocus::Receiving(receiving),
            samples,
        });
    }

    // The rings' element material and class covectors, the rings together.
    let parts = indexed(field.rings().len(), |g| {
        compose_ring(field, constitution, back, diamond, &retained, g)
    })?;
    let mut ring_pullbacks = Vec::with_capacity(parts.len());
    let mut classes_all: Vec<Vec<Rat>> = Vec::with_capacity(parts.len());
    let mut midpoint_energy: Vec<Rat> = Vec::with_capacity(parts.len());
    let mut element_covector: Vec<Rat> = Vec::with_capacity(parts.len());
    for part in parts {
        linear.extend(part.contrast);
        factors.extend(part.factors);
        ring_pullbacks.push(part.pullback);
        classes_all.push(part.classes);
        midpoint_energy.push(part.energy);
        element_covector.push(part.covector);
    }

    // The standing, through the declared lock chart: Δ = M q with the contrast map `M`, which is
    // symmetric, so ∂ℓ/∂q = Mᵀ g_σ = M g_σ ([`Field::contrast`]). A move of `q_g` moves the
    // contrast of `g` and of the other end of each contact at `g`: its chart's reach, each ring with
    // its element window's energy, and its covector scale the largest of their elements' adjoints
    // (`hnn::constitution`, "The factor families' certified step").
    let class_fields: Vec<&[Rat]> = classes_all.iter().map(Vec::as_slice).collect();
    let standings = indexed(field.rings().len(), |g| field.contrast(g, &class_fields))?;
    for (g, standing) in standings.into_iter().enumerate() {
        if retained(Locus::Standing(g)) {
            let mut rings = vec![g];
            for contact in field.contacts() {
                let (from, to) = contact.ends();
                for (end, other) in [(from, to), (to, from)] {
                    if end == g && !rings.contains(&other) {
                        rings.push(other);
                    }
                }
            }
            let covector = rings
                .iter()
                .map(|&r| element_covector[r].clone())
                .max()
                .unwrap_or_else(Rat::zero);
            factors.push(FactorStep {
                gradient: FactorGradient::Standing {
                    ring: g,
                    gradient: negated(&standing),
                    reach: rings
                        .iter()
                        .map(|&r| (r, midpoint_energy[r].clone()))
                        .collect(),
                },
                energy: midpoint_energy[g].clone(),
                covector,
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
        let turned_charts: Vec<Chart> = indexed(turned.len(), |c| Ok(integral(&turned[c])))?;
        let source = constitution
            .source_port(g)
            .ok_or(HnnError::MissingSourcePort { ring: g })?;
        // The passage (the request, continued by any placed section, in its one population,
        // `hnn::moment`) enters through `E_g` at the request's frame.
        let modulus = constitution.transport(g);
        let gradient = moment.encoder_covector(field, &current, g, opening, &modulus)?;
        let source_t = source.transpose()?;
        // The covector on the moment's counts at their weights (ruling B: the open reads
        // `M[c] w(c)`, so `∂/∂M[c] = w(c) Eᵀ h` with the weights held; at a transport of modulus
        // one `w = ν̂(n)` at every phase, an empty one included).
        let weights = if modulus.is_one() {
            vec![PopulationChart::of(field).value(moment.population(g)?); turned.len()]
        } else {
            moment.phase_weights(field, g, &modulus)?
        };
        let moment_covector = indexed(turned.len(), |c| {
            Ok(apply_rows(&source_t, &turned[c])?
                .into_iter()
                .map(|x| x * &weights[c])
                .collect())
        })?;
        // One sample per occupied phase: its feature the passage's normalized counts.
        let mut source_samples = Vec::new();
        for (c, h) in turned.iter().enumerate() {
            if moment.phase_counts(g, c)?.iter().all(|x| *x == 0) {
                continue;
            }
            let feature = moment.normalized_counts(field, g, c, &modulus)?;
            source_samples.push(Sample {
                weight: one.clone(),
                feature,
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
            // The whole normalized offset moment of each phase `(x, a, C_c[x, a] ν̂)` over its pair
            // population (`hnn::moment`: the open reads no window), read once; none at an empty
            // population.
            let tables = [moment.offset_table(field, g, offset)?];
            let mut nonzero: Vec<Vec<(usize, usize, Rat)>> = Vec::with_capacity(d);
            let mut energy = Rat::zero();
            for c in 0..d {
                let mut slots = Vec::new();
                for table in tables.iter().flatten() {
                    for (slot, &count) in table.phase(c, alphabet).iter().enumerate() {
                        if count == 0 {
                            continue;
                        }
                        let value = Rat::from_integer(BigInt::from(count)) * &table.weight;
                        energy += &value * &value;
                        slots.push((slot / alphabet, slot % alphabet, value));
                    }
                }
                nonzero.push(slots);
            }
            // Each rank reads only its own reads `a_ρ`, `b_ρ`, `e_ρ`: the ranks run together.
            let ranks = indexed(rank, |rho| {
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
                Ok((
                    combination(n, weights.iter().zip(&turned_charts)),
                    combination(
                        alphabet,
                        by_current.iter().map(|(weight, chart)| (weight, chart)),
                    ),
                    combination(
                        alphabet,
                        by_earlier.iter().map(|(weight, chart)| (weight, chart)),
                    ),
                ))
            })?;
            let mut outputs = Vec::with_capacity(rank);
            let mut current_reads = Vec::with_capacity(rank);
            let mut earlier_reads = Vec::with_capacity(rank);
            for (output, current_read, earlier_read) in ranks {
                outputs.push(output);
                current_reads.push(current_read);
                earlier_reads.push(earlier_read);
            }
            // The covector one phase's injection carries: the turned opening at each phase the
            // offset moment occupies.
            let covector = nonzero
                .iter()
                .zip(&turned)
                .filter(|(slots, _)| !slots.is_empty())
                .flat_map(|(_, h)| h.iter().map(Signed::abs))
                .max()
                .unwrap_or_else(Rat::zero);
            pair_steps.push(FactorStep {
                gradient: FactorGradient::PairPort {
                    ring: g,
                    offset,
                    outputs: outputs.iter().map(|x| negated(x)).collect(),
                    current: current_reads.iter().map(|x| negated(x)).collect(),
                    earlier: earlier_reads.iter().map(|x| negated(x)).collect(),
                },
                energy,
                covector,
            });
            pair_pullbacks.push((offset, [outputs, current_reads, earlier_reads]));
        }
        phases = phases.max(source_samples.len() as u64);
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

    // The loaded resonators: reverse their transient local state in reverse tick order (the word
    // returns each tick's transposed solve and operands), then pull the four scalar amplitudes onto
    // their immutable base forms. The exact inverse/material derivative and the executed chart's
    // adjoint residual remain separate readings in `WordReturn`.
    if back.resonators.len() != field.rings().len() {
        return Err(HnnError::Shape {
            what: "the loaded resonator pullbacks by ring",
            expected: field.rings().len(),
            found: back.resonators.len(),
        });
    }
    let mut resonator_pullbacks = Vec::new();
    for (g, ticks) in back.resonators.iter().enumerate() {
        let Some(material) = constitution.ring_resonator(g) else {
            if !ticks.is_empty() {
                return Err(HnnError::Resonator {
                    ring: g,
                    what: "the return has a resonator tick without a declared material",
                });
            }
            continue;
        };
        let (capacity, stiffness, dissipation, pump_strength) = material.gain_bases();
        let gains = material.gains();
        let mut loss_gradients = std::array::from_fn(|_| Rat::zero());
        let mut energies = std::array::from_fn(|_| Rat::zero());
        let mut reached = false;
        // The covector one tick carries at the resolvent's right-hand side, its solved `r̄`.
        let mut covector = Rat::zero();
        for tick in ticks {
            if !diamond.element_window(g, tick.tick) {
                continue;
            }
            reached = true;
            for value in &tick.solved {
                if value.abs() > covector {
                    covector = value.abs();
                }
            }
            let hω = scale(&(&h / integer(2)), &tick.rate);
            let midpoint = add(&tick.displacement, &hω);
            let w_minus_ω = sub(&tick.velocity, &tick.rate);
            let feature_c = scale(
                &(integer(4) * &gains[0]),
                &apply_rows(capacity, &w_minus_ω)?,
            );
            let feature_k = scale(
                &(integer(2) * &h * &gains[1]),
                &apply_rows(stiffness, &midpoint)?,
            );
            let feature_d = scale(
                &(integer(2) * &h * &gains[2]),
                &apply_rows(dissipation, &tick.rate)?,
            );
            let feature_p = match (material.base_pump(), pump_strength) {
                (Some(pump), Some(strength)) => scale(
                    &(integer(2) * &h * &gains[3] * strength),
                    &apply_rows(
                        &resonator_pump_base_form(pump, tick.phase, material.width())?,
                        &midpoint,
                    )?,
                ),
                _ => vec![Rat::zero(); material.width()],
            };
            loss_gradients[0] += dot(&tick.solved, &feature_c);
            loss_gradients[1] -= dot(&tick.solved, &feature_k);
            loss_gradients[2] -= dot(&tick.solved, &feature_d);
            loss_gradients[3] -= dot(&tick.solved, &feature_p);
            for (energy, feature) in energies
                .iter_mut()
                .zip([&feature_c, &feature_k, &feature_d, &feature_p])
            {
                *energy += dot(feature, feature);
            }
        }
        let pullback = ResonatorPullback {
            ring: g,
            gains: loss_gradients.clone(),
            energy: energies.clone(),
        };
        if retained(Locus::Resonator(g)) && reached {
            for family in 0..4 {
                factors.push(FactorStep {
                    gradient: FactorGradient::Resonator {
                        ring: g,
                        family,
                        gradient: -loss_gradients[family].clone(),
                    },
                    energy: energies[family].clone(),
                    covector: covector.clone(),
                });
            }
        }
        resonator_pullbacks.push(pullback);
    }

    // The contacts: their channel factors, conductance and pair geometry, the contacts together.
    let parts = indexed(field.contacts().len(), |a| {
        compose_contact(
            field,
            constitution,
            back,
            diamond,
            &retained,
            anchor,
            &h,
            a,
        )
    })?;
    let mut contact_pullbacks = Vec::with_capacity(parts.len());
    for (steps, pullback) in parts {
        factors.extend(steps);
        contact_pullbacks.push(pullback);
    }

    let reached: Vec<Locus> = crate::hnn::retention::loci(field)
        .into_iter()
        .filter(|locus| retained(*locus))
        .collect();
    let pullback = Pullback {
        rings: ring_pullbacks,
        contacts: contact_pullbacks,
        resonators: resonator_pullbacks,
        receiving: (receiving, matrix_of(map_gradient, width_r)?),
    };
    Ok(ComposedReturn {
        pullback,
        linear,
        factors,
        reached,
        phases,
    })
}

/// **One ring's part of the composition**: its contrast port's window (when retained), its
/// passive and slice factor steps (when retained), its pullback without the standing and the
/// source parts, its class covector and its midpoints' energy.
struct RingPart {
    contrast: Option<LinearStep>,
    factors: Vec<FactorStep>,
    /// The largest entry of an adjoint `u_t` in the element's window (its families' covector scale).
    covector: Rat,
    pullback: RingPullback,
    classes: Vec<Rat>,
    energy: Rat,
}

/// **Ring `g`'s part of the composition** (see [`compose`]): its ticks' vectors read once in the
/// integral chart, `K̄ = Σ_t u_t x̄_tᵀ`, the contrast port's `Σ_t u_t c_tᵀ`, and per slice the class
/// and the slice's gradients, the slices together.
fn compose_ring(
    field: &Field,
    constitution: &Constitution,
    back: &WordReturn,
    diamond: &Diamond,
    retained: &(impl Fn(Locus) -> bool + Sync),
    g: usize,
) -> Result<RingPart, HnnError> {
    use crate::ratio::linear::vector::{Chart, IntegralMatrix, integer_dot, integral, lcm};
    let one = Rat::one();
    let n = field.ring(g).width();
    let passive = constitution.passive_factor(g);
    let slices = constitution.slices(g);
    let ticks = &back.elements[g];
    // The sheet classes this word read.
    let sheets = sheet_classes(field, constitution, g)?;
    // Each tick's adjoint `u`, midpoint `x̄` and contrast `c`, read once in the integral chart.
    let charts: Vec<[Chart; 3]> = indexed(ticks.len(), |t| {
        let tick = &ticks[t];
        Ok([
            integral(&tick.adjoint),
            integral(&tick.midpoint),
            integral(&tick.contrast),
        ])
    })?;
    // K̄ = Σ_t u_t x̄_tᵀ and the contrast port's Σ_t u_t c_tᵀ.
    let element_gradient =
        IntegralMatrix::outer_sum(n, n, charts.iter().map(|[u, x, _]| (&one, u, x)));
    let contrast_gradient = outer_rows(
        n,
        n,
        &charts
            .iter()
            .map(|[u, _, c]| (&one, u, c))
            .collect::<Vec<_>>(),
    );
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
    // Each slice reads only its own pair `(s, v)` against the shared ticks: the slices run
    // together.
    let per_slice = indexed(slices.len(), |rho| {
        let (su, sv) = &slices[rho];
        let ((su, d_su), (sv, d_sv)) = (integral(su), integral(sv));
        let mut class = Rat::zero();
        let mut du = vec![BigInt::zero(); n];
        let mut dv = vec![BigInt::zero(); n];
        for ([u, x, _], (u_lift, x_lift)) in charts.iter().zip(&lifted) {
            let (u_su, x_sv, u_sv, x_su) = (
                integer_dot(&u.0, &su),
                integer_dot(&x.0, &sv),
                integer_dot(&u.0, &sv),
                integer_dot(&x.0, &su),
            );
            class += Rat::new(&u_su * &x_sv - &u_sv * &x_su, &u.1 * &x.1 * &d_su * &d_sv);
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
        Ok((
            class,
            (
                du.into_iter()
                    .map(|value| Rat::new(signed(value), &common * &d_sv))
                    .collect::<Vec<Rat>>(),
                dv.into_iter()
                    .map(|value| Rat::new(signed(value), &common * &d_su))
                    .collect::<Vec<Rat>>(),
            ),
        ))
    })?;
    let mut classes = vec![Rat::zero(); n];
    let mut slice_gradient = Vec::with_capacity(slices.len());
    for (rho, (class, gradient)) in per_slice.into_iter().enumerate() {
        classes[rho] += class;
        slice_gradient.push(gradient);
    }
    let mut energy = Rat::zero();
    let mut contrast_samples = Vec::new();
    // The covector one tick carries at the element's drive, its adjoint `u_t`: the element's
    // families' covector scale, as the contrast port's samples carry it.
    let mut covector = Rat::zero();
    for tick in ticks {
        if diamond.element_window(g, tick.tick) {
            energy += dot(&tick.midpoint, &tick.midpoint);
            for value in &tick.adjoint {
                if value.abs() > covector {
                    covector = value.abs();
                }
            }
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
    let (mut contrast, mut factors) = (None, Vec::new());
    if retained(Locus::Element(g)) && window {
        contrast = Some(LinearStep {
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
            covector: covector.clone(),
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
            covector: covector.clone(),
        });
    }
    Ok(RingPart {
        contrast,
        factors,
        covector,
        pullback: RingPullback {
            ring: g,
            passive: matrix_of(passive_gradient, passive.columns())?,
            contrast: matrix_of(contrast_gradient, n)?,
            slices: slice_gradient,
            classes: classes.clone(),
            standing: Vec::new(),
            source: None,
            pair: Vec::new(),
            moment: None,
        },
        classes,
        energy,
    })
}

/// **Contact `a`'s part of the composition** (see [`compose`]): its ticks' vectors read once in the
/// integral chart, the three forms' pulls `C̄ = Σ 2 r̄ (w − ω)ᵀ`, `K̄ = −h Σ r̄ (u + ½hω)ᵀ`,
/// `D̄ = −h Σ r̄ ωᵀ` (the three together), its factor steps (when retained) and its pullback.
#[allow(clippy::too_many_arguments)]
fn compose_contact(
    field: &Field,
    constitution: &Constitution,
    back: &WordReturn,
    diamond: &Diamond,
    retained: &(impl Fn(Locus) -> bool + Sync),
    anchor: &[BigInt],
    h: &Rat,
    a: usize,
) -> Result<(Vec<FactorStep>, ContactPullback), HnnError> {
    use crate::ratio::linear::vector::{Chart, IntegralMatrix, integral};
    let contact = field.contact(a);
    let k = contact.width();
    let (two, minus_h, half_h) = (integer(2), -h.clone(), h / integer(2));
    // Each tick's r̄, slip w − ω, strain u + ½hω and ω, read once in the integral chart, the ticks
    // together; the window's energies are summed afterwards in tick order.
    let ticks = &back.transits[a];
    let read = indexed(ticks.len(), |t| {
        let tick = &ticks[t];
        let (r, u, w, omega) = (&tick.solved, &tick.displacement, &tick.rate, &tick.midpoint);
        let slip: Vec<Rat> = w.iter().zip(omega).map(|(w, o)| w - o).collect();
        let strain = add(u, &scale(&half_h, omega));
        // The window's energies, and the covector the tick carries at the transit's right-hand
        // side, its solved `r̄` (the channel's families' covector scale).
        let energies = diamond.channel_window(field, a, tick.tick).then(|| {
            (
                [dot(&slip, &slip), dot(&strain, &strain), dot(omega, omega)],
                r.iter().map(Signed::abs).max().unwrap_or_else(Rat::zero),
            )
        });
        Ok((
            [
                integral(r),
                integral(&slip),
                integral(&strain),
                integral(omega),
            ],
            energies,
        ))
    })?;
    let mut energies = [Rat::zero(), Rat::zero(), Rat::zero()];
    let mut covector = Rat::zero();
    let mut window = false;
    let mut charts: Vec<[Chart; 4]> = Vec::with_capacity(read.len());
    for (chart, terms) in read {
        if let Some((terms, widest)) = terms {
            window = true;
            for (energy, term) in energies.iter_mut().zip(terms) {
                *energy += term;
            }
            if widest > covector {
                covector = widest;
            }
        }
        charts.push(chart);
    }
    // C̄ = Σ 2 r̄ (w − ω)ᵀ,  K̄ = −h Σ r̄ (u + ½hω)ᵀ,  D̄ = −h Σ r̄ ωᵀ, each pulled onto its factor.
    let forms = [
        constitution.contact_storage(a),
        constitution.contact_stiffness(a),
        constitution.contact_dissipation(a),
    ];
    let pulled = indexed(3, |index| {
        let weight = if index == 0 { &two } else { &minus_h };
        Ok(IntegralMatrix::outer_sum(
            k,
            k,
            charts
                .iter()
                .map(|chart| (weight, &chart[0], &chart[index + 1])),
        )
        .symmetric_times(forms[index], false)?)
    })?;
    let mut steps = Vec::new();
    if retained(Locus::Channel(a)) && window {
        let descent = |index: usize| {
            matrix_of(
                pulled[index].iter().map(|row| negated(row)).collect(),
                forms[index].columns(),
            )
        };
        steps.push(FactorStep {
            gradient: FactorGradient::Storage {
                contact: a,
                gradient: descent(0)?,
            },
            energy: energies[0].clone(),
            covector: covector.clone(),
        });
        steps.push(FactorStep {
            gradient: FactorGradient::Stiffness {
                contact: a,
                gradient: descent(1)?,
            },
            energy: energies[1].clone(),
            covector: covector.clone(),
        });
        steps.push(FactorStep {
            gradient: FactorGradient::Dissipation {
                contact: a,
                gradient: descent(2)?,
            },
            energy: energies[2].clone(),
            covector,
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
    let [storage, stiffness, dissipation]: [Vec<Vec<Rat>>; 3] =
        pulled.try_into().expect("three forms were pulled");
    Ok((
        steps,
        ContactPullback {
            contact: a,
            feature,
            conductance: back.conductance[a].clone(),
            storage: matrix_of(storage, forms[0].columns())?,
            stiffness: matrix_of(stiffness, forms[1].columns())?,
            dissipation: matrix_of(dissipation, forms[2].columns())?,
            key,
        },
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

/// [definition] **A cut**: the exterior stream's codes in order, and its pinned held-out positions.
/// Every cell is compared and then deposited (prequential scoring): "held out" means only that no design
/// choice (depth, precision, step, grain) was made on those cells, and that no crib reads them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cut {
    pub cells: Vec<usize>,
    pub held_out: Vec<Range<usize>>,
}

impl Cut {
    /// Whether the cell at `position` is held out.
    pub fn held_out(&self, position: usize) -> bool {
        self.held_out.iter().any(|range| range.contains(&position))
    }

    /// **The crib that closed an aeon at cell `at`**: at most `window` cells before `at`, none
    /// before the aeon's opening `start`, and none at or before a held-out cell, so the crib holds
    /// only cells already read and never a held-out one (review D1).
    pub fn closing_crib(&self, start: usize, at: usize, window: usize) -> Range<usize> {
        let mut from = at.saturating_sub(window).max(start);
        for range in &self.held_out {
            if range.start < at && range.end > from {
                from = from.max(range.end.min(at));
            }
        }
        from..at
    }
}

/// [definition] **Bits on a population of targets**: the model's code length on its scored face,
/// the receiver's population over the tree's face and the combined face (ruling A, THE_REBUILD U1);
/// the landmark tree's executed face alone (`tree`, the landmark tree: the receiving parametron's
/// tree at each cell's causal address and at the standing after every earlier cell, with no wave:
/// the face `q_T` the population weighs); the same tree's face at the grain (`tree_grain`: its
/// grain logits alone, the face the combined read opens at when the wave reads zero); the combined
/// face alone (the tree's grain logits plus the wave, whose covector the wave learns from). So
/// `combined − tree` (`L_C − L_T`) is the wave's contribution against the tree's executed face, the
/// population's log-odds of the tree over the combined face (it includes the grain's rounding,
/// `tree_grain − tree`, which the combined face inherits), and `model − tree` (`L_model − L_T`) is
/// what the population keeps of it: over the whole passage (both populations) `L_model` lies
/// between `min(L_T, L_C)` and one bit above it (Lean
/// `Compression/Landmark/Context/Tree.sequential_mixture_bounds`, the two-family population at
/// ½/½); and the online
/// baselines' (uniform;
/// order-0 and order-1 with the Krichevsky–Trofimov prior; PPM of order
/// [`PPM_ORDER`](crate::compression::landmark::context::baseline::PPM_ORDER) with escape
/// rule C), each an enclosure, over `cells` targets. xz and zstd, with their description cost, are
/// exterior codecs: the crate runs no process, so they are owed to the application, computed there
/// on the same cut and joined to this report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bits {
    pub model: ExactInterval,
    pub tree: ExactInterval,
    pub tree_grain: ExactInterval,
    pub combined: ExactInterval,
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
            tree: zero.clone(),
            tree_grain: zero.clone(),
            combined: zero.clone(),
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
/// what the deposit that reached it released (its residuals' exact bits) and stepped (the entries
/// whose lattice coordinate moved), and each contact's site reading at the commit (campaign 2's
/// contact-kind census, `hnn::contact::site_readings`, certified from the factors in one prime
/// chart and read exactly otherwise: the kinds a register refreshed after the next ingest reads),
/// the deposit's certified steps (each stepped family at its locus with its exponent `k`, the step `2^k`)
/// and its certified storage growth `ε_k`. The mount's point releases and steps nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurvePoint {
    pub commit: u64,
    pub bits: CarrierBits,
    pub released_bits: u64,
    pub stepped: u64,
    pub contacts: Vec<SiteReading>,
    pub steps: Vec<(Locus, Family, i64)>,
    /// The deposit's rounding refusals ([`DepositReading::vanished`]): the certified families that
    /// moved no lattice coordinate.
    pub vanished: Vec<(Locus, Family)>,
    pub storage_growth: Rat,
}

/// [definition] **The exposure's readout** (design (f)): bits on the training and held-out targets
/// against the baselines, the key reports, each aeon boundary (its length, collapse, readings,
/// first law and the face against the literal), the constitution's bits per deposit by carrier with
/// each deposit's released and stepped entries, the receiving windows whose source-to-receiver path
/// was open at their cut against all windows read (the refine receipt's located cause, review C2),
/// the peak bits of the change inside any word, the budget stop, the deadline, the description bits
/// (`Field::describe` plus the constitution's self-delimiting campaign-2 material declaration; the
/// field code includes its step rule, budget and pending capacity), the final resonator gains,
/// the located keys' bits (`⌈log₂ d_g⌉` per published key: the model pays for what
/// learning located) and `Kt = |describe| + key bits + L_target|model + ⌈log₂ work⌉` against the
/// literal over the cells read, the work counted and the state against the source. The run is
/// complete when it read the whole cut with no budget stop. Beside the readout, exterior, the host's
/// wall time by phase ([`WallTimes`]): it enters no law and no description, and it is the one field
/// two runs of one cut do not share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exposure {
    pub training: Bits,
    pub held_out: Bits,
    pub keys: Vec<KeyReport>,
    pub aeons: Vec<AeonBoundary>,
    /// The receiving face's course by aeon (ruling A): each aeon's model, tree and combined code
    /// lengths and the population's log-odds at its boundary, the run's last, open aeon at its end.
    pub course: Vec<AeonCourse>,
    pub constitution_curve: Vec<CurvePoint>,
    /// The receiving windows read: the closed epochs of the cut's cell clock at the receiver's
    /// section that the run compared (`hnn::receiving::ReceivingPhases::windows`).
    pub windows: u64,
    pub open_windows: u64,
    pub peak_word_bits: u64,
    pub stop: Option<(BudgetStop, u64)>,
    /// The cell at which the run stopped at its deadline ([`Reference::with_deadline`]), if it did.
    pub deadline: Option<u64>,
    pub complete: bool,
    pub description_bits: u64,
    /// Final scalar gains of declared resonators, in ring order (a constitutive reading, not an
    /// event archive).
    pub resonator_gains: Vec<(usize, [Rat; 4])>,
    /// The carried remainders of those gains, in ring order: what reached each family below its
    /// lattice's unit.
    pub resonator_remainders: Vec<(usize, [Rat; 4])>,
    pub key_bits: u64,
    pub kt: ExactInterval,
    pub literal_bits: u64,
    pub work: ExactWork,
    pub state: StateReport,
    /// [definition; agent-inferred, U5] The program's own counters, disclosed as such: the
    /// compares and the deposits the loop made. They are not clocks of the Holarchy; the
    /// constitution's clock at a locus is its deposit clock (`Constitution::clock`), an epoch count.
    pub compares: u64,
    pub deposits: u64,
    /// The executed word's readout (the lattice word).
    pub word: WordReport,
    /// The receiver's population at the end of the run (ruling A, THE_REBUILD U1).
    pub population: Option<PopulationReport>,
    /// The host's wall time by phase (exterior).
    pub wall: WallTimes,
    /// The exposure's own readings' wall time (exterior): the word balances and the census.
    pub readout: ReadoutWall,
}

/// [definition] **The receiver's population at the end of a run** (ruling A, THE_REBUILD U1,
/// `receiver::population::PortPopulation` over the tree `T` and the combined face `C` at ½/½): its
/// code `−log₂(½ L_T + ½ L_C)` read once from the families' likelihoods (the telescope), each
/// family's code alone, their log-odds `log₂(L_T/L_C) = L_C − L_T`, the cells received and its
/// exact bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationReport {
    pub code: ExactInterval,
    pub tree: Option<ExactInterval>,
    pub combined: Option<ExactInterval>,
    pub odds: Option<ExactInterval>,
    pub cells: u64,
    pub bits: u64,
}

impl PopulationReport {
    /// **The receiver's population's readings** (the struct's header).
    pub fn of(population: &PortPopulation) -> Result<Self, HnnError> {
        let refusal = crate::hnn::receiving::population_refusal;
        let tree = population
            .family_code(crate::hnn::receiving::TREE)
            .map_err(refusal)?;
        let combined = population
            .family_code(crate::hnn::receiving::COMBINED)
            .map_err(refusal)?;
        Ok(Self {
            code: population.code().map_err(refusal)?,
            odds: log_odds(tree.as_ref(), combined.as_ref())?,
            tree,
            combined,
            cells: population.cells(),
            bits: population.bits(),
        })
    }
}

/// **The log-odds of the tree over the combined face** `log₂(L_T/L_C) = L_C − L_T`, enclosed from
/// the families' codes; none while either is unbounded (a dead or undecided family).
fn log_odds(
    tree: Option<&ExactInterval>,
    combined: Option<&ExactInterval>,
) -> Result<Option<ExactInterval>, HnnError> {
    match (tree, combined) {
        (Some(tree), Some(combined)) => Ok(Some(ExactInterval::new(
            &combined.lower - &tree.upper,
            &combined.upper - &tree.lower,
        )?)),
        _ => Ok(None),
    }
}

/// [definition] **One aeon's leg of the receiving face's course** (ruling A): the cell at which it
/// closed (the joint clock's carry-out, or the run's end), the cells compared since the previous
/// boundary (every phase of the windows compared in it, a window counted in the aeon its compare
/// ran in), their code lengths under the model (the receiver's population), the tree's executed
/// face alone and the combined face alone, and the population's log-odds `log₂(L_T/L_C)` at the
/// boundary (`L_C − L_T` over every cell so far): whether the combined face stops losing as its
/// features stop growing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeonCourse {
    pub cell: u64,
    pub cells: u64,
    pub model: ExactInterval,
    pub tree: ExactInterval,
    pub combined: ExactInterval,
    pub odds: Option<ExactInterval>,
}

/// The sums of the aeon in progress.
struct Leg {
    cells: u64,
    model: ExactInterval,
    tree: ExactInterval,
    combined: ExactInterval,
}

impl Leg {
    fn open() -> Self {
        let zero = ExactInterval::point(Rat::zero());
        Self {
            cells: 0,
            model: zero.clone(),
            tree: zero.clone(),
            combined: zero,
        }
    }

    fn add(
        &mut self,
        model: &ExactInterval,
        tree: &ExactInterval,
        combined: &ExactInterval,
    ) -> Result<(), HnnError> {
        self.cells += 1;
        self.model = interval_sum(&self.model, model)?;
        self.tree = interval_sum(&self.tree, tree)?;
        self.combined = interval_sum(&self.combined, combined)?;
        Ok(())
    }

    /// Close the leg at a cell, with the population's log-odds read off the published
    /// constitution, and open the next.
    fn close(
        &mut self,
        cell: u64,
        constitution: &Constitution,
        ring: usize,
    ) -> Result<AeonCourse, HnnError> {
        let leg = std::mem::replace(self, Self::open());
        Ok(AeonCourse {
            cell,
            cells: leg.cells,
            model: leg.model,
            tree: leg.tree,
            combined: leg.combined,
            odds: match constitution.population(ring) {
                Some(population) => PopulationReport::of(population)?.odds,
                None => None,
            },
        })
    }
}

/// [definition] **The executed word's readout over an exposure** (the lattice word): the charts' tally
/// (reads, seeds, rounded Newton–Schulz steps, the largest certificate against the target), the
/// carried remainders the refines' words released at their ends (`forward`) and the compares'
/// returns released at their opens (`adjoint`), joined over the run; over every refine's full
/// ticks, how many balances were read, whether every one closed up to its residual within its
/// certified bound, and the largest residual in magnitude with the bound at that tick; and every
/// word's whole balance carried across its commit ([`WordBalances`], campaign 2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordReport {
    pub charts: ChartTally,
    pub forward: Remainders,
    pub adjoint: Remainders,
    pub balances: u64,
    pub closed: bool,
    pub largest_residual: Rat,
    pub residual_bound: Rat,
    pub words: WordBalances,
}

/// [definition] **Every word's balance over an exposure** (campaign 2, `hnn::word::WordBalance`,
/// formed from each refine's release on every realization of the port and carried across the commit
/// that follows it): the balances formed and carried across a commit, whether every one closed
/// (the combined identity with the deposition work and the interconnection's defect, and the
/// executed residual, the resonators' chart and split included, within its bound), the largest
/// executed residual in magnitude with its bound, the deposition work summed over the commits with
/// the largest in magnitude, and the interconnection's defect summed (the resonator's port work
/// plus the field's signed port term: zero by construction when loaded, since the field's term is
/// formed as the negative of the resonator's work, and the resonator's port work when unloaded;
/// the loaded evidence is the bounded executed residual).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WordBalances {
    pub formed: u64,
    pub committed: u64,
    pub closed: bool,
    pub largest_residual: Rat,
    pub residual_bound: Rat,
    pub deposition: Rat,
    pub largest_deposition: Rat,
    pub interconnection: Rat,
}

impl WordBalances {
    fn record(&mut self, balance: &WordBalance) {
        self.closed &= balance.closes();
        self.formed += 1;
        let residual = balance.residual().abs();
        if self.formed == 1 || residual > self.largest_residual {
            self.largest_residual = residual;
            self.residual_bound = balance.bound.clone();
        }
        if let Some(commit) = &balance.commit {
            self.committed += 1;
            self.deposition += &commit.deposition;
            if commit.deposition.abs() > self.largest_deposition {
                self.largest_deposition = commit.deposition.abs();
            }
        }
        self.interconnection += &balance.interconnection;
    }
}

/// [definition] **The exposure's own readings' wall time** (exterior; no law reads it): the word
/// balances' power forms and commits, and the contact-kind census at every commit (the contact
/// site readings of the constitution curve).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReadoutWall {
    pub balance: Duration,
    pub census: Duration,
}

/// **Code one cell in every baseline into `bits`, then count it** (the exposure's population sums).
fn code_baselines(baselines: &mut Baselines, bits: &mut Bits, code: usize) -> Result<(), HnnError> {
    let codes = baselines.code_cell(code)?;
    bits.uniform = interval_sum(&bits.uniform, &codes.uniform)?;
    bits.order_zero = interval_sum(&bits.order_zero, &codes.order_zero)?;
    bits.order_one = interval_sum(&bits.order_one, &codes.order_one)?;
    bits.ppm = interval_sum(&bits.ppm, &codes.ppm)?;
    bits.cells += 1;
    Ok(())
}

impl Reference {
    /// **Run campaign 1's exposure protocol on a cut** and read its measurement (module header):
    /// [`expose`] on this reference, at its declared budget, pending capacity and deadline.
    /// The admitted family is the field's declared receivers throughout. Refused unless the cut is
    /// exactly the field's declared population, which `Field::declare` checked against `n*`. Under a
    /// deadline ([`Reference::with_deadline`]) the reading stops after that many receiving windows.
    pub fn expose(&self, field: &Field, cut: &Cut) -> Result<Exposure, HnnError> {
        expose(
            self,
            &Declared {
                budget: self.budget,
                pending_capacity: self.pending_capacity,
                deadline: self.deadline,
            },
            field,
            cut,
        )
    }

    /// Run the same prequential protocol from a caller-declared initial constitution.
    pub fn expose_with(
        &self,
        field: &Field,
        cut: &Cut,
        constitution: Constitution,
    ) -> Result<Exposure, HnnError> {
        let current = Current::at_rest(field);
        let resident = self.mount_with(field, &current, constitution)?;
        expose_from(
            self,
            &Declared {
                budget: self.budget,
                pending_capacity: self.pending_capacity,
                deadline: self.deadline,
            },
            field,
            cut,
            resident,
        )
    }
}

/// [measured-diagnostic; agent-inferred, October 2; the
/// [contact loop record](../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)
/// §7] **One window's contact ablation** ([`contact_ablation`]): the contact families the window's
/// own return moved when its deposit is restricted to the contacts, the deposition work of that
/// contacts-only commit on the window's end change (`½⟨x, ΔΘ x⟩`, `PowerForm::deposition_work`),
/// and the next window's code read at the predecessor and at the contacts-only successor, each
/// after the window's own ingest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactAblation {
    pub position: usize,
    /// The aeon the window lies in (0 the first).
    pub aeon: usize,
    pub moved: Vec<(Locus, Family)>,
    pub vanished: Vec<(Locus, Family)>,
    pub work: Rat,
    pub held: ExactInterval,
    pub contacts: ExactInterval,
    /// Whether the next window's word (the exposure's consumer, a fresh word at the next cut) ends
    /// with different contact states, reads different exact logits, and different grain faces, at
    /// the contacts-only successor.
    pub states_differ: bool,
    pub logits_differ: bool,
    pub faces_differ: bool,
    /// The continuing consumer (Astra's check): the window's own retained end change continued at
    /// the predecessor's and at the successor's operands with nothing injected, on the clock after
    /// the window's junction steps, read through the receiving phases: whether its anchors, its
    /// exact logits and its grain faces differ.
    pub continued_anchors_differ: bool,
    pub continued_logits_differ: bool,
    pub continued_faces_differ: bool,
    /// Whether the next window's grain cells differ above the fibre (some class's carry or phase
    /// class, what the code reads), fresh and continued; a face can differ in its fibres alone.
    pub cells_differ: bool,
    pub continued_cells_differ: bool,
    /// The largest change of the next window's exponents `v = carry + phase/L + fibre` (bits of
    /// log-mass, before normalization) over its phases and classes, fresh and continued: the
    /// contacts' change in the receiver's own units.
    pub exponent_shift: Rat,
    pub continued_exponent_shift: Rat,
    /// The contacts-only commit's largest relative factor change: over the contacts and their three
    /// factors, the largest entry change over that factor's largest entry.
    pub factor_change: Rat,
    /// The contacts-only commit's certified channel families, how many of them vanished below
    /// the lattice, and the sum of their certified decreases `a` (the size of the return that
    /// reached the contacts, `a = |G|²/h′`).
    pub contact_families: usize,
    pub contact_vanished: usize,
    pub contact_alignment: Rat,
    /// The continued consumer's largest relative anchor change (largest entry change over the
    /// largest anchor entry), and its exponent spread: the largest `|v_c − v_d|` within a phase.
    pub anchor_change: Rat,
    pub exponent_spread: Rat,
}

/// [measured-diagnostic; agent-inferred, October 2; the contact loop record §13] **The contacts'
/// cumulative change at an aeon's close**: at the first window after each aeon boundary, that
/// window read at the published constitution and at the same constitution with every contact's
/// factors returned to the opening's, from the same resident state: the largest change of its
/// exponents, the receiver's exponent span there, and both codes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CumulativeContacts {
    pub aeon: usize,
    pub position: usize,
    pub exponent_shift: Rat,
    pub spread: Rat,
    pub held: ExactInterval,
    pub reverted: ExactInterval,
    /// Over the following windows with both constitutions frozen (no deposit), up to the next
    /// carry-out or [`AblationOptions::information`] windows: the readings compared, and `Σ Var_p(δ)` over them in
    /// bits² (`δ_c = v′_c − v_c` between the opening-contacts and the learned readings, `p` the
    /// learned face's masses at their enclosures' midpoints). The information the receiver gains
    /// about the contacts is `(ln 2/2) Σ Var_p(δ)` to second order (the record's §11, step 2).
    pub readings: usize,
    pub variance: Rat,
    /// Over the same frozen windows, the code with the opening's contacts less the code with the
    /// learned contacts, summed (enclosed), and the windows where it is strictly positive, strictly
    /// negative or undecided: the first-order difference on the actual targets.
    pub code_difference: ExactInterval,
    pub better: usize,
    pub worse: usize,
    pub undecided: usize,
    /// The receiving map `R` at this close: its largest entry, and its largest entry change since
    /// the previous close (the opening for the first) over that largest entry.
    pub receiving_largest: Rat,
    pub receiving_change: Rat,
}

/// [measured-diagnostic] **What [`contact_ablation`] reads beside its windows**: the frozen windows
/// of the information read at each close (`0` skips it) and whether each deposit's realized descent
/// is read (two more reads a window).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AblationOptions {
    pub information: usize,
    pub descent: bool,
}


/// [measured-diagnostic; agent-inferred, October 2; the contact loop record §15] **One deposit's
/// realized descent, split** (the Lean thread's condition, PR #151): the window read against its own
/// targets at the predecessor and at the successor. At each phase, with `δ_c` the change of class
/// `c`'s exponent and `Δ_c = δ_c − δ_t` its change relative to the target `t`, and `p̃` the
/// predecessor face's odometer masses: `A⁺ = Σ_(c≠t) p̃_c max(−Δ_c, 0)` (the part favouring the
/// target), `A⁻ = Σ_(c≠t) p̃_c max(Δ_c, 0)` (the part lifting other classes above it), summed over
/// the phases; and both codes. The realized secant, not the tangent the certificate reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositDescent {
    pub aeon: usize,
    pub a_plus: Rat,
    pub a_minus: Rat,
    pub before: ExactInterval,
    pub after: ExactInterval,
}

/// [measured-diagnostic; the contact loop record §15] **The run of [`contact_ablation`]**: its
/// windows, its aeon closes, `R`'s steps, each deposit's realized descent, and for every contact
/// factor entry the residuals its deposits released below the lattice: their sum, the sum of their
/// magnitudes, and their count (coherent when the sum's magnitude approaches the magnitudes' sum).
#[derive(Clone, Debug, Default)]
pub struct AblationRun {
    pub windows: Vec<ContactAblation>,
    pub cumulative: Vec<CumulativeContacts>,
    pub receiver: Vec<ReceiverStep>,
    pub descents: Vec<DepositDescent>,
    pub released: BTreeMap<(Locus, Carrier, usize), Released>,
}

/// One contact factor entry's released residuals over a run: their sum `S`, the sum of their
/// magnitudes, the sum of their squares `Q` and their count. The coherence statistic is
/// `Z = S/√Q` (the Lean thread's test: coherent when `|Z| > √(2 ln(2/α))`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Released {
    pub sum: Rat,
    pub magnitude: Rat,
    pub squares: Rat,
    pub count: usize,
}

/// [measured-diagnostic] **One deposit's receiving-map step** in [`contact_ablation`]: its aeon, the
/// certified decrease `a` of `R`'s step, its step `η`, and whether it moved a lattice coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverStep {
    pub aeon: usize,
    pub alignment: Rat,
    pub step: Rat,
    pub moved: bool,
}

/// [measured-diagnostic] **The contact loop on a cut** (Astra's check, on the host reference): the
/// exposure's own order over the first `windows` receiving windows (refine, compare, deposit, then
/// the window's ingest). At each window whose successor window exists, before the full deposit, the
/// compare's deposit is restricted to its contact families and deposited alone on the predecessor;
/// the same later drive (the next window, read against its own cells) is then read at the
/// predecessor and at that contacts-only successor, each after the window's ingest
/// ([`ContactAblation`]). The full deposit then proceeds as in the exposure. At an aeon's
/// carry-out the aeon is closed (no keys are located: the exposure's crib step is omitted), and the
/// next window reads the contacts' cumulative change ([`CumulativeContacts`]). Stops at the
/// deadline or at a budget refusal.
pub fn contact_ablation(
    reference: &Reference,
    field: &Field,
    cells: &[usize],
    windows: usize,
    options: AblationOptions,
    on_boundary: &mut dyn FnMut(&CumulativeContacts, &[ContactAblation], &[ReceiverStep]),
) -> Result<AblationRun, HnnError> {
    let mut resident = reference.mount(field, &Current::at_rest(field))?;
    let opening = resident.constitution().clone();
    let receiving_ring = resident
        .admitted()
        .first()
        .map(|p| p.ring())
        .ok_or(HnnError::Shape { what: "a declared receiver", expected: 1, found: 0 })?;
    let mut last_receiving = opening.receiving_map(receiving_ring).cloned();
    let family = resident.admitted().to_vec();
    let mut aeon = 0usize;
    let mut cumulative = Vec::new();
    let mut receiver = Vec::new();
    let mut descents = Vec::new();
    let mut released: BTreeMap<(Locus, Carrier, usize), Released> = BTreeMap::new();
    let mut boundary = false;
    let phases = resident
        .admitted()
        .first()
        .cloned()
        .ok_or(HnnError::Shape { what: "a declared receiver", expected: 1, found: 0 })?;
    let aperture = phases.aperture();
    let spans: Vec<Range<usize>> = phases.windows(cells.len())?.into_iter().collect();
    let (moment, _) = reference.ingest(&mut resident, None, &[])?;
    let feed = |reference: &Reference, resident: &mut Resident, window: &[usize]| -> Result<bool, HnnError> {
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference.ingest(resident, Some(&moment), &one_hot(&window[fed..]))?;
            let ingested = ingested.forward.into_present().expect("ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                return Ok(false);
            }
        }
        Ok(true)
    };
    type Read = (ExactInterval, Vec<[Vec<Rat>; 2]>, Option<Faces>);
    let read = |reference: &Reference, resident: &mut Resident, window: &[usize]| -> Result<Read, HnnError> {
        let (pending, refined) = reference.refine(resident, &moment, &phases)?;
        let states = match &refined.receipt.detail {
            ReceiptDetail::Refine { word, .. } => word.change.states.clone(),
            _ => Vec::new(),
        };
        let faces = refined.forward.into_present();
        let (_, compared) = reference.compare(resident, pending, &one_hot(window))?;
        let holon = compared.forward.into_present().expect("a compare returns its ratio");
        let mut total = ExactInterval::point(Rat::zero());
        for phase in holon.phases() {
            total = interval_sum(&total, &phase.code_length)?;
        }
        Ok((total, states, faces))
    };
    // Each face's grain cells above the fibre: (carry, phase class) per class.
    let grained = |faces: Option<&Faces>| -> Option<Vec<Vec<(BigInt, u64)>>> {
        faces.map(|f| {
            f.faces
                .iter()
                .map(|face| face.cells().iter().map(|c| (c.carry.clone(), c.phase)).collect())
                .collect()
        })
    };
    // The largest exponent change between two windows' faces, in bits.
    let shift = |a: Option<&Faces>, b: Option<&Faces>| -> Rat {
        let (Some(a), Some(b)) = (a, b) else { return Rat::zero() };
        let value = |c: &crate::receiver::face::GrainCell, grain: u64| {
            Rat::from_integer(c.carry.clone()) + Rat::new(BigInt::from(c.phase), BigInt::from(grain)) + &c.fibre
        };
        a.faces
            .iter()
            .zip(&b.faces)
            .flat_map(|(x, y)| {
                x.cells().iter().zip(y.cells()).map(move |(p, q)| {
                    (value(p, x.grain()) - value(q, y.grain())).abs()
                })
            })
            .max()
            .unwrap_or_else(Rat::zero)
    };
    let factor_change = |a: &Constitution, b: &Constitution| -> Rat {
        let largest = |m: &crate::ratio::linear::ExactRatMatrix| {
            m.entries().iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero)
        };
        let mut most = Rat::zero();
        for c in 0..field.contacts().len() {
            for (x, y) in [
                (a.contact_storage(c), b.contact_storage(c)),
                (a.contact_stiffness(c), b.contact_stiffness(c)),
                (a.contact_dissipation(c), b.contact_dissipation(c)),
            ] {
                let scale = largest(x);
                if scale.is_positive() {
                    let moved = x
                        .entries()
                        .iter()
                        .zip(y.entries())
                        .map(|(p, q)| (p - q).abs())
                        .max()
                        .unwrap_or_else(Rat::zero);
                    most = most.max(moved / scale);
                }
            }
        }
        most
    };
    let mut out = Vec::new();
    for (k, span) in spans.iter().enumerate().take(windows) {
        let window = &cells[span.clone()];
        if window.len() != aperture {
            break;
        }
        let next = spans.get(k + 1).map(|s| &cells[s.clone()]).filter(|w| w.len() == aperture);
        if std::mem::take(&mut boundary) {
            let mut reverted = resident.constitution().clone();
            for c in 0..field.contacts().len() {
                reverted = reverted.with_channel(
                    c,
                    opening.contact_storage(c).clone(),
                    opening.contact_stiffness(c).clone(),
                    opening.contact_dissipation(c).clone(),
                )?;
            }
            let mut held = resident.clone();
            let mut back = resident.clone();
            back.constitution = reverted;
            back.forget_kept_reads();
            let (held_code, _, held_faces) = read(reference, &mut held, window)?;
            let (back_code, _, back_faces) = read(reference, &mut back, window)?;
            let spread = held_faces
                .as_ref()
                .map(|f| {
                    f.faces
                        .iter()
                        .map(|face| {
                            let v: Vec<Rat> = face
                                .cells()
                                .iter()
                                .map(|c| {
                                    Rat::from_integer(c.carry.clone())
                                        + Rat::new(BigInt::from(c.phase), BigInt::from(face.grain()))
                                        + &c.fibre
                                })
                                .collect();
                            v.iter().max().cloned().unwrap_or_else(Rat::zero)
                                - v.iter().min().cloned().unwrap_or_else(Rat::zero)
                        })
                        .max()
                        .unwrap_or_else(Rat::zero)
                })
                .unwrap_or_else(Rat::zero);
            // The information over the following windows, both constitutions frozen.
            let (mut readings, mut variance) = (0usize, Rat::zero());
            let mut code_difference = interval_difference(&back_code, &held_code)?;
            let tally = |d: &ExactInterval, counts: &mut (usize, usize, usize)| {
                if d.lower.is_positive() {
                    counts.0 += 1;
                } else if d.upper.is_negative() {
                    counts.1 += 1;
                } else {
                    counts.2 += 1;
                }
            };
            let mut counts = (0usize, 0usize, 0usize);
            tally(&code_difference.clone(), &mut counts);
            let mut faces_pair = (held_faces.clone(), back_faces.clone());
            let mut j = k;
            while options.information > 0 {
                if let (Some(a), Some(b)) = (&faces_pair.0, &faces_pair.1) {
                    for (fa, fb) in a.faces.iter().zip(&b.faces) {
                        let value = |c: &crate::receiver::face::GrainCell, grain: u64| {
                            Rat::from_integer(c.carry.clone())
                                + Rat::new(BigInt::from(c.phase), BigInt::from(grain))
                                + &c.fibre
                        };
                        let delta: Vec<Rat> = fa
                            .cells()
                            .iter()
                            .zip(fb.cells())
                            .map(|(p, q)| value(q, fb.grain()) - value(p, fa.grain()))
                            .collect();
                        let masses: Vec<Rat> = (0..delta.len())
                            .map(|c| -> Result<Rat, HnnError> {
                                let e = fa.mass(c)?.enclosure()?;
                                Ok((&e.lower + &e.upper) / Rat::from_integer(BigInt::from(2)))
                            })
                            .collect::<Result<_, _>>()?;
                        let total: Rat = masses.iter().sum();
                        if total.is_positive() {
                            let mean: Rat = masses.iter().zip(&delta).map(|(p, d)| p * d).sum::<Rat>() / &total;
                            let second: Rat = masses.iter().zip(&delta).map(|(p, d)| p * d * d).sum::<Rat>() / &total;
                            variance += second - &mean * &mean;
                            readings += 1;
                        }
                    }
                }
                if !feed(reference, &mut held, &cells[spans[j].clone()])?
                    || !feed(reference, &mut back, &cells[spans[j].clone()])?
                {
                    break;
                }
                j += 1;
                if j >= spans.len() || j >= k + options.information || cells[spans[j].clone()].len() != aperture {
                    break;
                }
                let next_window = &cells[spans[j].clone()];
                let (ca, _, fa) = read(reference, &mut held, next_window)?;
                let (cb, _, fb) = read(reference, &mut back, next_window)?;
                let d = interval_difference(&cb, &ca)?;
                tally(&d, &mut counts);
                code_difference = interval_sum(&code_difference, &d)?;
                faces_pair = (fa, fb);
            }
            cumulative.push(CumulativeContacts {
                aeon,
                position: span.start,
                exponent_shift: shift(held_faces.as_ref(), back_faces.as_ref()),
                spread,
                held: held_code,
                reverted: back_code,
                readings,
                variance,
                code_difference,
                better: counts.0,
                worse: counts.1,
                undecided: counts.2,
                receiving_largest: resident
                    .constitution()
                    .receiving_map(receiving_ring)
                    .map(|m| m.entries().iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero))
                    .unwrap_or_else(Rat::zero),
                receiving_change: {
                    let now = resident.constitution().receiving_map(receiving_ring).cloned();
                    let change = match (&last_receiving, &now) {
                        (Some(a), Some(b)) => {
                            let scale = b.entries().iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero);
                            let moved = a
                                .entries()
                                .iter()
                                .zip(b.entries())
                                .map(|(x, y)| (x - y).abs())
                                .max()
                                .unwrap_or_else(Rat::zero);
                            if scale.is_positive() { moved / scale } else { Rat::zero() }
                        }
                        _ => Rat::zero(),
                    };
                    last_receiving = now;
                    change
                },
            });
            on_boundary(cumulative.last().expect("pushed"), &out, &receiver);
        }
        let (pending, refined) = reference.refine(&mut resident, &moment, &phases)?;
        let word = match &refined.receipt.detail {
            ReceiptDetail::Refine { word, .. } => word.as_ref().clone(),
            _ => return Err(HnnError::Shape { what: "a refine's word balance", expected: 1, found: 0 }),
        };
        let (staged, compared) = reference.compare(&mut resident, pending, &one_hot(window))?;
        if let (Some(next), Component::Present(deposit)) = (next, &compared.deposit) {
            let theta = resident.constitution().clone();
            let contacts: Vec<FactorStep> = deposit
                .factors()
                .iter()
                .filter(|s| matches!(s.gradient.locus(), Locus::Channel(_)))
                .cloned()
                .collect();
            if !contacts.is_empty() {
                let loci: Vec<Locus> = contacts.iter().map(|s| s.gradient.locus()).collect();
                let mut alone = Deposit::new(deposit.commit(), Vec::new(), contacts, loci);
                if let Some(reach) = deposit.reach() {
                    alone = alone.with_reach(reach.clone());
                }
                let (successor, reading) = theta.deposited(&alone)?;
                let successor_kept = successor.clone();
                let continued = |c: &Constitution| -> Result<(Vec<Vec<Rat>>, Faces), HnnError> {
                    let operands = Operands::at_cut(field, c, resident.current())?;
                    let nothing: Vec<Vec<Rat>> =
                        word.change.storage.iter().map(|w| vec![Rat::zero(); w.len()]).collect();
                    let mut carried = Word::continuing(
                        field,
                        operands,
                        &word.change,
                        &nothing,
                        phases.junction_steps(),
                    )?;
                    let anchors = carried.forward(&phases)?;
                    let reads = anchors
                        .iter()
                        .map(|anchor| phases.read(field, c, resident.current(), anchor))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok((anchors, Faces::of_reads(&reads, phases.grain())?))
                };
                let (held_anchors, held_continued) = continued(&theta)?;
                let (moved_anchors, moved_continued) = continued(&successor)?;
                let before = PowerForm::read(field, &theta, resident.current())?;
                let after = PowerForm::read(field, &successor, resident.current())?;
                let work = before.deposition_work(&after, &word.change)?;
                let mut held = resident.clone();
                let mut moved_res = resident.clone();
                moved_res.constitution = successor;
                moved_res.forget_kept_reads();
                let (open_held, open_moved) = (
                    feed(reference, &mut held, window)?,
                    feed(reference, &mut moved_res, window)?,
                );
                if open_held && open_moved {
                    let (held_code, held_states, held_faces) = read(reference, &mut held, next)?;
                    let (moved_code, moved_states, moved_faces) = read(reference, &mut moved_res, next)?;
                    out.push(ContactAblation {
                        position: span.start,
                        aeon,
                        moved: reading
                            .steps
                            .iter()
                            .filter(|(l, s)| !reading.vanished.contains(&(*l, s.family)))
                            .map(|(l, s)| (*l, s.family))
                            .collect(),
                        vanished: reading.vanished.clone(),
                        work,
                        held: held_code,
                        contacts: moved_code,
                        states_differ: held_states != moved_states,
                        logits_differ: held_faces.as_ref().map(|f| &f.logits)
                            != moved_faces.as_ref().map(|f| &f.logits),
                        faces_differ: held_faces.as_ref().map(|f| &f.faces)
                            != moved_faces.as_ref().map(|f| &f.faces),
                        continued_anchors_differ: held_anchors != moved_anchors,
                        continued_logits_differ: held_continued.logits != moved_continued.logits,
                        continued_faces_differ: held_continued.faces != moved_continued.faces,
                        cells_differ: grained(held_faces.as_ref()) != grained(moved_faces.as_ref()),
                        continued_cells_differ: grained(Some(&held_continued))
                            != grained(Some(&moved_continued)),
                        factor_change: factor_change(&theta, &successor_kept),
                        contact_families: reading.steps.len(),
                        contact_vanished: reading.vanished.len(),
                        contact_alignment: reading.steps.iter().map(|(_, s)| s.step.alignment.clone()).sum(),
                        anchor_change: {
                            let scale = held_anchors.iter().flatten().map(|x| x.abs()).max().unwrap_or_else(Rat::zero);
                            let moved = held_anchors
                                .iter()
                                .flatten()
                                .zip(moved_anchors.iter().flatten())
                                .map(|(p, q)| (p - q).abs())
                                .max()
                                .unwrap_or_else(Rat::zero);
                            if scale.is_positive() { moved / scale } else { Rat::zero() }
                        },
                        exponent_spread: held_continued
                            .faces
                            .iter()
                            .map(|face| {
                                let v: Vec<Rat> = face
                                    .cells()
                                    .iter()
                                    .map(|c| {
                                        Rat::from_integer(c.carry.clone())
                                            + Rat::new(BigInt::from(c.phase), BigInt::from(face.grain()))
                                            + &c.fibre
                                    })
                                    .collect();
                                let hi = v.iter().max().cloned().unwrap_or_else(Rat::zero);
                                let lo = v.iter().min().cloned().unwrap_or_else(Rat::zero);
                                hi - lo
                            })
                            .max()
                            .unwrap_or_else(Rat::zero),
                        exponent_shift: shift(held_faces.as_ref(), moved_faces.as_ref()),
                        continued_exponent_shift: shift(Some(&held_continued), Some(&moved_continued)),
                    });
                }
            }
        }
        let before = if options.descent {
            let mut pre = resident.clone();
            Some(read(reference, &mut pre, window)?)
        } else {
            None
        };
        match reference.deposit(&mut resident, staged) {
            Ok(returned) => {
                if let Some((before_code, _, before_faces)) = before {
                let mut post = resident.clone();
                let (after_code, _, after_faces) = read(reference, &mut post, window)?;
                let (mut a_plus, mut a_minus) = (Rat::zero(), Rat::zero());
                if let (Some(fa), Some(fb)) = (&before_faces, &after_faces) {
                    let value = |c: &crate::receiver::face::GrainCell, grain: u64| {
                        Rat::from_integer(c.carry.clone())
                            + Rat::new(BigInt::from(c.phase), BigInt::from(grain))
                            + &c.fibre
                    };
                    for ((x, y), &target) in fa.faces.iter().zip(&fb.faces).zip(window) {
                        let masses = x.odometer_masses()?;
                        let delta: Vec<Rat> = x
                            .cells()
                            .iter()
                            .zip(y.cells())
                            .map(|(p, q)| value(q, y.grain()) - value(p, x.grain()))
                            .collect();
                        for (c, (d, p)) in delta.iter().zip(&masses).enumerate() {
                            if c == target {
                                continue;
                            }
                            let relative = d - &delta[target];
                            if relative.is_negative() {
                                a_plus -= p * &relative;
                            } else {
                                a_minus += p * &relative;
                            }
                        }
                    }
                }
                descents.push(DepositDescent {
                    aeon,
                    a_plus,
                    a_minus,
                    before: before_code,
                    after: after_code,
                });
                }
                if let Component::Present(reading) = &returned.deposit {
                    for (locus, carrier, entry, residual) in &reading.released {
                        if matches!(locus, Locus::Channel(_)) {
                            let slot = released.entry((*locus, *carrier, *entry)).or_default();
                            slot.sum += residual;
                            slot.magnitude += residual.abs();
                            slot.squares += residual * residual;
                            slot.count += 1;
                        }
                    }
                    for (locus, step) in &reading.steps {
                        if matches!(locus, Locus::ReceivingMap(_)) {
                            receiver.push(ReceiverStep {
                                aeon,
                                alignment: step.step.alignment.clone(),
                                step: step.step.step.clone(),
                                moved: !reading.vanished.contains(&(*locus, step.family)),
                            });
                        }
                    }
                }
            }
            Err(HnnError::ConstitutionBudget { .. }) => break,
            Err(other) => return Err(other),
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) =
                reference.ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))?;
            let ingested = ingested.forward.into_present().expect("ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                reference.close_aeon(&mut resident, &family)?;
                aeon += 1;
                boundary = true;
            }
        }
    }
    Ok(AblationRun {
        windows: out,
        cumulative,
        receiver,
        descents,
        released,
    })
}

/// [definition] **What an exposure reads of a port's resident** beside the port's own methods: the
/// admitted family, the published constitution, the budget stop, an open moment, the lift point,
/// the state's bits with and without the collapse, the executed charts' tally and the wall time by
/// phase. The host reference's [`Resident`] answers them, and so does a device's resident, so the
/// exposure protocol is stated once ([`expose`]) for every realization of the port.
pub trait ExposedResident {
    fn admitted(&self) -> &[ReceivingPhases];
    fn constitution(&self) -> &Constitution;
    fn stopped(&self) -> Option<&BudgetStop>;
    fn moment(&self, id: &MomentId) -> Option<&SourceMoment>;
    fn current(&self) -> &Current;
    fn state_bits(&self) -> u64;
    fn state_bits_without_collapse(&self) -> u64;
    fn tally(&self) -> &ChartTally;
    fn wall(&self) -> &WallTimes;
}

impl ExposedResident for Resident {
    fn admitted(&self) -> &[ReceivingPhases] {
        Resident::admitted(self)
    }
    fn constitution(&self) -> &Constitution {
        Resident::constitution(self)
    }
    fn stopped(&self) -> Option<&BudgetStop> {
        Resident::stopped(self)
    }
    fn moment(&self, id: &MomentId) -> Option<&SourceMoment> {
        Resident::moment(self, id)
    }
    fn current(&self) -> &Current {
        Resident::current(self)
    }
    fn state_bits(&self) -> u64 {
        Resident::state_bits(self)
    }
    fn state_bits_without_collapse(&self) -> u64 {
        Resident::state_bits_without_collapse(self)
    }
    fn tally(&self) -> &ChartTally {
        Resident::tally(self)
    }
    fn wall(&self) -> &WallTimes {
        Resident::wall(self)
    }
}

/// [definition] **The declarations an exposure reads off its port**: the constitution's budget and
/// the pending capacity (which [`Field::describe`] codes), and the deadline in windows
/// ([`Reference::with_deadline`]).
#[derive(Clone, Copy, Debug)]
pub struct Declared {
    pub budget: u64,
    pub pending_capacity: usize,
    pub deadline: Option<u64>,
}

/// **Run campaign 1's exposure protocol on a cut through any execution port** (module header, "The
/// exposure"): the one protocol the host reference ([`Reference::expose`]) and a device realization
/// run, so their readouts are comparable line for line.
pub fn expose<P>(
    port: &P,
    declared: &Declared,
    field: &Field,
    cut: &Cut,
) -> Result<Exposure, HnnError>
where
    P: ExecutionPort,
    P::Resident: ExposedResident,
{
    if cut.cells.len() as u64 != field.population() {
        return Err(HnnError::Shape {
            what: "the cut's cells against the declared population",
            expected: usize::try_from(field.population()).unwrap_or(usize::MAX),
            found: cut.cells.len(),
        });
    }
    let resident = port.mount(field, &Current::at_rest(field))?;
    expose_from(port, declared, field, cut, resident)
}

/// Continue the standard exposure protocol from an already mounted resident.
pub fn expose_from<P>(
    port: &P,
    declared: &Declared,
    field: &Field,
    cut: &Cut,
    mut resident: P::Resident,
) -> Result<Exposure, HnnError>
where
    P: ExecutionPort,
    P::Resident: ExposedResident,
{
    if cut.cells.len() as u64 != field.population() {
        return Err(HnnError::Shape {
            what: "the cut's cells against the declared population",
            expected: usize::try_from(field.population()).unwrap_or(usize::MAX),
            found: cut.cells.len(),
        });
    }
    let declared_physics = resident.constitution().describe_physics();
    let declared_physics_bits = declared_physics.len() as u64;
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
    let mut locate = |resident: &mut P::Resident, span: Range<usize>| -> Result<(), HnnError> {
        if span.len() > crib.offset {
            let at = span.end as u64;
            let located = port.locate_keys(resident, &one_hot(&cells[span]), crib.offset)?;
            keys.push(KeyReport {
                cell: at,
                detail: located.receipt.detail,
            });
        }
        Ok(())
    };
    let (moment, _) = port.ingest(&mut resident, None, &[])?;
    let mut aeon_start = 0usize;
    let mut training = Bits::empty();
    let mut held_out = Bits::empty();
    let mut baselines = Baselines::new(alphabet)?;
    let mut aeons = Vec::new();
    let mut course = Vec::new();
    let mut leg = Leg::open();
    let mut readout = ReadoutWall::default();
    let started = Instant::now();
    let contacts = site_readings(field, resident.constitution())?;
    readout.census += started.elapsed();
    let mut curve = vec![CurvePoint {
        commit: resident.constitution().commit(),
        bits: resident.constitution().carrier_bits(),
        released_bits: 0,
        stepped: 0,
        contacts,
        steps: Vec::new(),
        vanished: Vec::new(),
        storage_growth: Rat::zero(),
    }];
    let mut words = WordBalances {
        closed: true,
        ..WordBalances::default()
    };
    let (mut windows, mut open_windows, mut peak_word_bits) = (0u64, 0u64, 0u64);
    let (mut forward, mut adjoint) = (Remainders::default(), Remainders::default());
    let (mut balances, mut closed) = (0u64, true);
    let (mut largest_residual, mut residual_bound) = (Rat::zero(), Rat::zero());
    let mut stop = None;
    let mut work = ExactWork::nothing();
    let (mut compares, mut deposits) = (0u64, 0u64);
    let mut deadline = None;
    // The receiving windows are the epochs of the cut's cell clock at the receiver's section
    // (`ReceivingPhases::windows`): the loop reads them, and its position is the epoch's opening.
    let mut position = 0usize;
    for span in phases.windows(cells.len())? {
        position = span.start;
        let end = span.end;
        let window = &cells[position..end];
        if window.len() == aperture && declared.deadline.is_some_and(|windows| compares >= windows)
        {
            deadline = Some(position as u64);
            break;
        }
        if window.len() == aperture {
            let (pending, refined) = port.refine(&mut resident, &moment, &phases)?;
            work = work.then(&refined.receipt.work);
            if let ReceiptDetail::Refine {
                path,
                peak_bits,
                remainders,
                ..
            } = &refined.receipt.detail
            {
                windows += 1;
                open_windows += u64::from(path.open);
                peak_word_bits = peak_word_bits.max(*peak_bits);
                forward = forward.join(remainders);
            }
            for balance in &refined.receipt.balances {
                balances += 1;
                closed &= balance.closes();
                if balance.residual.abs() > largest_residual {
                    largest_residual = balance.residual.abs();
                    residual_bound = balance.bound.clone();
                }
            }
            // The word's whole balance, carried across the commit that follows (campaign 2).
            let mut word = match &refined.receipt.detail {
                ReceiptDetail::Refine { word, .. } => word.as_ref().clone(),
                _ => {
                    return Err(HnnError::Shape {
                        what: "a refine's receipt with the word's balance",
                        expected: 1,
                        found: 0,
                    });
                }
            };
            let (staged, compared) = port.compare(&mut resident, pending, &one_hot(window))?;
            work = work.then(&compared.receipt.work);
            if let ReceiptDetail::Compare { released, .. } = &compared.receipt.detail {
                adjoint = adjoint.join(released);
            }
            compares += 1;
            let holon = compared
                .forward
                .into_present()
                .expect("a compare returns its ratio");
            // The model's (the population's) and the tree face alone's code lengths, its executed face
            // and its face at the grain (ruling A, the landmark tree): the compare's readings, each
            // phase at the standing after the window's earlier phases, before the deposit and the
            // window's ingest; the combined face's are the Holon ratio's.
            let (tree, tree_grain, model) = match &compared.receipt.detail {
                ReceiptDetail::Compare {
                    tree,
                    tree_grain,
                    model,
                    ..
                } => (tree.clone(), tree_grain.clone(), model.clone()),
                _ => {
                    return Err(HnnError::Shape {
                        what: "a compare's receipt with the tree face and the model",
                        expected: 1,
                        found: 0,
                    });
                }
            };
            for (offset, ((((phase, tree), grained), model), &code)) in holon
                .phases()
                .iter()
                .zip(&tree)
                .zip(&tree_grain)
                .zip(&model)
                .zip(window)
                .enumerate()
            {
                let bits = if cut.held_out(position + offset) {
                    &mut held_out
                } else {
                    &mut training
                };
                bits.model = interval_sum(&bits.model, model)?;
                bits.tree = interval_sum(&bits.tree, tree)?;
                bits.tree_grain = interval_sum(&bits.tree_grain, grained)?;
                bits.combined = interval_sum(&bits.combined, &phase.code_length)?;
                code_baselines(&mut baselines, bits, code)?;
                leg.add(model, tree, &phase.code_length)?;
            }
            // Prequential scoring: every compared window is deposited, held-out windows
            // included; only the budget stop discards.
            if resident.stopped().is_some() {
                port.discard(&mut resident, Handle::Staged(staged))?;
            } else {
                // The power form at the word's cut before the deposit: the commit's `Θ`.
                let started = Instant::now();
                let before = PowerForm::read(field, resident.constitution(), resident.current())?;
                readout.balance += started.elapsed();
                match port.deposit(&mut resident, staged) {
                    Ok(returned) => {
                        work = work.then(&returned.receipt.work);
                        deposits += 1;
                        let (released_bits, stepped) = returned
                            .deposit
                            .present()
                            .map_or((0, 0), |reading| (reading.released_bits, reading.stepped));
                        let vanished = returned
                            .deposit
                            .present()
                            .map_or_else(Vec::new, |reading| reading.vanished.clone());
                        let (steps, storage_growth) = returned.deposit.present().map_or_else(
                            || (Vec::new(), Rat::zero()),
                            |reading| {
                                (
                                    reading
                                        .steps
                                        .iter()
                                        .map(|(locus, step)| {
                                            (*locus, step.family, step.step.exponent)
                                        })
                                        .collect(),
                                    reading.storage_growth.clone(),
                                )
                            },
                        );
                        let started = Instant::now();
                        let after =
                            PowerForm::read(field, resident.constitution(), resident.current())?;
                        word.commit(&before, &after)?;
                        readout.balance += started.elapsed();
                        let started = Instant::now();
                        let contacts = site_readings(field, resident.constitution())?;
                        readout.census += started.elapsed();
                        curve.push(CurvePoint {
                            commit: resident.constitution().commit(),
                            bits: resident.constitution().carrier_bits(),
                            released_bits,
                            stepped,
                            contacts,
                            steps,
                            vanished,
                            storage_growth,
                        });
                    }
                    Err(refusal @ HnnError::ConstitutionBudget { .. }) => {
                        stop = BudgetStop::of(&refusal).map(|stop| (stop, position as u64));
                    }
                    Err(other) => return Err(other),
                }
            }
            words.record(&word);
        } else {
            for &code in window {
                baselines.update(code);
            }
        }
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) =
                port.ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))?;
            let ingested = ingested.forward.into_present().expect("ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                let at = position + fed;
                course.push(leg.close(at as u64, resident.constitution(), phases.ring())?);
                let closed = port.close_aeon(&mut resident, &family)?;
                aeons.push(closed.forward.into_present().expect("a boundary"));
                locate(&mut resident, cut.closing_crib(aeon_start, at, crib.window))?;
                aeon_start = at;
            }
        }
        position = end;
    }
    let description_bits = field
        .describe(declared.budget, declared.pending_capacity)
        .len() as u64
        + declared_physics_bits;
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
        course: {
            course.push(leg.close(position as u64, resident.constitution(), phases.ring())?);
            course
        },
        constitution_curve: curve,
        windows,
        open_windows,
        peak_word_bits,
        complete: stop.is_none() && deadline.is_none(),
        stop,
        deadline,
        description_bits,
        resonator_gains: resident.constitution().resonator_gains(),
        resonator_remainders: resident.constitution().resonator_gain_remainders(),
        key_bits,
        kt,
        literal_bits: symbol * position as u64,
        work,
        state,
        compares,
        deposits,
        word: WordReport {
            charts: resident.tally().clone(),
            forward,
            adjoint,
            balances,
            closed,
            largest_residual,
            residual_bound,
            words,
        },
        wall: *resident.wall(),
        readout,
        population: resident
            .constitution()
            .population(phases.ring())
            .map(PopulationReport::of)
            .transpose()?,
    })
}

// -------------------------------------------------------------------------------------------
// the landmark tree's prequential measurement on a cut

/// [definition; agent-inferred] **The landmark tree's prequential measurement on a cut** (the tree
/// is `compression::landmark::context`'s; the cut is the exposure's, [`Cut`]): the tree over the
/// ticks' letters and the online baselines (`compression::landmark::context::baseline`) over the
/// same cells in the same order, each cell scored at the current standing and then deposited, with
/// exact enclosures on the development and held-out populations ([`prequential`], and the tree alone
/// `tree_prequential` (retired September 30 after batch P; last at `8a1b41cf`)). [historical; September 30, batch H] The count-only development choices
/// are retired with their last consumer, the notebook's `hnn_landmark` (N1): source at
/// [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/reference.rs),
/// their readings in the landmark tree's September 26 records. Their rules, read on the
/// development cells only: the depth sweep (`choose_depth`, `choose_depth_within`) raised `D` from
/// `max(1, forced)` while the development code fell strictly by disjoint enclosures (or to a
/// declared deepest depth), charged `⌈log₂⌉` of the depths tried; the stop-prior sweep
/// (`choose_prior`) ran each declared law at its own depth sweep and chose the least charged law
/// only when its enclosure lay strictly below the `½` incumbent's, charged `⌈log₂⌉` of the laws;
/// `oracle_cost` compared the executed face with the reference oracle (`IdealLandmarks`) cell by
/// cell against the certificate plus the oracle's own rule.

fn measurement_shape(what: &'static str, expected: usize, found: usize) -> HnnError {
    HnnError::Shape {
        what,
        expected,
        found,
    }
}

/// [definition] **Code lengths on one population**, each an enclosure of the population's faces'
/// product ([`PassageCode`]) over `cells` cells: the tree's executed face and the online baselines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coded {
    pub tree: ExactInterval,
    pub uniform: ExactInterval,
    pub order_zero: ExactInterval,
    pub order_one: ExactInterval,
    pub ppm: ExactInterval,
    pub cells: u64,
}

/// [definition] **One tree's run**: its declaration and widths, its chart's report, its stored nodes,
/// its label pool's letters (stored where paths part) and stored bits, the rule's a-priori residual a cell and
/// the largest per-cell certified residual over the run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeRun {
    pub declaration: LandmarkDeclaration,
    pub widths: Widths,
    pub chart: ChartReport,
    pub nodes: usize,
    pub held: usize,
    pub bits: u64,
    pub face_rule: Rat,
    pub largest_residual: Rat,
}

/// [definition] **The prequential measurement** ([`prequential`]): the development and held-out
/// populations' code lengths and the tree's run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prequential {
    pub development: Coded,
    pub held_out: Coded,
    pub run: TreeRun,
}

/// Refused unless there is one letter per cell.
fn aligned(cells: &[usize], letters: &[Letter]) -> Result<(), HnnError> {
    if cells.len() != letters.len() {
        return Err(measurement_shape(
            "one tick's letter per cell",
            cells.len(),
            letters.len(),
        ));
    }
    Ok(())
}

/// A tree's prequential sums over one stream, `[development, held-out]`, and the run.
fn run_tree(
    cells: &[usize],
    letters: &[Letter],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    declaration: &LandmarkDeclaration,
) -> Result<([ExactInterval; 2], TreeRun), HnnError> {
    aligned(cells, letters)?;
    let mut tree = Landmarks::new(declaration.clone())?;
    let mut codes = [PassageCode::new(), PassageCode::new()];
    let mut largest_residual = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree.receive(&letter_address(letters, position, declaration.depth), class)?;
        codes[usize::from(held_out(position))].face(&reading.executed)?;
        if reading.residual > largest_residual {
            largest_residual = reading.residual;
        }
    }
    Ok((
        [codes[0].bits()?, codes[1].bits()?],
        TreeRun {
            declaration: declaration.clone(),
            widths: tree.widths(),
            chart: tree.chart(),
            nodes: tree.nodes(),
            held: tree.held(),
            bits: tree.bits(),
            face_rule: tree.face_rule(),
            largest_residual,
        },
    ))
}

/// The baselines' prequential sums over one stream, `[development, held-out]`, and the counts.
fn run_baselines(
    cells: &[usize],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    alphabet: usize,
) -> Result<([BaselineCodes; 2], [u64; 2]), HnnError> {
    let mut baselines = Baselines::new(alphabet)?;
    let mut codes = [[PassageCode::new(); 4]; 2];
    let mut counts = [0u64; 2];
    for (position, &class) in cells.iter().enumerate() {
        let faces = baselines.face_cell(class)?;
        let part = usize::from(held_out(position));
        for (code, face) in codes[part].iter_mut().zip([
            &faces.uniform,
            &faces.order_zero,
            &faces.order_one,
            &faces.ppm,
        ]) {
            code.face(face)?;
        }
        counts[part] += 1;
    }
    let sums = |[uniform, order_zero, order_one, ppm]: [PassageCode; 4]| {
        Ok::<_, HnnError>(BaselineCodes {
            uniform: uniform.bits()?,
            order_zero: order_zero.bits()?,
            order_one: order_one.bits()?,
            ppm: ppm.bits()?,
        })
    };
    let [development, held] = codes;
    Ok(([sums(development)?, sums(held)?], counts))
}

/// **The prequential measurement on a cut** (the section header): the tree over the ticks' letters and
/// the online baselines over the same cells in the same order, each cell scored at the current
/// standing and then deposited, with enclosures on the development and held-out populations.
pub fn prequential(
    cut: &Cut,
    letters: &[Letter],
    declaration: &LandmarkDeclaration,
) -> Result<Prequential, HnnError> {
    let held_out = |position: usize| cut.held_out(position);
    let (tree, baselines) = rayon::join(
        || run_tree(&cut.cells, letters, &held_out, declaration),
        || run_baselines(&cut.cells, &held_out, declaration.alphabet),
    );
    let ([development_tree, held_tree], run) = tree?;
    let ([development, held], counts) = baselines?;
    let coded = |tree: ExactInterval, baselines: BaselineCodes, cells: u64| Coded {
        tree,
        uniform: baselines.uniform,
        order_zero: baselines.order_zero,
        order_one: baselines.order_one,
        ppm: baselines.ppm,
        cells,
    };
    Ok(Prequential {
        development: coded(development_tree, development, counts[0]),
        held_out: coded(held_tree, held, counts[1]),
        run,
    })
}

