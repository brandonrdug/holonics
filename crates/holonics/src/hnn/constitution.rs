//! **The constitution `Θ`: its one owner, per locus and factored, and its deposition.**
//!
//! [definition] `Θ` is the medium (design (a), "The one object"). [`Constitution`] is its one owner:
//! every learned map, the standings `q` included, with the declared steps `γ_U` and `η_x`, a commit
//! counter and the bit budget `B_Θ`. Its fields are private; only [`Constitution::deposited`] (the
//! successor of a staged deposit) and the collapse at an aeon boundary change it (guard 4). It holds
//! the current parameters and their normal statistics, and no list of deposits, updates, gradients
//! or producers. The guarantee is structural, the struct's own private fields; the doctest shows
//! only that no field named `deposits` exists (`E0609`, no such field), and the runtime guard
//! (`tests/guards.rs`, guard 4) reads the loci and statistics after deposits:
//!
//! ```compile_fail,E0609
//! use holonics::hnn::Constitution;
//! // No journal by that name: a constitution has no `deposits` field (guard 4).
//! fn replay(theta: &Constitution) -> usize {
//!     theta.deposits.len()
//! }
//! ```
//!
//! [definition] **Loci** ([`Locus`]). Per ring `g`: its element (the passive factor `f_g` with
//! `W_s,g = −f_g f_gᵀ`, the contrast port `W_c,g`, the skew slices `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ`), its
//! standing `q_g`, on a source ring its source ports (`E_g` and the factored pair port `E_g^(δ)`),
//! on a receiving ring its receiving map `R` and the receiving parametron's landmark tree
//! (Decision 28, `hnn::landmark::Landmarks`), both at the receiving locus. Per contact `a`: its channel's
//! square factors (`C_a = c_a c_aᵀ`, `K_a = b_a b_aᵀ`, `D_a = F_a F_aᵀ`). The junction admittance `Y_g` and the
//! contact conductance `G_a` (`Y_a`, `β_a`, the screws) are declared on the field in campaign 1; the
//! collapse names them as loci, but they carry no learned value.
//!
//! [definition] **Deposition** (design (a), `deposit`; Lean `HNN/Normal`), the exact update `Δ` of
//! each locus at the predecessor's lattice-valued operands:
//!
//! ```text
//! ΔH_U = Σ_t w f_t f_tᵀ ,            ΔW_U = γ_U Σ_t w g_t (H_U'⁻¹ f_t)ᵀ ,  H_U' the carried successor Gram    per linear locus (E_g, R, W_c)
//! Δh_x = Σ_t w |f_t|² ,              Δx = η_x G_x / h_x' ,                 h_x' the carried successor statistic  per factor family
//! n_s(t) += 1, β_s ← β_s k_s(t)/q    per reached comparison, on the path its address a opens (target t)       the landmark tree
//! ```
//!
//! [definition; agent-inferred] **Decision 28 at the receiving locus.** The receiving map `R` keeps
//! the prox step on its reached covectors (Decisions 22 and 24), the covector of the ratio read on
//! the combined face (`hnn::receiving::ReceivingRead::combined`). Beside it the receiving
//! parametron stores its landmark tree (`hnn::landmark::Landmarks`, declared from the receiver by
//! `hnn::receiving::landmark_declaration`), which each reached comparison deposits on the path its
//! causal address opens ([`LandmarkStep`], in cell order); its counts are integers of half-units
//! and its mixture ratios are carried by the owner's β chart, so no lattice carry and no clock is
//! read for it. It shares the locus's diamond row (retained always) and its collapse rule (never
//! released; Lean `HNN/LandmarkTree.release_rule`: only nodes deeper than `D` are releasable, and
//! there are none). Decision 27's region table, its depth-one case, is retired from Rust; its laws
//! stay in Lean `HNN/RegionCounts`. Decision 26's exogenous law and standing read are retired: the
//! tree's face contains the marginal (Lean `HNN/TargetFace`'s finite-chart obstruction stays a
//! theorem).
//!
//! [definition; agent-inferred] **The carrier lattice and the budgeted release** (Lean
//! `HNN/LatticeDeposit`). Exact rational deposition compounds: the maps that form each other's
//! covectors (`E`, `R`, `W_c` through the word's inverses) feed their denominators into the next
//! deposit (measured on the chain control: 1,126 → 10,883 → 623,415 bits over two deposits). By
//! CLAUDE.md's exact representation law ("when a value outgrows its carrier, it is rebased,
//! factored or re-represented with its decoder and residual"), with the Ratio's `div_rem` and the
//! carry cocycle (`Geometry/PhaseCarry.carry_cocycle`: helix = circle + carry, the lattice
//! coordinate the winding and the remainder its phase), every entry of a locus `ℓ` (its maps,
//! factors and statistics) lives on the field's declared lattice `2^(−L_ℓ)ℤ` ([`Lattice`],
//! `Field::lattice`) with a carried remainder `r`. A remainder carried exactly keeps a bounded
//! magnitude but a denominator that accumulates every update's, and releasing it at the aeon
//! collapse bounds neither its bits (an aeon is a first-passage time of the joint clock's carry
//! chain, with no upper bound) nor the drift (the releases add across aeons). The retention law
//! applied to the whole admitted future gives the budget instead: the total released since a
//! locus's founding stays below the one-unit deviation the lattice rule certifies. Each locus keeps
//! a **deposit clock** `m` ([`Constitution::clock`]): the count of epochs at the locus's section,
//! the deposits that reached it with a nonzero update. It starts at the locus's founding (the
//! field's mount, or a later founding), is not reset at an aeon boundary, and ends when the collapse
//! releases the locus whole. [definition] It is the flux reading of the aeon epoch owner at that
//! section: the constitution's commits are occurrences and its deposits the passages between them,
//! the locus's section is crossed by exactly the deposits that move it, and the section's reading of
//! the aeon since the founding is its flux, forward minus backward crossings
//! ([`crate::aeon::epochs`], [`crate::aeon::Epochs::flux`]; Lean
//! `Aeon/Clock/Epoch.{reading_eq_crossings, crossings_concat}`). Deposits only advance the
//! commits, so every crossing is forward and the flux is the count (the monotone case, as for a
//! ring section on the clock lift, `Epoch.monotone_count_is_flux`). The count is kept and the
//! ticks are not: the budgeted carry reads only `m`, so the count is the sufficient statistic of
//! the epochs for the admitted future, and it adds under concatenation across aeons
//! (`crossings_concat`). A deposit carries each entry at the precision of the Elias-gamma length
//! of `m` ([`gamma_length`], the field's own natural code) through [`BudgetedCarry`]:
//!
//! ```text
//! u = 2^(−L_ℓ) ,  k_m = 2⌊log₂ m⌋ + 1
//! y   = Δ + r_prev                                   exact
//! y   = y_f + e ,   y_f ∈ 2^(−L−k_m)ℤ nearest, ties upward ,   e ∈ [−½·2^(−L−k_m), ½·2^(−L−k_m))
//! y_f = q u + r ,   q nearest, ties upward ,   r ∈ [−u/2, u/2) ∩ 2^(−L−k_m)ℤ
//! entry += q u ;  carry r ;  release e (exact, in the deposit's reading)
//! ```
//!
//! The applied steps, the carried remainder and the released residuals equal the exact sum of the
//! updates, per entry (`lattice_deposit_accounting`); the releases of one entry since the locus's
//! founding sum to less than `u/2` (Kraft for the Elias-gamma lengths, `gamma_kraft_lt_one`,
//! `release_bounded_since_founding`), so the word always reads within one unit of the exact
//! accumulation of what reached the locus (`within_one_unit_since_founding`), which moves a linear
//! read (the normal-law maps `E_g`, `R`, `W_c`) by at most `X_ℓ 2^(−L_ℓ) ≤ 1/(2L_R)`, below every
//! admitted receiver's grain (`remainder_below_grain`); the factor loci enter the word as products
//! of their factors, and their bound is the word-level certificate owed in #62. A carried remainder is `ρ·2^(−L−k_m)` with `|ρ| ≤ 2^(k_m−1)`, so it
//! takes `O(L + log m)` bits (`remainder_numerator_bounded`, `remainder_rat_bits_bounded`). An
//! entry whose update is zero moves nothing and releases nothing (`carry_entry_zero`: its remainder
//! already lies on the finer lattice), and a deposit with no nonzero update at `ℓ` leaves the locus
//! and its clock (`carry_zero`). The aeon collapse releases no remainder of a retained locus and
//! resets no clock. Within one deposit an entry's updates compose exactly before its one release (a
//! residual staged by an earlier step of the same deposit is taken back into `y`), so each clock
//! value releases at most once per entry. [open] The counterfactual bound (how far the carried
//! trajectory is from the one whose updates are computed at never-rounded operands) is
//! `Objects/CommitRebase`'s `commit_chain_residual`, `Σ K^(n−1−i) r_i`, and needs a Lipschitz bound
//! `K` of the deposit map, which is owed. Brandon may override this choice.
//!
//! A [`NormalLaw`] keeps `W` and its Gram `H` of the locus's own width (no global Gram), each
//! carried, and the **solved chart** `X̂ ≈ H⁻¹` of the carried Gram (Decision 24, Lean
//! `HNN/LatticeWord`; [`SolvedChart`]): a lattice matrix on `2^(−L_s)ℤ` with its certified left
//! residual `δ = ‖1 − X̂H‖∞`, computed exactly, warm-started from the previous chart at each deposit
//! and refined by rounded Newton–Schulz steps until `δ ≤ δ_ℓ`, both declared by rule
//! ([`ChartRule`]) so that the prox identity's released residual moves a read by less than the
//! receiver's grain. The exact solved chart it replaces grew by the Hadamard bound of the carried
//! Gram (0.40 Mbit over 24 windows of the standing real cut, still growing). [proved-derived;
//! formal-checked] **The carried Gram stays positive
//! definite with no clamp** (Lean `carried_gram_posDef`, `carried_gram_posDef_rule`): every entry
//! of `H` is within one unit of the exact Gram `H_exact = I + Σ w f fᵀ ⪰ I`
//! (`within_one_unit_since_founding`), so `|vᵀ(H − H_exact)v| ≤ u(Σ|v_i|)² ≤ n·u·|v|²` for its
//! width `n`, and since the lattice rule's `X_ℓ` is at least `n`, `n·u ≤ 1/(2L_R)` and
//! `H ⪰ (1 − 1/(2L_R)) I` since the locus's founding. `B` is not carried: under `W H = B` it is
//! `W H`, and the prox step `W' = W + γ G X̂` (Lean `HNN/Normal.normal_prox_step` at the exact
//! inverse, `HNN/LatticeWord.prox_chart_residual` at the chart) needs only `W`, the chart of `H'` and
//! `G`. The factor carriers keep `C`, `K`, `D` and `−W_s` positive semidefinite as
//! squares, with no clamp and no projection (Lean `factorCarrier_psd`). [agent-inferred] `h_x` is a
//! statistic like `H`: it accumulates over deposits, starting at 1, so a factor step is
//! preconditioned by its family's own feature energy.
//!
//! [definition] **The budget and stop rule** (design (d), R3 §5): the successor is computed exactly
//! and its exact bits (every numerator and denominator: the lattice entries, the carried remainders,
//! the statistics and the solved charts at their lattices) are counted before publication. Past
//! `B_Θ` the deposit is refused with [`HnnError::ConstitutionBudget`], naming the loci that grew most; the predecessor
//! stays published. The lattice bounds the entries' bits (`lattice_bits_bounded`) and the clock the
//! remainders' (`remainder_rat_bits_bounded`); [`Constitution::carrier_bits`] reads the three parts
//! separately, and [`DepositReading`] the released residuals and their bits, with each chart's
//! certificate and released prox residual ([`ChartReading`]). The deposit clocks,
//! like the commit counter, are counters of `⌈log₂ m⌉` bits and are not counted against `B_Θ`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Normal.normal_prox_step` at the carried Gram, with `HNN/LatticeDeposit.within_one_unit_since_founding` | [`NormalLaw`]: `W` is the prox iterate at the carried Gram `H'` (`B` is not carried, so `W` is not the minimizer of the accumulated `J(W)`), and `H` stays within one unit of the exact statistic `I + Σ w f fᵀ` |
//! | `HNN/Normal.normal_prox_step`, `depositLocus_solves`; `HNN/LatticeWord.{prox_chart_residual, prox_chart_certificate}` | [`NormalLaw::deposited`] (the step at the carried Gram through the executed chart, its residual released and reported: [`ChartReading`]) |
//! | `HNN/LatticeWord.{nsStep, newton_schulz_left, rounded_refinement_residual_left, rounded_refinement_certificate_left, rowNorm, latticeChart}` | [`SolvedChart`] (the certificate and the rounded refinement) |
//! | `HNN/LatticeWord.{warm_start_residual, warm_start_certificate}` | [`SolvedChart`] (why the warm start takes the window's rank-one steps) |
//! | `HNN/LatticeWord.{roundedIter_certificate, newton_schulz_iter_left, inverse_chart_deviation}` | [`ChartRule`] (the lattice `L_s`, the target `δ_ℓ`, the refinement count) |
//! | `HNN/Normal.normalStatistic_standing`, `objective_eq_statisticObjective`, for its statistic `H` only (carried on the lattice) | [`NormalLaw::gram`] (keeps `H`, never the samples) |
//! | `HNN/Normal.deposit_local`, `windowGram_apply_eq_zero` | [`Constitution::deposited`] (per locus, only its window) |
//! | `HNN/Normal.reaction_deposit_storage_unchanged`, `reaction_deposits_keep_committed_energy` | [`DepositReading::growth`] |
//! | `HNN/Normal.factorCarrier_psd` | the factor families ([`FactorGradient`]) |
//! | `HNN/Normal.standing_deposit`, `sheetClass_locally_constant` | [`FactorGradient::Standing`] |
//! | `HNN/LatticeDeposit.{quot, rem, div_rem_spec, rem_bounds, quot_eq_zero_of_bounds, fine}` | [`Lattice::div_rem`] (the carry's fine split), [`Lattice::div_rem_coordinate`] (its coarse split) |
//! | `HNN/LatticeDeposit.{gammaLength, gamma_kraft_lt_one}` | [`gamma_length`] |
//! | `HNN/LatticeDeposit.{carry, release, carry_accounting, lattice_deposit_accounting, carry_zero, carry_entry_zero, carry_entry_below_grain}` | [`BudgetedCarry`], the carried deposit of every entry |
//! | `HNN/LatticeDeposit.{carried_remainder_bounded, remainder_numerator_bounded, remainder_rat_bits_bounded}` | [`Constitution::carried_remainders`], [`CarrierBits::remainders`] |
//! | `HNN/LatticeDeposit.{release_bounded, release_bounded_since_founding, within_one_unit_since_founding, remainder_below_grain}` | [`DepositReading::released`] |
//! | `HNN/LatticeDeposit.{carried_gram_posDef, carried_gram_posDef_rule}` | [`NormalLaw::gram`] (the carried Gram) |
//! | `HNN/LatticeDeposit.{lattice_bits_bounded, lattice_rat_bits_bounded}` | [`Constitution::carrier_bits`] |
//! | `HNN/LatticeDeposit.lattice_deposit_descends` | [`Constitution::deposited`] with `hnn::retention::collapse` |

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::landmark::{Landmarks, Letter};
use crate::hnn::moment::PairPort;
use crate::hnn::port::Deposit;
use crate::hnn::propagation::gram;
use crate::hnn::realization::{indexed, outer_rows};
use crate::hnn::receiving::landmark_declaration;
use crate::holon::deposition::CommittedEnergyBound;
use crate::ratio::linear::vector::{Chart, integral, lcm, matrix_form};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::{Rat, rat};

/// The declared constitution budget of campaign 1: `B_Θ = 2^33` exact bits.
pub const CAMPAIGN_ONE_BUDGET: u64 = 1 << 33;

// -------------------------------------------------------------------------------------------
// the carrier lattice

/// [definition; agent-inferred] **A declared carrier lattice** `2^(−L)ℤ` (Lean
/// `HNN/LatticeDeposit`): the Ratio's division with remainder at a dyadic unit. See the module
/// header for the law and its source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lattice {
    exponent: u32,
}

impl Lattice {
    pub const fn new(exponent: u32) -> Self {
        Self { exponent }
    }

    /// `L`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// `2^L`.
    fn scale(&self) -> BigInt {
        BigInt::one() << self.exponent as usize
    }

    /// The unit `2^(−L)`.
    pub fn unit(&self) -> Rat {
        Rat::new(BigInt::one(), self.scale())
    }

    /// Whether `value` lies on the lattice (Lean `OnLattice`).
    pub fn contains(&self, value: &Rat) -> bool {
        (self.scale() % value.denom()).is_zero()
    }

    /// **Division with remainder at the nearest lattice point, ties upward** (Lean
    /// `HNN/LatticeDeposit.{quot, rem, div_rem_spec, rem_bounds}`): `value = q·2^(−L) + r` with
    /// `q = ⌊value·2^L + ½⌋`, so `−2^(−L−1) ≤ r < 2^(−L−1)`, and a remainder alone divides to
    /// `q = 0` (`quot_eq_zero_of_bounds`). It is the budgeted carry's **fine split** (Lean `fine`,
    /// `release`), at the fine lattice `2^(−L−k_m)ℤ`. Read in the value's own chart: for
    /// `value = a/b` in lowest terms, `q = ⌊(2a·2^L + b)/2b⌋`, and the remainder's numerator
    /// `a·2^L − bq` shares only powers of two with its denominator `b·2^L` (`gcd(a, b) = 1`), so it
    /// is reduced by a shift: one integer division and no `gcd` of the value's size.
    pub fn div_rem(&self, value: &Rat) -> (BigInt, Rat) {
        let (numerator, denominator) = (value.numer(), value.denom());
        let scaled = numerator << self.exponent as usize;
        let top: BigInt = (&scaled << 1usize) + denominator;
        let bottom: BigInt = denominator << 1usize;
        let (mut quotient, residue) = (&top / &bottom, &top % &bottom);
        if residue.is_negative() {
            quotient -= 1;
        }
        let remainder = scaled - denominator * &quotient;
        if remainder.is_zero() {
            return (quotient, Rat::zero());
        }
        let whole = denominator << self.exponent as usize;
        let shift = remainder
            .trailing_zeros()
            .unwrap_or(0)
            .min(whole.trailing_zeros().unwrap_or(0));
        (quotient, Rat::new_raw(remainder >> shift, whole >> shift))
    }

    /// **The same division of a point given by its coordinate on a finer lattice** `2^(−L−k)ℤ`
    /// (Lean `quot`, `rem` at a point of `OnLattice (L + k)`): `P·2^(−L−k) = q·2^(−L) + ρ·2^(−L−k)`
    /// with `q = ⌊(P + 2^(k−1)) / 2^k⌋` (ties upward) and `ρ = P − q·2^k ∈ [−2^(k−1), 2^(k−1))`. It is
    /// the budgeted carry's **coarse split** of the fine point; at `k = 0` the point is on the
    /// lattice and `ρ = 0`.
    pub fn div_rem_coordinate(&self, point: &BigInt, finer: u32) -> (BigInt, BigInt) {
        if finer == 0 {
            return (point.clone(), BigInt::zero());
        }
        let quotient = (point + (BigInt::one() << (finer - 1) as usize)) >> finer as usize;
        let remainder = point - (&quotient << finer as usize);
        (quotient, remainder)
    }
}

/// [definition; agent-inferred] **The precision of the budgeted carry at deposit clock `m`**: the
/// Elias-gamma length `k_m = 2⌊log₂ m⌋ + 1` of `m` (Lean `HNN/LatticeDeposit.gammaLength`, `k_0 = 1`),
/// the field's own natural code (`field.rs`, `describe`). Its weights `2^(−k_m)` sum to less than one
/// over every clock (`gamma_kraft_lt_one`).
pub fn gamma_length(clock: u64) -> u32 {
    2 * clock.max(1).ilog2() + 1
}

/// [definition; agent-inferred] **One deposit's budgeted carry at one locus** (Lean
/// `HNN/LatticeDeposit.{step, carry, release}`; the module header states the law): the locus's
/// lattice `2^(−L)ℤ`, the clock `m` the deposit advances it to (its precision `k_m` names the fine
/// lattice `2^(−L−k_m)ℤ`), and what the deposit does there, staged by carrier and entry until it
/// publishes: each entry's released residual `e` (exact) and its applied coordinate `q`, and whether
/// any update at the locus was nonzero (only then does the clock advance).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetedCarry {
    lattice: Lattice,
    clock: u64,
    staged: BTreeMap<(Carrier, usize), (Rat, BigInt)>,
    moved: bool,
}

impl BudgetedCarry {
    /// At a locus's lattice, for the deposit that advances its clock to `clock` (`m ≥ 1`).
    pub fn new(lattice: Lattice, clock: u64) -> Self {
        Self {
            lattice,
            clock,
            staged: BTreeMap::new(),
            moved: false,
        }
    }

    /// `m`, the clock the deposit advances the locus to.
    pub fn clock(&self) -> u64 {
        self.clock
    }

    /// `k_m`.
    pub fn precision(&self) -> u32 {
        gamma_length(self.clock)
    }

    /// Whether any update at the locus was nonzero, so the clock advances (Lean `carry_zero`
    /// otherwise).
    pub fn moved(&self) -> bool {
        self.moved
    }

    /// **The released residuals** `e ≠ 0`, exact, by carrier and entry (Lean `release`): each at most
    /// `½·2^(−L−k_m)` (`release_bounded`).
    pub fn released(&self) -> Vec<(Carrier, usize, Rat)> {
        self.staged
            .iter()
            .filter(|(_, (residual, _))| !residual.is_zero())
            .map(|((carrier, entry), (residual, _))| (*carrier, *entry, residual.clone()))
            .collect()
    }

    /// The number of entries whose applied lattice coordinate `q` is nonzero (review R5).
    pub fn stepped(&self) -> u64 {
        self.staged
            .values()
            .filter(|(_, quotient)| !quotient.is_zero())
            .count() as u64
    }
}

/// [definition] **The carried remainders of one lattice-valued array** (Lean `Carried.rem`), by
/// flat entry index; a zero remainder is not stored, so two carriers with one content compare equal.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Carry(BTreeMap<usize, Rat>);

impl Carry {
    /// **One entry's budgeted deposit** (Lean `carry`, `carry_accounting`): `y = Δ + r_prev` split at
    /// the fine lattice `2^(−L−k_m)ℤ` into `y_f + e` and `y_f` at the lattice into `q·2^(−L) + r`; the
    /// entry moves by `q·2^(−L)`, `r` is carried and `e` is staged for release. A zero update moves
    /// nothing and releases nothing (`carry_entry_zero`). A residual staged by an earlier step of the
    /// same deposit at this entry is taken back into `y`, so the deposit releases once per entry.
    fn deposit(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        index: usize,
        entry: &mut Rat,
        update: &Rat,
    ) {
        if update.is_zero() {
            return;
        }
        at.moved = true;
        let staged = at.staged.remove(&(carrier, index));
        let previous = self.0.remove(&index);
        let carried = carried_entry(&at.lattice, at.precision(), entry, update, staged, previous);
        self.adopt(at, carrier, index, entry, carried)
    }

    /// Carry a whole flat array's update, entry by entry.
    ///
    /// [definition; agent-inferred] Each entry's step reads only its own update, staged residual
    /// and carried remainder, and writes only its own: the entries run together
    /// (`hnn::realization`), and their results are taken into the carry and the budgeted
    /// carry afterwards, in entry order.
    fn deposit_all(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        entries: &mut [Rat],
        updates: &[Rat],
    ) {
        let moving: Vec<(usize, Option<Staged>, Option<Rat>)> =
            (0..entries.len().min(updates.len()))
                .filter(|&index| !updates[index].is_zero())
                .map(|index| {
                    (
                        index,
                        at.staged.remove(&(carrier, index)),
                        self.0.remove(&index),
                    )
                })
                .collect();
        if moving.is_empty() {
            return;
        }
        at.moved = true;
        let (lattice, precision) = (at.lattice, at.precision());
        let current: &[Rat] = entries;
        let carried: Vec<(usize, CarriedEntry)> = moving
            .into_par_iter()
            .map(|(index, staged, previous)| {
                (
                    index,
                    carried_entry(
                        &lattice,
                        precision,
                        &current[index],
                        &updates[index],
                        staged,
                        previous,
                    ),
                )
            })
            .collect();
        for (index, step) in carried {
            self.adopt(at, carrier, index, &mut entries[index], step);
        }
    }

    /// Take one entry's carried step into the array, the carry and the budgeted carry.
    fn adopt(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        index: usize,
        entry: &mut Rat,
        step: CarriedEntry,
    ) {
        *entry = step.entry;
        if !step.remainder.is_zero() {
            self.0.insert(index, step.remainder);
        }
        if let Some(staged) = step.staged {
            at.staged.insert((carrier, index), staged);
        }
    }

    /// The remainder at an entry.
    fn at(&self, index: usize) -> Rat {
        self.0.get(&index).cloned().unwrap_or_else(Rat::zero)
    }

    fn bits(&self) -> u64 {
        self.0.values().map(bits).sum()
    }
}

/// An entry's staged residual `e` and applied coordinate `q` within one deposit.
type Staged = (Rat, BigInt);

/// **One entry's carried step**, read alone: the entry moved by `q·2^(−L)`, the remainder `r` to
/// carry, and the residual and coordinate to stage (none when both are zero).
struct CarriedEntry {
    entry: Rat,
    remainder: Rat,
    staged: Option<Staged>,
}

/// **One entry's budgeted deposit** of a nonzero update ([`Carry::deposit`], Lean `carry`,
/// `carry_accounting`) at the lattice and precision of its locus's deposit, from the entry, the
/// residual and coordinate an earlier step of the same deposit staged there, and the remainder the
/// entry carries.
fn carried_entry(
    lattice: &Lattice,
    precision: u32,
    entry: &Rat,
    update: &Rat,
    staged: Option<Staged>,
    previous: Option<Rat>,
) -> CarriedEntry {
    let (staged, applied) = staged.unwrap_or_else(|| (Rat::zero(), BigInt::zero()));
    let previous = previous.unwrap_or_else(Rat::zero);
    let exponent = lattice.exponent + precision;
    // y = Δ + staged + r_prev. The carried remainder lies on the fine lattice of an earlier
    // clock, so it moves the fine point by its own coordinate and adds nothing to `e`.
    let mut moving = if staged.is_zero() {
        update.clone()
    } else {
        update + &staged
    };
    let carried = match dyadic_coordinate(&previous, exponent) {
        Some(coordinate) => coordinate,
        None => {
            moving += &previous;
            BigInt::zero()
        }
    };
    let (point, residual) = Lattice::new(exponent).div_rem(&moving);
    let point = point + carried;
    // y_f = P·2^(−L−k): its coordinate at the lattice, nearest, ties upward.
    let (quotient, coordinate) = lattice.div_rem_coordinate(&point, precision);
    let remainder = Rat::new(coordinate, BigInt::one() << exponent as usize);
    let entry = entry + Rat::new(quotient.clone(), lattice.scale());
    let applied = applied + quotient;
    let staged = (!residual.is_zero() || !applied.is_zero()).then_some((residual, applied));
    CarriedEntry {
        entry,
        remainder,
        staged,
    }
}

/// The coordinate of `value` on `2^(−S)ℤ`, when it lies there (`None` otherwise).
fn dyadic_coordinate(value: &Rat, exponent: u32) -> Option<BigInt> {
    let denominator = value.denom();
    let twos = denominator.trailing_zeros().unwrap_or(0);
    (denominator.bits() == twos + 1 && twos <= u64::from(exponent))
        .then(|| value.numer() << (u64::from(exponent) - twos) as usize)
}

/// Carry a matrix update onto a lattice-valued matrix, refusing a mismatched shape.
fn carried_matrix(
    carry: &mut Carry,
    at: &mut BudgetedCarry,
    carrier: Carrier,
    matrix: &ExactRatMatrix,
    update: &ExactRatMatrix,
    what: &'static str,
) -> Result<ExactRatMatrix, HnnError> {
    if (update.rows(), update.columns()) != (matrix.rows(), matrix.columns()) {
        return Err(HnnError::Shape {
            what,
            expected: matrix.rows() * matrix.columns(),
            found: update.rows() * update.columns(),
        });
    }
    let mut entries = matrix.entries().to_vec();
    carry.deposit_all(at, carrier, &mut entries, update.entries());
    flat_matrix(matrix.rows(), matrix.columns(), entries)
}

fn flat_matrix(rows: usize, columns: usize, entries: Vec<Rat>) -> Result<ExactRatMatrix, HnnError> {
    let rows_vec: Vec<Vec<Rat>> = if columns == 0 {
        vec![Vec::new(); rows]
    } else {
        entries.chunks(columns).map(<[Rat]>::to_vec).collect()
    };
    Ok(ExactRatMatrix::shaped(rows, columns, rows_vec)?)
}

/// [definition] **The constitution's bits by carrier** (the budget's parts): the lattice entries
/// (maps, factors, statistics), their carried remainders, and the solved charts `X̂ ≈ H⁻¹` of the
/// carried Grams at their lattices, with their certificates; each value counted by its numerator's
/// and denominator's bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CarrierBits {
    pub entries: u64,
    pub remainders: u64,
    pub solved: u64,
}

impl CarrierBits {
    pub fn total(&self) -> u64 {
        self.entries + self.remainders + self.solved
    }

    fn add(&mut self, other: CarrierBits) {
        self.entries += other.entries;
        self.remainders += other.remainders;
        self.solved += other.solved;
    }
}

// -------------------------------------------------------------------------------------------
// loci

/// [definition] **A locus of the constitution**, as the collapse and the budget name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Locus {
    /// Ring `g`'s element: `W_s`, the slices, `W_c` (edge `g → g`).
    Element(usize),
    /// Ring `g`'s junction: `Y_g` (edges `g → g`, `g → h`), declared.
    Junction(usize),
    /// Contact `a`'s channel: `c_a`, `b_a`, `F_a` and its matchings.
    Channel(usize),
    /// Contact `a`'s conductance `G_a`: `Y_a`, `β_a` and the pair geometry, declared.
    Conductance(usize),
    /// Ring `g`'s source ports `E_g`, `E_g^(δ)`, `I_g`.
    SourcePort(usize),
    /// Ring `g`'s standing `q_g`.
    Standing(usize),
    /// Ring `g`'s receiving map `R`.
    ReceivingMap(usize),
}

impl Locus {
    /// **The design's operator-entry count** of a locus: an element's `n_g²`, a channel's `3k_a²`
    /// (its `C`, `K`, `D`), and zero for every other locus (design (a), retention item 3, the
    /// count `release.py` reports).
    pub fn entries(&self, field: &Field) -> usize {
        match *self {
            Locus::Element(ring) => field.ring(ring).width().pow(2),
            Locus::Channel(contact) => 3 * field.contact(contact).width().pow(2),
            _ => 0,
        }
    }
}

// -------------------------------------------------------------------------------------------
// steps

/// [definition] **The declared steps**: the normal law's proxy step `γ_U` and the factor step `η_x`
/// (one each in campaign 1, recorded in the field's description by the caller).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Steps {
    pub proxy: Rat,
    pub factor: Rat,
}

impl Steps {
    /// Campaign 1: `γ_U = 1` (the pure normal solve), `η_x = 1/2`.
    pub fn campaign_one() -> Self {
        Self {
            proxy: Rat::one(),
            factor: rat(1, 2),
        }
    }
}

// -------------------------------------------------------------------------------------------
// the solved chart

/// `⌈log₂ x⌉` for `x ≥ 1` (`0` at `x ≤ 1`).
fn ceil_log2(x: u128) -> u32 {
    if x <= 1 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    }
}

/// The widest shift a residual's coordinates take: `2^(L_s + e_H)` with its sign and one more bit
/// of headroom stays inside the `i128` carrier.
const RESIDUAL_SHIFT: u32 = 125;

/// [definition; agent-inferred] **The chart rule of a normal law's locus** (Decision 24; Lean
/// `HNN/LatticeWord.{prox_chart_certificate, rounded_refinement_certificate_left,
/// roundedIter_certificate}`), declared from the locus's carrier lattice `L_ℓ` and the finest
/// admitted receiver grain `L_R`, as `L_ℓ` is from `L_R` and `X_ℓ`:
///
/// ```text
/// target     δ_ℓ = 2^(−D_ℓ) ,   D_ℓ = 2L_ℓ + 1 − ⌊log₂ L_R⌋        (so δ_ℓ ≤ L_R·2^(−2L_ℓ−1))
/// lattice    L_s = D_ℓ + ⌈log₂ n⌉ + ⌈log₂ ‖H'‖∞⌉ + 2                (n the Gram's width)
/// ```
///
/// **Why the target.** At an executed chart `X̂` of the carried successor Gram `H'`, the map step
/// `ΔW = γ Σ w g fᵀX̂` leaves the prox identity `(W + ΔW)H' = WH' + γG` (`G = Σ w g fᵀ`) with the
/// released residual `ρ = γG(1 − X̂H')` (`prox_chart_residual`, summed over the window's returns),
/// `‖ρ‖∞ ≤ ‖γG‖∞ δ` (`prox_chart_certificate`). The map differs from the exact prox step's by
/// `−ρH'⁻¹`, so a read at an operand `x` moves by `|ρ_i H'⁻¹ x| ≤ ‖ρ_i‖₂‖x‖₂/λ_min(H') ≤
/// ‖ρ‖∞‖x‖₁/c`, with `c = 1 − 1/(2L_R)` the carried Gram's margin (`carried_gram_posDef_rule`).
/// One return of a unit-scale covector (`‖wγg‖∞ ≤ 1`, the lattice rule's assumption) and a feature
/// `‖f‖₁ ≤ X_ℓ` read at an operand `‖x‖₁ ≤ X_ℓ` therefore moves by at most `X_ℓ²δ/c`; the lattice
/// rule's `2L_R X_ℓ ≤ 2^(L_ℓ)` makes that at most `2^(2L_ℓ)δ/(2L_R(2L_R − 1)) ≤ 1/(4L_R)` at
/// `δ ≤ δ_ℓ`: the chart's release moves a read by no more than a carried remainder does
/// (`remainder_below_grain`), below the receiver's grain. Each deposit reports the bound its own
/// returns reach ([`ChartReading::read`]), so the unit-scale assumption is measured, as the lattice
/// rule's is.
///
/// **Why the lattice.** A rounded refinement adds to the certificate the chart's rounding
/// `‖ΔH'‖∞ ≤ n·2^(−L_s)/2·‖H'‖∞` (`rounded_refinement_certificate_left`) and the residual's rounding at
/// the chart's lattice, `‖(R̃ − R)X̂H'‖∞ ≤ n·2^(−L_s)/2·(1 + δ)`; together at most
/// `2n·2^(−L_s)‖H'‖∞ ≤ δ_ℓ/2`, so from any certificate at most `δ_ℓ` every rounded refinement stays
/// at most `δ_ℓ` (`roundedIter_certificate` at `c = δ_ℓ ≤ 1/2`), and from above it the certificates
/// fall to the fixed point near `δ_ℓ/2`. The Gram's own norm is read at each deposit, as the clock's
/// Elias-gamma length is: the lattice refines as the Gram grows, and never coarsens (a coarser chart
/// is a finer one's lattice point). Brandon may override the rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartRule {
    lattice: Lattice,
    grain: u128,
}

impl ChartRule {
    /// At a locus's carrier lattice and the finest admitted receiver grain `L_R ≥ 1`.
    pub fn new(lattice: Lattice, grain: u128) -> Self {
        Self {
            lattice,
            grain: grain.max(1),
        }
    }

    /// `L_ℓ`'s lattice.
    pub fn lattice(&self) -> Lattice {
        self.lattice
    }

    /// `L_R`.
    pub fn grain(&self) -> u128 {
        self.grain
    }

    /// `D_ℓ = 2L_ℓ + 1 − ⌊log₂ L_R⌋` (at least 1).
    pub fn target_exponent(&self) -> u32 {
        (2 * self.lattice.exponent() + 1)
            .saturating_sub(self.grain.ilog2())
            .max(1)
    }

    /// `δ_ℓ = 2^(−D_ℓ)`.
    pub fn target(&self) -> Rat {
        Lattice::new(self.target_exponent()).unit()
    }

    /// `L_s = D_ℓ + ⌈log₂ n⌉ + ⌈log₂ ‖H'‖∞⌉ + 2` for a Gram of width `n` whose norm has
    /// `⌈log₂ ‖H'‖∞⌉ = norm`.
    pub fn exponent(&self, width: usize, norm: u32) -> u32 {
        self.target_exponent() + ceil_log2(width as u128) + norm + 2
    }

    /// **The most a released prox residual of norm `‖ρ‖∞ ≤ released` moves a read** at an operand
    /// of ℓ1 norm `X_ℓ ≤ 2^(L_ℓ)/(2L_R)`: `released · X_ℓ/c ≤ released · 2^(L_ℓ)/(2L_R − 1)`.
    pub fn read(&self, released: &Rat) -> Rat {
        released * Rat::new(self.lattice.scale(), BigInt::from(2 * self.grain - 1))
    }

    /// **The refinements one phase may take**: from the scaled identity `2^(−a)I`,
    /// `a = ⌈log₂ ‖H'‖∞⌉`, the residual `1 − 2^(−a)H'` has spectrum in `[0, 1 − 2^(−a)c]`, and
    /// `k` refinements raise it to the `2^k`-th power (`newton_schulz_iter_left`); its row
    /// certificate is at most `√n` times its spectral radius, so
    /// `a + ⌈log₂(D_ℓ + ⌈log₂ n⌉ + 2)⌉ + 4` refinements reach `δ_ℓ` with the rounding's margin.
    fn refinements(&self, width: usize, norm: u32) -> u32 {
        let depth = u128::from(self.target_exponent() + ceil_log2(width as u128) + 2);
        norm + ceil_log2(depth) + 4
    }
}

/// [definition; agent-inferred] **The solved chart** `X̂ ≈ H⁻¹` of a normal law's carried Gram
/// (Decision 24; Lean `HNN/LatticeWord`): a symmetric lattice matrix on `2^(−L_s)ℤ` with its certified
/// left residual `δ = ‖1 − X̂H‖∞`, computed exactly. The Gram is the identity off its **support**
/// (the rows where a deposit moved it: `H = I + Σ w f fᵀ` moves only rows some feature reached), and
/// so is the chart; the chart is carried on the support as integer coordinates (`i128`, with the
/// carrier refused past it), and every product it takes is an integer product. The founding chart is
/// exact: `H_0 = I`, `X̂ = I`, `δ = 0`.
///
/// A deposit ([`SolvedChart::deposited`]) moves the Gram to `H' = H + Σ w f fᵀ` (carried) and the
/// chart in three stages, each on the successor's lattice:
///
/// ```text
/// warm start   X₀ = X̂ − X̂F(Ω⁻¹ + FᵀX̂F)⁻¹FᵀX̂      the window's returns F, Ω = diag(w), one rank-one step each, rounded
///              1 − X₀(H + FΩFᵀ) = (1 − X̂FS⁻¹Fᵀ)(1 − X̂H)                                              (exact identity)
/// certificate  δ = ‖1 − X₀H'‖∞                      exact, from integer products
/// refinement   X ← round((2 − XH')X) = round(X + R X) ,  R = 1 − XH'     until δ ≤ δ_ℓ ;  1 − X'H' = R² − (rounding)H'
/// ```
///
/// [agent-inferred] The previous chart alone is not a warm start: after a deposit it has residual
/// `(1 − X̂H) − X̂ΔH` (`warm_start_residual`), whose certificate `δ + ‖ΔH‖∞‖X̂‖∞`
/// (`warm_start_certificate`) passes 1 whenever a return's feature is large (`‖f fᵀ‖∞` up to
/// `X_ℓ²`), and the exact residual `−H⁻¹ΔH` then has spectral radius above 1, where Newton–Schulz
/// diverges. The window's rank-one steps (Sherman–Morrison, read at the chart's lattice) carry the
/// residual instead: with `S = Ω⁻¹ + FᵀX̂F` the identity above holds in any ring (it expands to
/// `X̂F[Ω − S⁻¹(Ω⁻¹ + FᵀX̂F)Ω]Fᵀ = 0`), so an exact chart stays exact and a certified one keeps its
/// residual up to `1 − X̂FS⁻¹Fᵀ` (near `H'⁻¹H`). The Lean statement of that identity is owed in #62
/// ("Step 4 (#73) owed"); nothing rests on it, since the certificate is computed exactly afterwards.
/// When the warm start's certificate is not below 1, or a refinement does not lower it, the chart
/// restarts from the scaled identity `2^(−a)I`, whose residual is contracting (spectrum in `[0, 1)`).
/// A refinement that does not reach `δ_ℓ` within the rule's count is refused. Sherman–Morrison and the
/// exact inversion are retired as solves: the rank-one steps are only the warm start.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolvedChart {
    /// `L_s`: every entry lies on `2^(−L_s)ℤ`.
    exponent: u32,
    /// The Gram's support `S`, ascending; off it the chart is the identity.
    support: Vec<usize>,
    /// The chart on `S × S` as integer coordinates at `2^(−L_s)`, row-major and symmetric.
    block: Vec<i128>,
    /// `δ = ‖1 − X̂H‖∞`, exact.
    certificate: Rat,
}

/// What one deposit's refinement of a chart read: the warm start's certificate (`None` when it left
/// the `i128` carrier), the refinements taken, whether it restarted from the scaled identity, and the
/// bits of the certified residual `1 − X̂H'` (its nonzero entries, reduced).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Refinement {
    warm: Option<Rat>,
    refinements: u32,
    cold: bool,
    residual_bits: u64,
}

/// A carried Gram read on its support: the support, the finest dyadic exponent `e_H` of its entries
/// there, their integer coordinates at `2^(−e_H)` (row-major), and `⌈log₂ ‖H‖∞⌉` (0 at most 1).
struct GramBlock {
    support: Vec<usize>,
    exponent: u32,
    coordinates: Vec<i128>,
    norm: u32,
}

impl GramBlock {
    /// Read a carried Gram (every entry on a dyadic lattice), refusing a coordinate past `i128` and an
    /// entry off every dyadic lattice (a Gram that is not carried has no chart).
    fn of(gram: &[Vec<Rat>]) -> Result<Self, HnnError> {
        let support: Vec<usize> = (0..gram.len())
            .filter(|&i| {
                gram[i].iter().enumerate().any(
                    |(j, x)| {
                        if i == j { !x.is_one() } else { !x.is_zero() }
                    },
                )
            })
            .collect();
        let s = support.len();
        let mut exponent = 0u32;
        for &i in &support {
            for &j in &support {
                let denominator = gram[i][j].denom();
                let twos = denominator.trailing_zeros().unwrap_or(0);
                if denominator.bits() != twos + 1 {
                    return Err(ExactLinearError::InverseCertificateFailure.into());
                }
                exponent = exponent.max(twos as u32);
            }
        }
        let overflow = || HnnError::from(ExactLinearError::ExtentOverflow);
        let mut coordinates = Vec::with_capacity(s * s);
        let mut widest = 1u128 << exponent;
        for &i in &support {
            let mut row = 0u128;
            for &j in &support {
                let value = &gram[i][j];
                let twos = value.denom().trailing_zeros().unwrap_or(0) as u32;
                let coordinate = (value.numer() << (exponent - twos) as usize)
                    .to_i128()
                    .ok_or_else(overflow)?;
                row = row
                    .checked_add(coordinate.unsigned_abs())
                    .ok_or_else(overflow)?;
                coordinates.push(coordinate);
            }
            widest = widest.max(row);
        }
        let norm = ceil_log2(widest).saturating_sub(exponent);
        Ok(Self {
            support,
            exponent,
            coordinates,
            norm,
        })
    }
}

/// One row of an integer product, exact: in the `i128` carrier while every partial sum fits it,
/// otherwise in bounded-bit integers (the row's bits are at most the operands' plus `⌈log₂ s⌉`).
enum ProductRow {
    Narrow(Vec<i128>),
    Wide(Vec<BigInt>),
}

impl ProductRow {
    /// Row `row · B` of an `s × s` row-major `B`.
    fn of(row: &[i128], matrix: &[i128], s: usize) -> Self {
        let mut sums = vec![0i128; s];
        let narrow = 'narrow: {
            for (k, &left) in row.iter().enumerate() {
                if left == 0 {
                    continue;
                }
                for (sum, &right) in sums.iter_mut().zip(&matrix[k * s..(k + 1) * s]) {
                    match left
                        .checked_mul(right)
                        .and_then(|term| sum.checked_add(term))
                    {
                        Some(value) => *sum = value,
                        None => break 'narrow false,
                    }
                }
            }
            true
        };
        if narrow {
            return ProductRow::Narrow(sums);
        }
        let mut sums = vec![BigInt::zero(); s];
        for (k, &left) in row.iter().enumerate() {
            if left == 0 {
                continue;
            }
            let left = BigInt::from(left);
            for (sum, &right) in sums.iter_mut().zip(&matrix[k * s..(k + 1) * s]) {
                if right != 0 {
                    *sum += &left * right;
                }
            }
        }
        ProductRow::Wide(sums)
    }

    /// Entry `j` with `offset − entry` taken, in the `i128` carrier or `None`.
    fn subtracted_from(&self, j: usize, offset: i128) -> Option<i128> {
        match self {
            ProductRow::Narrow(sums) => offset.checked_sub(sums[j]),
            ProductRow::Wide(sums) => (BigInt::from(offset) - &sums[j]).to_i128(),
        }
    }

    /// Entry `j` at the nearest point of `2^(−k)` coarser, ties upward, in the `i128` carrier or
    /// `None`.
    fn nearest(&self, j: usize, k: u32) -> Option<i128> {
        match self {
            ProductRow::Narrow(sums) => nearest_shift(sums[j], k),
            ProductRow::Wide(sums) => nearest_shift_wide(&sums[j], k).to_i128(),
        }
    }
}

/// `x·2^(−k)` at its nearest integer, ties upward (Lean `quot` at a coordinate).
fn nearest_shift(x: i128, k: u32) -> Option<i128> {
    if k == 0 {
        return Some(x);
    }
    x.checked_add(1i128 << (k - 1)).map(|y| y >> k)
}

/// `x·2^(−k)` at its nearest integer, ties upward, in bounded-bit integers.
fn nearest_shift_wide(x: &BigInt, k: u32) -> BigInt {
    if k == 0 {
        return x.clone();
    }
    (x + (BigInt::one() << (k - 1) as usize)) >> k as usize
}

/// `numerator / denominator` at its nearest integer, ties upward (`denominator > 0`).
fn nearest_quotient(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let top: BigInt = (numerator << 1usize) + denominator;
    let bottom: BigInt = denominator << 1usize;
    let (mut quotient, residue) = (&top / &bottom, &top % &bottom);
    if residue.is_negative() {
        quotient -= 1;
    }
    quotient
}

/// A symmetric `s × s` block from its upper-triangle rows (row `i` holds columns `i..s`).
fn mirrored(s: usize, upper: Vec<Vec<i128>>) -> Vec<i128> {
    let mut block = vec![0i128; s * s];
    for (i, row) in upper.into_iter().enumerate() {
        for (offset, value) in row.into_iter().enumerate() {
            let j = i + offset;
            block[i * s + j] = value;
            block[j * s + i] = value;
        }
    }
    block
}

/// **The certified residual** of a chart block `X` (at `2^(−L_s)`) against a Gram block `H` (at
/// `2^(−e_H)`): `P = 2^(L_s + e_H)(1 − XH)` exactly, with `δ = max_i Σ_j |P_ij| · 2^(−L_s − e_H)`
/// (Lean `rowNorm`). Each row reads only the shared blocks and writes only its own: the rows run
/// together. `None` when an entry leaves the `i128` carrier.
fn certified(block: &[i128], gram: &[i128], s: usize, shift: u32) -> Option<(Vec<i128>, Rat)> {
    let one = 1i128 << shift;
    let rows: Vec<Option<(Vec<i128>, u128)>> = (0..s)
        .into_par_iter()
        .map(|i| {
            let product = ProductRow::of(&block[i * s..(i + 1) * s], gram, s);
            let mut row = Vec::with_capacity(s);
            let mut sum = 0u128;
            for j in 0..s {
                let value = product.subtracted_from(j, if i == j { one } else { 0 })?;
                sum = sum.checked_add(value.unsigned_abs())?;
                row.push(value);
            }
            Some((row, sum))
        })
        .collect();
    let mut residual = Vec::with_capacity(s * s);
    let mut widest = 0u128;
    for row in rows {
        let (row, sum) = row?;
        widest = widest.max(sum);
        residual.extend(row);
    }
    Some((
        residual,
        Rat::new(BigInt::from(widest), BigInt::one() << shift as usize),
    ))
}

/// **One rounded Newton–Schulz refinement, left form** (Lean `nsStep`, `newton_schulz_left`,
/// `rounded_refinement_certificate_left`): `X' = round(X + R̃X)` on `2^(−L_s)ℤ`, with `R̃` the certified
/// residual `P·2^(−L_s−e_H)` read at the chart's lattice. `X + RX = (2 − XH)X` is symmetric for a
/// symmetric `X` and `H`, so the upper triangle is formed and mirrored. The rows run together. `None`
/// when an entry leaves the `i128` carrier.
fn refined(
    block: &[i128],
    residual: &[i128],
    s: usize,
    gram_exponent: u32,
    exponent: u32,
) -> Option<Vec<i128>> {
    let rounded: Vec<i128> = residual
        .iter()
        .map(|&p| nearest_shift(p, gram_exponent))
        .collect::<Option<_>>()?;
    let upper: Vec<Option<Vec<i128>>> = (0..s)
        .into_par_iter()
        .map(|i| {
            let product = ProductRow::of(&rounded[i * s..(i + 1) * s], block, s);
            (i..s)
                .map(|j| block[i * s + j].checked_add(product.nearest(j, exponent)?))
                .collect()
        })
        .collect();
    Some(mirrored(s, upper.into_iter().collect::<Option<_>>()?))
}

/// **The warm start's rank-one steps** at the chart's lattice (Sherman–Morrison): for each return
/// `(w, f)`, with `f̃` the feature at `2^(−L_s)` and `v = X̂f̃` rounded there,
/// `X̂ ← X̂ − w v vᵀ/(1 + w f̃ᵀv)`, each entry at its nearest lattice point (upper triangle, mirrored).
/// A step whose denominator is not positive is skipped (the certificate then decides). The rows of
/// each step run together.
fn corrected(
    mut block: Vec<i128>,
    s: usize,
    exponent: u32,
    features: &[(&Rat, Vec<BigInt>)],
) -> Result<Vec<i128>, HnnError> {
    let overflow = || HnnError::from(ExactLinearError::ExtentOverflow);
    let shift = exponent as usize;
    for (weight, feature) in features {
        let reach: Vec<BigInt> = (0..s)
            .into_par_iter()
            .map(|i| {
                let mut sum = BigInt::zero();
                for (k, value) in feature.iter().enumerate() {
                    let c = block[i * s + k];
                    if c != 0 && !value.is_zero() {
                        sum += value * c;
                    }
                }
                nearest_shift_wide(&sum, exponent)
            })
            .collect();
        let energy: BigInt = feature.iter().zip(&reach).map(|(f, v)| f * v).sum();
        let denominator: BigInt = (weight.denom() << (2 * shift)) + weight.numer() * &energy;
        if !denominator.is_positive() {
            continue;
        }
        let scaled: Vec<BigInt> = reach
            .iter()
            .map(|v| (weight.numer() * v) << shift)
            .collect();
        let current = &block;
        let upper: Vec<Result<Vec<i128>, HnnError>> = (0..s)
            .into_par_iter()
            .map(|i| {
                (i..s)
                    .map(|j| {
                        let step = nearest_quotient(&(&scaled[i] * &reach[j]), &denominator)
                            .to_i128()
                            .ok_or_else(overflow)?;
                        current[i * s + j].checked_sub(step).ok_or_else(overflow)
                    })
                    .collect()
            })
            .collect();
        block = mirrored(s, upper.into_iter().collect::<Result<_, _>>()?);
    }
    Ok(block)
}

/// The bits of a residual's nonzero entries `P·2^(−shift)`, each as a reduced ratio.
fn residual_bits(residual: &[i128], shift: u32) -> u64 {
    residual
        .iter()
        .filter(|p| **p != 0)
        .map(|&p| lattice_bits(p, shift))
        .sum()
}

/// The bits of the lattice value `c·2^(−L)` as a reduced ratio (numerator and denominator), as
/// [`bits`] counts it.
fn lattice_bits(c: i128, exponent: u32) -> u64 {
    if c == 0 {
        return 1;
    }
    let twos = c.trailing_zeros().min(exponent);
    let magnitude = c.unsigned_abs() >> twos;
    u64::from(128 - magnitude.leading_zeros()) + u64::from(exponent - twos + 1)
}

impl SolvedChart {
    /// **The founding chart**: `H_0 = I`, so `X̂ = I` exactly, `δ = 0`.
    pub fn identity() -> Self {
        Self {
            exponent: 0,
            support: Vec::new(),
            block: Vec::new(),
            certificate: Rat::zero(),
        }
    }

    /// `L_s`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// `δ = ‖1 − X̂H‖∞`, exact.
    pub fn certificate(&self) -> &Rat {
        &self.certificate
    }

    /// The Gram's support the chart is carried on.
    pub fn support(&self) -> &[usize] {
        &self.support
    }

    /// The chart as rows of width `n`.
    pub fn dense(&self, n: usize) -> Vec<Vec<Rat>> {
        let mut rows: Vec<Vec<Rat>> = (0..n).map(|i| unit(n, i)).collect();
        let (s, scale) = (self.support.len(), BigInt::one() << self.exponent as usize);
        for (a, &i) in self.support.iter().enumerate() {
            for (b, &j) in self.support.iter().enumerate() {
                rows[i][j] = Rat::new(BigInt::from(self.block[a * s + b]), scale.clone());
            }
        }
        rows
    }

    /// Its bits at its lattice as a matrix of width `n`, each entry a reduced ratio as [`bits`]
    /// counts the other carriers (off the support: `1` on the diagonal, `0` elsewhere), with the
    /// certificate's.
    fn bits(&self, n: usize) -> u64 {
        let s = self.support.len();
        let outside = (n * n - s * s) as u64 + (n - s) as u64;
        let block: u64 = self
            .block
            .iter()
            .map(|&c| lattice_bits(c, self.exponent))
            .sum();
        outside + block + bits(&self.certificate)
    }

    /// **The reach `X̂f`** of a feature in the integral chart (`F / d`), in the integral chart
    /// (`over d·2^(L_s)`): the identity off the support.
    fn reach(&self, (values, denominator): &Chart) -> Chart {
        let shift = self.exponent as usize;
        let mut reach: Vec<BigInt> = values.iter().map(|value| value << shift).collect();
        let s = self.support.len();
        for (a, &i) in self.support.iter().enumerate() {
            let mut sum = BigInt::zero();
            for (b, &k) in self.support.iter().enumerate() {
                let c = self.block[a * s + b];
                if c != 0 && !values[k].is_zero() {
                    sum += &values[k] * c;
                }
            }
            reach[i] = sum;
        }
        (reach, denominator << shift)
    }

    /// The chart carried onto another support at a lattice at least as fine: an entry both
    /// supports hold moves by `2^(L − L_s)` exactly, and an index the chart did not hold enters as the
    /// identity's.
    fn carried_to(&self, support: &[usize], exponent: u32) -> Result<Vec<i128>, HnnError> {
        let s = support.len();
        // Every chart and the rule's lattice lie within the residual's shift, so the move fits.
        let shift = exponent - self.exponent;
        if exponent > RESIDUAL_SHIFT {
            return Err(ExactLinearError::ExtentOverflow.into());
        }
        let scale = 1i128 << shift;
        let held: BTreeMap<usize, usize> = self
            .support
            .iter()
            .enumerate()
            .map(|(a, &i)| (i, a))
            .collect();
        let width = self.support.len();
        let mut block = vec![0i128; s * s];
        for (a, i) in support.iter().enumerate() {
            for (b, j) in support.iter().enumerate() {
                let value = match (held.get(i), held.get(j)) {
                    (Some(&p), Some(&q)) => self.block[p * width + q],
                    _ if a == b => 1i128 << self.exponent,
                    _ => 0,
                };
                block[a * s + b] = value
                    .checked_mul(scale)
                    .ok_or(ExactLinearError::ExtentOverflow)?;
            }
        }
        Ok(block)
    }

    /// **The successor's chart** (the type's header): the Gram `gram` is the carried successor, and
    /// `features` the window's returns `(w, f)` in the integral chart. Refused past the `i128` carrier
    /// or when the refinement does not reach `δ_ℓ` within the rule's count.
    fn deposited(
        &self,
        gram: &[Vec<Rat>],
        features: &[(&Rat, &Chart)],
        rule: &ChartRule,
    ) -> Result<(Self, Refinement), HnnError> {
        let n = gram.len();
        let carried = GramBlock::of(gram)?;
        let s = carried.support.len();
        let exponent = rule.exponent(n, carried.norm).max(self.exponent);
        let shift = exponent + carried.exponent;
        if shift > RESIDUAL_SHIFT {
            return Err(ExactLinearError::ExtentOverflow.into());
        }
        if s == 0 {
            let chart = Self {
                exponent,
                ..Self::identity()
            };
            let refinement = Refinement {
                warm: Some(Rat::zero()),
                refinements: 0,
                cold: false,
                residual_bits: 0,
            };
            return Ok((chart, refinement));
        }
        // The returns on the support at the chart's lattice.
        let features: Vec<(&Rat, Vec<BigInt>)> = features
            .iter()
            .map(|(weight, (values, denominator))| {
                let feature = carried
                    .support
                    .iter()
                    .map(|&k| {
                        let value = &values[k] << exponent as usize;
                        if denominator.is_one() {
                            value
                        } else {
                            nearest_quotient(&value, denominator)
                        }
                    })
                    .collect();
                (*weight, feature)
            })
            .collect();
        let target = rule.target();
        let warm = corrected(
            self.carried_to(&carried.support, exponent)?,
            s,
            exponent,
            &features,
        )?;
        let mut residual = certified(&warm, &carried.coordinates, s, shift);
        let certificate = residual.as_ref().map(|(_, delta)| delta.clone());
        let mut block = warm;
        let limit = rule.refinements(n, carried.norm);
        let (mut refinements, mut phase, mut cold, mut stalled) = (0u32, 0u32, false, false);
        loop {
            if let Some((_, delta)) = &residual
                && *delta <= target
            {
                break;
            }
            let contracting = residual
                .as_ref()
                .is_some_and(|(_, delta)| *delta < Rat::one());
            if !cold && (!contracting || stalled || phase >= limit) {
                // The scaled identity 2^(−a)I: its residual 1 − 2^(−a)H' is contracting.
                cold = true;
                phase = 0;
                block = vec![0i128; s * s];
                for a in 0..s {
                    block[a * s + a] = 1i128 << (exponent - carried.norm);
                }
                residual = certified(&block, &carried.coordinates, s, shift);
                continue;
            }
            let failure = || HnnError::from(ExactLinearError::InverseCertificateFailure);
            if phase >= limit {
                return Err(failure());
            }
            let (p, delta) = residual.as_ref().ok_or_else(failure)?;
            let Some(next) = refined(&block, p, s, carried.exponent, exponent) else {
                // A warm refinement that leaves the carrier restarts; a cold one is refused.
                if cold {
                    return Err(failure());
                }
                stalled = true;
                continue;
            };
            let next_residual = certified(&next, &carried.coordinates, s, shift);
            stalled = next_residual
                .as_ref()
                .is_none_or(|(_, next_delta)| next_delta >= delta);
            block = next;
            residual = next_residual;
            refinements += 1;
            phase += 1;
        }
        let (p, delta) = residual.expect("certified above");
        let chart = Self {
            exponent,
            support: carried.support,
            block,
            certificate: delta,
        };
        let refinement = Refinement {
            warm: certificate,
            refinements,
            cold,
            residual_bits: residual_bits(&p, shift),
        };
        Ok((chart, refinement))
    }
}

/// **One rounded refinement of a dense chart** (a test fixture's reading of the certified residual
/// and the refinement): a symmetric chart on `2^(−exponent)ℤ` against a carried Gram, returning the
/// refined chart with the certificates before and after. `None` when the chart is off its lattice or
/// an entry leaves the `i128` carrier.
#[cfg(test)]
pub(crate) fn refined_once(
    chart: &[Vec<Rat>],
    exponent: u32,
    gram: &[Vec<Rat>],
) -> Option<(Vec<Vec<Rat>>, Rat, Rat)> {
    let carried = GramBlock::of(gram).ok()?;
    let s = carried.support.len();
    let scale = Rat::from_integer(BigInt::one() << exponent as usize);
    let mut block = Vec::with_capacity(s * s);
    for &i in &carried.support {
        for &j in &carried.support {
            let coordinate = &chart[i][j] * &scale;
            if !coordinate.is_integer() {
                return None;
            }
            block.push(coordinate.to_integer().to_i128()?);
        }
    }
    let shift = exponent + carried.exponent;
    let (residual, before) = certified(&block, &carried.coordinates, s, shift)?;
    let next = refined(&block, &residual, s, carried.exponent, exponent)?;
    let (_, after) = certified(&next, &carried.coordinates, s, shift)?;
    let chart = SolvedChart {
        exponent,
        support: carried.support,
        block: next,
        certificate: after.clone(),
    };
    Some((chart.dense(gram.len()), before, after))
}

/// [definition] **One normal law's solved chart at a deposit** (Decision 24; Lean
/// `HNN/LatticeWord.prox_chart_certificate`): the chart's lattice `L_s`, the declared target `δ_ℓ`,
/// the warm start's certificate (`None` when it left the `i128` carrier), the executed chart's
/// certificate `δ = ‖1 − X̂H'‖∞` (exact), the refinements taken and whether the chart restarted from
/// the scaled identity; the **released prox residual** `ρ = γ G (1 − X̂H')` by its certificate
/// `‖ρ‖∞ ≤ Σ_t |wγ| ‖g_t‖∞ ‖f_t‖₁ · δ` (exact; `prox_chart_certificate` per return, summed) and the most
/// it moves a read ([`ChartRule::read`]); and the bits of its factor `1 − X̂H'` (nonzero entries,
/// reduced), the part of `ρ` the deposit's own covectors do not already carry. The release is
/// reported, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReading {
    pub exponent: u32,
    pub target: Rat,
    pub warm: Option<Rat>,
    pub certificate: Rat,
    pub refinements: u32,
    pub cold: bool,
    pub released: Rat,
    pub read: Rat,
    pub residual_bits: u64,
}

// -------------------------------------------------------------------------------------------
// the normal law

/// [definition] **One observed return at a linear locus**: its weight `w`, its feature `f_t` and
/// its descent covector `g_t` (Lean `HNN/Normal.Sample`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sample {
    pub weight: Rat,
    pub feature: Vec<Rat>,
    pub covector: Vec<Rat>,
}

/// [definition] **One locus's deposition owner** (design (c), `NormalLaw`): the map `W` (`m × n`)
/// and its Gram `H` (`n × n`, the locus's own width), each on the locus's lattice with its carried
/// remainders, and the solved chart `X̂ ≈ H⁻¹` of the carried Gram on its own lattice with its
/// certified residual ([`SolvedChart`], Decision 24). `B = W H` is not carried (module header). Its
/// law is the prox step at the carried Gram through the executed chart (Lean
/// `HNN/Normal.normal_prox_step`, `HNN/LatticeWord.prox_chart_residual`: `W' = W + γ G X̂`, the prox
/// identity holding up to the released residual `γG(1 − X̂H')`) with the carried Gram within one unit
/// of the exact statistic since the locus's founding
/// (`HNN/LatticeDeposit.within_one_unit_since_founding`): `W` is the prox iterate, not the minimizer
/// of the accumulated objective `tr(WHWᵀ) − 2tr(WBᵀ) + C`, which `normalStatistic_standing` states for
/// an exact `(H, B)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalLaw {
    map: ExactRatMatrix,
    gram: Vec<Vec<Rat>>,
    chart: SolvedChart,
    map_carry: Carry,
    gram_carry: Carry,
}

impl NormalLaw {
    /// **The unit prior at a map**: `H_0 = I` (so `B_0 = W_0`), no remainder, and the founding chart
    /// `X̂ = I` exact (`δ = 0`).
    pub fn with_prior(map: ExactRatMatrix) -> Self {
        let n = map.columns();
        let identity: Vec<Vec<Rat>> = (0..n).map(|i| unit(n, i)).collect();
        Self {
            gram: identity,
            chart: SolvedChart::identity(),
            map,
            map_carry: Carry::default(),
            gram_carry: Carry::default(),
        }
    }

    /// `W`.
    pub fn map(&self) -> &ExactRatMatrix {
        &self.map
    }

    /// `H`, the carried Gram.
    pub fn gram(&self) -> ExactRatMatrix {
        rows_matrix(&self.gram)
    }

    /// `X̂ ≈ H⁻¹`, the solved chart of the carried Gram, dense: within `δ` of the inverse in its
    /// left residual, `‖1 − X̂H‖∞ = δ` ([`NormalLaw::chart`]).
    pub fn solved(&self) -> ExactRatMatrix {
        rows_matrix(&self.chart.dense(self.gram.len()))
    }

    /// The solved chart, with its lattice and certificate.
    pub fn chart(&self) -> &SolvedChart {
        &self.chart
    }

    /// `W`'s carried remainders, dense.
    pub fn map_remainder(&self) -> ExactRatMatrix {
        let (m, n) = (self.map.rows(), self.map.columns());
        rows_matrix(
            &(0..m)
                .map(|i| (0..n).map(|j| self.map_carry.at(i * n + j)).collect())
                .collect::<Vec<Vec<Rat>>>(),
        )
    }

    /// `H`'s carried remainders, dense.
    pub fn gram_remainder(&self) -> ExactRatMatrix {
        let n = self.gram.len();
        rows_matrix(
            &(0..n)
                .map(|i| (0..n).map(|j| self.gram_carry.at(i * n + j)).collect())
                .collect::<Vec<Vec<Rat>>>(),
        )
    }

    /// **The carried prox step through the solved chart** over a window's samples (Lean
    /// `HNN/Normal.normal_prox_step` at the carried operands, `HNN/LatticeDeposit.carry`,
    /// `HNN/LatticeWord.prox_chart_residual`): `ΔH = Σ w f fᵀ` carried onto `H` gives `H'`; the chart
    /// of `H'` follows from the previous chart ([`SolvedChart`]: the warm start, its exact
    /// certificate and the rounded refinements to `δ ≤ δ_ℓ` of the locus's [`ChartRule`]); then
    /// `ΔW = γ Σ w g (X̂f)ᵀ`, so `(W + ΔW)H' = WH' + γG − γG(1 − X̂H')` exactly, with `G = Σ w g fᵀ`;
    /// `ΔW` is carried onto `W`. Each carry is at the budgeted carry `at` of the locus's deposit (its
    /// residuals staged there). Returns the successor with its chart's reading, `None` when the
    /// window reached nothing (no nonzero weighted feature), which moves nothing.
    ///
    /// [definition; agent-inferred] **The sums are read in the integral chart**: each sample's
    /// feature and covector is charted once as integers over its least common denominator
    /// (`ratio::linear::vector::integral`), each reach `X̂f` is an integer product over the feature's
    /// denominator times `2^(L_s)`, each sum of rank-one terms is formed over integers and each entry
    /// normalized once (`ΔW` by `IntegralMatrix::outer_sum`, the symmetric `ΔH` on its upper triangle
    /// and mirrored). A reduced ratio is canonical, so every value equals the termwise rational sum's.
    /// The samples' exact bits (the word's receiving reads and the ratio's covectors, thousands of
    /// bits each) make the update's normalization, one per entry, the cost; its residual the carry
    /// releases exactly.
    pub fn deposited(
        &self,
        samples: &[Sample],
        proxy: &Rat,
        rule: &ChartRule,
        at: &mut BudgetedCarry,
    ) -> Result<(Self, Option<ChartReading>), HnnError> {
        let (m, n) = (self.map.rows(), self.map.columns());
        for sample in samples {
            if sample.feature.len() != n || sample.covector.len() != m {
                return Err(HnnError::Shape {
                    what: "a normal sample (feature, covector)",
                    expected: n + m,
                    found: sample.feature.len() + sample.covector.len(),
                });
            }
        }
        let active: Vec<(&Sample, Chart)> = samples
            .iter()
            .filter(|sample| !sample.weight.is_zero())
            .filter(|sample| sample.feature.iter().any(|x| !x.is_zero()))
            .map(|sample| (sample, integral(&sample.feature)))
            .collect();
        if active.is_empty() {
            return Ok((self.clone(), None));
        }
        let mut next = self.clone();
        // ΔH = Σ w f fᵀ, carried onto H.
        let gram_update = gram_sum(
            n,
            active
                .iter()
                .map(|(sample, feature)| (&sample.weight, feature)),
        );
        let mut gram: Vec<Rat> = self.gram.iter().flatten().cloned().collect();
        next.gram_carry
            .deposit_all(at, Carrier::Gram, &mut gram, &gram_update);
        next.gram = gram.chunks(n).map(<[Rat]>::to_vec).collect();
        // The chart of H', from the previous chart.
        let features: Vec<(&Rat, &Chart)> = active
            .iter()
            .map(|(sample, feature)| (&sample.weight, feature))
            .collect();
        let (chart, refinement) = self.chart.deposited(&next.gram, &features, rule)?;
        next.chart = chart;
        // ΔW = γ Σ w g (X̂f)ᵀ at the successor's chart, carried onto W. Each sample's term reads only
        // its own covector and reach: the samples run together. Each term's `|wγ| ‖g‖∞ ‖f‖₁` bounds its
        // share of the released prox residual.
        let moving: Vec<&(&Sample, Chart)> = active
            .iter()
            .filter(|(sample, _)| !sample.covector.iter().all(Zero::is_zero))
            .collect();
        let chart = &next.chart;
        let terms: Vec<(Rat, Chart, Chart, Rat)> = indexed(moving.len(), |t| {
            let (sample, feature) = moving[t];
            let weight = proxy * &sample.weight;
            let covector = integral(&sample.covector);
            let widest = covector
                .0
                .iter()
                .map(|x| x.magnitude())
                .max()
                .cloned()
                .unwrap_or_default();
            let mass: BigInt = feature
                .0
                .iter()
                .map(|x| BigInt::from(x.magnitude().clone()))
                .sum();
            let share = weight.abs()
                * Rat::new(BigInt::from(widest), covector.1.clone())
                * Rat::new(mass, feature.1.clone());
            Ok((weight, covector, chart.reach(feature), share))
        })?;
        let map_update: Vec<Rat> = outer_rows(
            m,
            n,
            &terms
                .iter()
                .map(|(weight, covector, reach, _)| (weight, covector, reach))
                .collect::<Vec<_>>(),
        )
        .into_iter()
        .flatten()
        .collect();
        let mut map = self.map.entries().to_vec();
        next.map_carry
            .deposit_all(at, Carrier::Map, &mut map, &map_update);
        next.map = flat_matrix(m, n, map)?;
        let released =
            next.chart.certificate() * terms.iter().map(|(.., share)| share).sum::<Rat>();
        let reading = ChartReading {
            exponent: next.chart.exponent(),
            target: rule.target(),
            warm: refinement.warm,
            certificate: next.chart.certificate().clone(),
            refinements: refinement.refinements,
            cold: refinement.cold,
            read: rule.read(&released),
            released,
            residual_bits: refinement.residual_bits,
        };
        Ok((next, Some(reading)))
    }

    /// Its bits by carrier.
    fn carrier_bits(&self) -> CarrierBits {
        CarrierBits {
            entries: self
                .map
                .entries()
                .iter()
                .chain(self.gram.iter().flatten())
                .map(bits)
                .sum(),
            remainders: self.map_carry.bits() + self.gram_carry.bits(),
            solved: self.chart.bits(self.gram.len()),
        }
    }

    /// Whether every entry of `W` and `H` lies on the lattice.
    fn on_lattice(&self, lattice: &Lattice) -> bool {
        self.map
            .entries()
            .iter()
            .chain(self.gram.iter().flatten())
            .all(|value| lattice.contains(value))
    }
}

/// **`Σ_t w_t f_t f_tᵀ` in the integral chart**: each feature charted once, the numerators summed
/// over integers on the terms' common denominator, and each entry of the upper triangle normalized
/// once; the form is symmetric, so the lower triangle is its mirror. Each row of the upper triangle
/// reads only the shared features and writes only its own entries: the rows run together
/// (`hnn::realization`).
fn gram_sum<'a>(n: usize, terms: impl IntoIterator<Item = (&'a Rat, &'a Chart)>) -> Vec<Rat> {
    let terms: Vec<(&Rat, &Chart, BigInt)> = terms
        .into_iter()
        .map(|(weight, feature)| (weight, feature, weight.denom() * &feature.1 * &feature.1))
        .collect();
    let denominator = terms
        .iter()
        .fold(BigInt::one(), |common, (.., scale)| lcm(&common, scale));
    let factors: Vec<BigInt> = terms
        .iter()
        .map(|(weight, _, scale)| weight.numer() * (&denominator / scale))
        .collect();
    let rows: Vec<Vec<Rat>> = (0..n)
        .into_par_iter()
        .map(|i| {
            let mut numerators = vec![BigInt::zero(); n - i];
            for ((_, (values, _), _), factor) in terms.iter().zip(&factors) {
                if values[i].is_zero() {
                    continue;
                }
                let left = &values[i] * factor;
                for j in i..n {
                    if !values[j].is_zero() {
                        numerators[j - i] += &left * &values[j];
                    }
                }
            }
            numerators
                .into_iter()
                .map(|numerator| {
                    if numerator.is_zero() {
                        Rat::zero()
                    } else {
                        Rat::new(numerator, denominator.clone())
                    }
                })
                .collect()
        })
        .collect();
    let mut entries = vec![Rat::zero(); n * n];
    for (i, row) in rows.into_iter().enumerate() {
        for (offset, value) in row.into_iter().enumerate() {
            let j = i + offset;
            if value.is_zero() {
                continue;
            }
            entries[j * n + i] = value.clone();
            entries[i * n + j] = value;
        }
    }
    entries
}

/// **The factor step's update `rate · g`**, the canonical product of two reduced ratios:
/// `(a/b)(c/d) = (a/g₁ · c/g₂) / (b/g₂ · d/g₁)` with `g₁ = gcd(a, d)`, `g₂ = gcd(c, b)`, the same
/// reduced value as `Ratio`'s product.
///
/// [definition; agent-inferred] The rate `η_x / h_x` is a small lattice ratio and the gradient
/// entry a large one (thousands of bits, from the pullback), so each cross `gcd` pairs a small
/// operand with a large one. It is read by Euclid's remainder first (`crate::ratio::gcd`), which
/// costs the large operand's size once; the binary `gcd` behind `Ratio`'s product halves the large
/// operand a bit at a time, paying its full size on every step. The value is `Ratio`'s (receipt:
/// the equality run of `hnn_lattice_growth`, which recomputes every factor update as `Ratio`'s
/// product, [`NormalLaw::deposited`]).
fn rate_times(rate: &Rat, value: &Rat) -> Rat {
    if rate.is_zero() || value.is_zero() {
        return Rat::zero();
    }
    let first = crate::ratio::gcd(rate.numer(), value.denom());
    let second = crate::ratio::gcd(value.numer(), rate.denom());
    Rat::new_raw(
        (rate.numer() / &first) * (value.numer() / &second),
        (rate.denom() / &second) * (value.denom() / &first),
    )
}

/// `rate · G` entry by entry ([`rate_times`]).
fn rate_matrix(rate: &Rat, matrix: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let entries: Vec<Rat> = matrix
        .entries()
        .iter()
        .map(|x| rate_times(rate, x))
        .collect();
    flat_matrix(matrix.rows(), matrix.columns(), entries)
}

fn rows_matrix(rows: &[Vec<Rat>]) -> ExactRatMatrix {
    let columns = rows.first().map_or(0, Vec::len);
    ExactRatMatrix::shaped(rows.len(), columns, rows.to_vec()).expect("rows of one width")
}

fn bits(value: &Rat) -> u64 {
    value.numer().bits() + value.denom().bits()
}

// -------------------------------------------------------------------------------------------
// the material

#[derive(Clone, Debug, PartialEq, Eq)]
struct RingMaterial {
    standing: Vec<Rat>,
    standing_scale: Rat,
    passive: ExactRatMatrix,
    passive_scale: Rat,
    contrast: NormalLaw,
    slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    slice_scale: Rat,
    source: Option<NormalLaw>,
    pairs: Vec<(usize, PairPort)>,
    pair_scale: Rat,
    receiving: Option<NormalLaw>,
    /// The receiving parametron's landmark tree (Decision 28), on a receiving ring.
    tree: Option<Landmarks>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ContactMaterial {
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    scales: [Rat; 3],
}

/// [definition] **A carried array of a locus**: an array whose entries live on the locus's
/// lattice with their carried remainders. `Map` and `Gram` are a normal law's `W` and `H` (the
/// contrast port's on an element, `E`'s on a source port, `R`'s on a receiving map); the others are
/// the factor families' entries and statistics `h_x`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Carrier {
    Map,
    Gram,
    Passive,
    PassiveScale,
    Slices,
    SliceScale,
    Standing,
    StandingScale,
    /// Family 0, 1, 2: the outputs `e`, the current reads `a`, the earlier reads `b`.
    Pair {
        offset: usize,
        family: usize,
    },
    PairScale,
    /// 0, 1, 2: the storage `c`, the stiffness `b`, the dissipation `F`.
    Factor(usize),
    FactorScale(usize),
}

type Carries = BTreeMap<(Locus, Carrier), Carry>;

/// `h_x' = h_x + Σ w|f|²`, carried on the family's lattice; the step's rate `η_x / h_x'`, refused
/// when the carried statistic is not positive.
fn advance(
    carries: &mut Carries,
    at: &mut BudgetedCarry,
    key: (Locus, Carrier),
    scale: &mut Rat,
    energy: &Rat,
    eta: &Rat,
) -> Result<Rat, HnnError> {
    carries
        .entry(key)
        .or_default()
        .deposit(at, key.1, 0, scale, energy);
    if !scale.is_positive() {
        return Err(HnnError::FactorStatistic {
            locus: key.0,
            statistic: scale.clone(),
        });
    }
    Ok(eta / &*scale)
}

/// Carry `rate · delta` onto a family of vectors, flat in row order.
fn carried_rows(
    carry: &mut Carry,
    at: &mut BudgetedCarry,
    carrier: Carrier,
    base: &[Vec<Rat>],
    delta: &[Vec<Rat>],
    rate: &Rat,
) -> Vec<Vec<Rat>> {
    let mut index = 0;
    base.iter()
        .zip(delta)
        .map(|(row, drow)| {
            let width = row.len();
            let mut row = row.clone();
            for (i, (x, dx)) in row.iter_mut().zip(drow).enumerate() {
                carry.deposit(at, carrier, index + i, x, &rate_times(rate, dx));
            }
            index += width;
            row
        })
        .collect()
}

/// [definition] **A linear locus** that a deposit's normal law updates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LinearLocus {
    /// `E_g`: feature the phase-binned counts `M_g[c]`, covector `P^(c−τ)` of the open's covector.
    SourcePort(usize),
    /// `W_c,g`: feature the contrast `c_t`, covector the element adjoint's `u_t`.
    Contrast(usize),
    /// `R` on ring `g`: feature the rotated anchor, covector the logit covector.
    Receiving(usize),
}

impl LinearLocus {
    pub fn locus(&self) -> Locus {
        match *self {
            LinearLocus::SourcePort(g) => Locus::SourcePort(g),
            LinearLocus::Contrast(g) => Locus::Element(g),
            LinearLocus::Receiving(g) => Locus::ReceivingMap(g),
        }
    }
}

/// [definition] **One linear locus's window**: its samples inside the causal diamond.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearStep {
    pub locus: LinearLocus,
    pub samples: Vec<Sample>,
}

/// [definition] **One reached comparison's deposit into the receiving parametron's landmark tree**
/// (Decision 28): its receiving ring, the causal address its phase read the tree at
/// (`hnn::receiving::ActiveAddress::phase`) and its target class. The deposit applies a window's
/// steps in cell order, each on the paths its address opens (Lean
/// `HNN/LandmarkTree.landmark_step`), at the receiving locus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkStep {
    pub ring: usize,
    pub address: Vec<Letter>,
    pub class: usize,
}

/// [definition] **A factor family's descent direction `G_x`** (the negative gradient of the ratio's
/// log), shaped as the family's factors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactorGradient {
    /// The passive factor `f_g` (`W_s = −f fᵀ`).
    Passive {
        ring: usize,
        gradient: ExactRatMatrix,
    },
    /// The slices' `(u_ρ, v_ρ)`.
    Slices {
        ring: usize,
        gradient: Vec<(Vec<Rat>, Vec<Rat>)>,
    },
    /// The standing `q_g`, through the declared lock chart (the class covector carried by the
    /// transpose of the contrast map `q ↦ Δ`).
    Standing { ring: usize, gradient: Vec<Rat> },
    /// The pair port's outputs `e_ρ`, current reads `a_ρ` and earlier reads `b_ρ`.
    PairPort {
        ring: usize,
        offset: usize,
        outputs: Vec<Vec<Rat>>,
        current: Vec<Vec<Rat>>,
        earlier: Vec<Vec<Rat>>,
    },
    /// `c_a` (`C_a = c cᵀ`).
    Storage {
        contact: usize,
        gradient: ExactRatMatrix,
    },
    /// `b_a` (`K_a = b bᵀ`).
    Stiffness {
        contact: usize,
        gradient: ExactRatMatrix,
    },
    /// `F_a` (`D_a = F Fᵀ`).
    Dissipation {
        contact: usize,
        gradient: ExactRatMatrix,
    },
}

impl FactorGradient {
    /// Every entry of the descent direction, in the family's carry order.
    pub fn entries(&self) -> Box<dyn Iterator<Item = &Rat> + '_> {
        match self {
            FactorGradient::Passive { gradient, .. }
            | FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. } => Box::new(gradient.entries().iter()),
            FactorGradient::Slices { gradient, .. } => {
                Box::new(gradient.iter().flat_map(|(u, v)| u.iter().chain(v)))
            }
            FactorGradient::Standing { gradient, .. } => Box::new(gradient.iter()),
            FactorGradient::PairPort {
                outputs,
                current,
                earlier,
                ..
            } => Box::new(outputs.iter().chain(current).chain(earlier).flatten()),
        }
    }

    pub fn locus(&self) -> Locus {
        match *self {
            FactorGradient::Passive { ring, .. } | FactorGradient::Slices { ring, .. } => {
                Locus::Element(ring)
            }
            FactorGradient::Standing { ring, .. } => Locus::Standing(ring),
            FactorGradient::PairPort { ring, .. } => Locus::SourcePort(ring),
            FactorGradient::Storage { contact, .. }
            | FactorGradient::Stiffness { contact, .. }
            | FactorGradient::Dissipation { contact, .. } => Locus::Channel(contact),
        }
    }
}

/// [definition] **One factor step**: the family's descent direction and the feature energy
/// `Σ_t w|f_t|²` its window adds to the family's statistic `h_x`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorStep {
    pub gradient: FactorGradient,
    pub energy: Rat,
}

/// [definition] **What a deposit's publication reads**: the energy-growth bound `ε_k` certified
/// for the storage forms (`Q_(k+1) ⪯ (1 + ε_k) Q_k`, zero when only reaction material moved, `None`
/// when no dyadic bound up to `2^40` certifies it), the running product `∏(1 + ε_k)`, the commit
/// reached, the successor's exact bits against the budget, the loci reached, and the budgeted
/// carry's report: every residual the deposit released (exact and sparse, with its locus, carrier
/// and entry; Lean `HNN/LatticeDeposit.release`), their bits, and the number of entries whose
/// lattice coordinate moved (`q ≠ 0`, review R5); and each normal law's solved chart with the prox
/// residual its chart released ([`ChartReading`], Decision 24); and the cells its reached
/// comparisons deposited into the receiving parametrons' landmark trees (Decision 28). The release
/// is reported, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositReading {
    pub growth: Option<Rat>,
    pub product: Rat,
    pub commit: u64,
    pub bits: u64,
    pub budget: u64,
    pub loci: Vec<Locus>,
    pub released: Vec<(Locus, Carrier, usize, Rat)>,
    pub released_bits: u64,
    pub stepped: u64,
    pub charts: Vec<(Locus, ChartReading)>,
    pub landmarks: u64,
}

// -------------------------------------------------------------------------------------------
// the constitution

/// [definition] **The constitution `Θ`**, the one owner. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constitution {
    rings: Vec<RingMaterial>,
    contacts: Vec<ContactMaterial>,
    steps: Steps,
    budget: u64,
    commit: u64,
    released: BTreeSet<Locus>,
    bound: CommittedEnergyBound,
    /// The declared lattice of every learned locus (the field's).
    lattices: BTreeMap<Locus, Lattice>,
    /// The factor families' carried remainders (the normal laws carry their own).
    carries: Carries,
    /// Each locus's deposit clock: the deposits that reached it with a nonzero update since its
    /// founding.
    clocks: BTreeMap<Locus, u64>,
    /// `L_R`, the finest admitted receiver grain (the field's), which the chart rule reads.
    grain: u128,
}

/// SplitMix64's finalizer after one golden-gamma step.
fn splitmix(state: u64) -> u64 {
    let mut z = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// **The declared sign generator** (design (d), campaign 1's declared values): entry `(i, j)` of
/// locus `ℓ` is `+1` when the low bit of `SplitMix64` over `(0, ℓ, i, j)` is set, `−1` otherwise,
/// the tuple folded as `z ← splitmix(z ⊕ x)` from `z = splitmix(0)`.
pub fn declared_sign(locus: u64, i: u64, j: u64) -> Rat {
    let mut z = splitmix(0);
    for x in [locus, i, j] {
        z = splitmix(z ^ x);
    }
    if z & 1 == 1 { Rat::one() } else { -Rat::one() }
}

/// The locus codes of the sign generator: `kind · 2^40 + index · 2^20 + part`.
fn locus_code(kind: u64, index: usize, part: usize) -> u64 {
    (kind << 40) + ((index as u64) << 20) + part as u64
}

fn scaled_identity(n: usize, value: Rat) -> ExactRatMatrix {
    ExactRatMatrix::identity(n)
        .expect("a positive extent")
        .scaled(&value)
}

fn unit(n: usize, i: usize) -> Vec<Rat> {
    (0..n)
        .map(|j| if i == j { Rat::one() } else { Rat::zero() })
        .collect()
}

impl Constitution {
    /// **Campaign 1's initial constitution and its priors** (design (d), R3 D2):
    ///
    /// | Locus | Initial value | Update |
    /// |---|---|---|
    /// | `E_g` on a source ring | the sign generator times ½ | normal law, `H_0 = I`, `B_0 = E_0` |
    /// | `E_g^(δ)`, rank `2d_g` | `e_ρ = 0`; `a_ρ`, `b_ρ` from the sign generator | factor steps |
    /// | `R` on a receiving ring | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | the landmark tree on a receiving ring, declared from its first receiver | empty: every node unfounded, every face uniform (`α = ½` at first arrival) | the landmark deposit (Decision 28) |
    /// | `W_c,g` | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | `W_s,g = −f fᵀ` | `f = ½I` | factor step |
    /// | slices | `u_ρ = e_ρ`, `v_ρ = e_(ρ+1)`: the skew cyclic shift | factor steps |
    /// | `q_g` | 0 (every sheet class `+1`) | the lock chart's preconditioned step |
    /// | `c_a`, `b_a`, `F_a` | `I`, `½I`, `½I` | factor steps |
    ///
    /// The sign generator's locus codes: `E` of ring `g` is kind 0; the pair port's current and
    /// earlier reads of ring `g` at the `o`-th declared offset are kind 2 and 3 with part `o` (kind
    /// 1 was `R`'s while it opened at the sign generator, Decision 27).
    ///
    /// [definition; agent-inferred] **`R_0 = 0`, `E_0` the sign generator times ½.** The receiving
    /// map opens at zero, so the combined face opens exactly at the tree's and the wave earns every
    /// bit it moves: the located failure read the old prior's reading `R_0 z` alone at `10 + 9/16 +
    /// ε` bits a cell, a share in `[51/56, 3713/4077]` of the held-out logits' energy. With `E_0 = 0`
    /// and `e_ρ = 0` as well, the source moment `m̃`, the open, every wave and every feature
    /// `f = P_R^(τ_R) v_R` would be zero, so `R`'s step `G = Σ γ g fᵀ` and every upstream covector
    /// `Rᵀ g` would vanish at every commit: the chain of maps needs one nonzero member to carry a
    /// covector. `E_0` takes the sign generator's pattern at the value `R_0` had. Its normal law keeps
    /// the prior's reading (`B_0 = E_0`), a fixed feature map that `R` reads, not a term of the
    /// face: at `R = 0` it moves no logit. `R` moves at the first deposit, and the upstream loci
    /// receive a covector from the second compare on (the tests
    /// `the_wave_is_inert_when_every_map_opens_at_zero` and
    /// `r_opens_at_zero_and_learns_from_the_first_deposit`).
    ///
    /// Every initial value (0, ±½, 1, the unit vectors) lies on every lattice `L ≥ 1`, and each
    /// locus takes the field's declared lattice ([`Field::lattice`]).
    pub fn initial(field: &Field, steps: Steps, budget: u64) -> Result<Self, HnnError> {
        let lattices = field.lattices().clone();
        // L_R = ⌈1/ε_bits⌉, the finest admitted receiver's (`FieldDeclaration::lattice_by_rule`).
        let grain = field
            .receivers()
            .iter()
            .filter(|receiver| receiver.tolerance.is_positive())
            .filter_map(|receiver| {
                (Rat::one() / &receiver.tolerance)
                    .ceil()
                    .to_integer()
                    .to_u128()
            })
            .max()
            .unwrap_or(1);
        let a = field.alphabet();
        let receivers: BTreeSet<usize> = field.receivers().iter().map(|r| r.ring).collect();
        // Each receiving ring's tree, declared from its first declared receiver.
        let tree = |g: usize| -> Result<Option<Landmarks>, HnnError> {
            field
                .receivers()
                .iter()
                .find(|receiver| receiver.ring == g)
                .map(|receiver| Landmarks::new(landmark_declaration(field, receiver)?))
                .transpose()
        };
        let rings = field
            .rings()
            .iter()
            .enumerate()
            .map(|(g, ring)| {
                let n = ring.width();
                let source = field
                    .is_source(g)
                    .then(|| {
                        let map = ExactRatMatrix::shaped(
                            n,
                            a,
                            (0..n)
                                .map(|i| {
                                    (0..a)
                                        .map(|j| {
                                            declared_sign(locus_code(0, g, 0), i as u64, j as u64)
                                                * rat(1, 2)
                                        })
                                        .collect()
                                })
                                .collect(),
                        )?;
                        Ok::<_, HnnError>(NormalLaw::with_prior(map))
                    })
                    .transpose()?;
                let pairs = if field.is_source(g) {
                    field
                        .offsets()
                        .iter()
                        .enumerate()
                        .map(|(o, &offset)| {
                            let reads = |kind: u64| -> Vec<Vec<Rat>> {
                                (0..n)
                                    .map(|rho| {
                                        (0..a)
                                            .map(|x| {
                                                declared_sign(
                                                    locus_code(kind, g, o),
                                                    rho as u64,
                                                    x as u64,
                                                )
                                            })
                                            .collect()
                                    })
                                    .collect()
                            };
                            Ok((
                                offset,
                                PairPort::new(vec![vec![Rat::zero(); n]; n], reads(2), reads(3))?,
                            ))
                        })
                        .collect::<Result<Vec<_>, HnnError>>()?
                } else {
                    Vec::new()
                };
                let receiving = receivers
                    .contains(&g)
                    .then(|| ExactRatMatrix::zero(2 * a, n).map(NormalLaw::with_prior))
                    .transpose()?;
                Ok(RingMaterial {
                    standing: vec![Rat::zero(); n],
                    standing_scale: Rat::one(),
                    passive: scaled_identity(n, rat(1, 2)),
                    passive_scale: Rat::one(),
                    contrast: NormalLaw::with_prior(ExactRatMatrix::zero(n, n)?),
                    slices: (0..n)
                        .map(|rho| (unit(n, rho), unit(n, (rho + 1) % n)))
                        .collect(),
                    slice_scale: Rat::one(),
                    source,
                    pairs,
                    pair_scale: Rat::one(),
                    receiving,
                    tree: tree(g)?,
                })
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let contacts = field
            .contacts()
            .iter()
            .map(|contact| {
                let k = contact.width();
                ContactMaterial {
                    storage: scaled_identity(k, Rat::one()),
                    stiffness: scaled_identity(k, rat(1, 2)),
                    dissipation: scaled_identity(k, rat(1, 2)),
                    scales: [Rat::one(), Rat::one(), Rat::one()],
                }
            })
            .collect();
        Ok(Self {
            rings,
            contacts,
            steps,
            budget,
            commit: 0,
            released: BTreeSet::new(),
            bound: CommittedEnergyBound::new(Rat::zero()),
            lattices,
            carries: Carries::new(),
            clocks: BTreeMap::new(),
            grain,
        })
    }

    /// The commit counter.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// The declared steps.
    pub fn steps(&self) -> &Steps {
        &self.steps
    }

    /// `B_Θ`.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    /// The loci the collapse has released.
    pub fn released(&self) -> &BTreeSet<Locus> {
        &self.released
    }

    /// **A locus's deposit clock** `m` (Lean `Carried.clock`): the count of epochs at the locus's
    /// section, the deposits that reached it with a nonzero update since its founding; not reset at
    /// an aeon boundary, and ended when the collapse releases the locus whole. It is the flux of the
    /// constitution's aeon since the founding through the locus's section
    /// ([`crate::aeon::Epochs::flux`]; Lean `Aeon/Clock/Epoch.reading_eq_crossings`), a count
    /// because deposits only advance (module header); the ticks are not retained.
    pub fn clock(&self, locus: Locus) -> u64 {
        self.clocks.get(&locus).copied().unwrap_or(0)
    }

    /// The running energy-bound product `∏(1 + ε_k)`.
    pub fn energy_product(&self) -> &Rat {
        self.bound.product()
    }

    /// Ring `g`'s source-port normal law `E_g`.
    pub fn source_law(&self, ring: usize) -> Option<&NormalLaw> {
        self.rings[ring].source.as_ref()
    }

    /// Ring `g`'s contrast-port normal law `W_c,g`.
    pub fn contrast_law(&self, ring: usize) -> &NormalLaw {
        &self.rings[ring].contrast
    }

    /// Ring `g`'s receiving-map normal law `R`.
    pub fn receiving_law(&self, ring: usize) -> Option<&NormalLaw> {
        self.rings[ring].receiving.as_ref()
    }

    /// The factor families' statistics `h_x` of ring `g`: standing, passive, slices, pair port.
    pub fn ring_scales(&self, ring: usize) -> [&Rat; 4] {
        let material = &self.rings[ring];
        [
            &material.standing_scale,
            &material.passive_scale,
            &material.slice_scale,
            &material.pair_scale,
        ]
    }

    /// Contact `a`'s factor statistics `h_x`: storage, stiffness, dissipation.
    pub fn contact_scales(&self, contact: usize) -> &[Rat; 3] {
        &self.contacts[contact].scales
    }

    /// **Replace one ring's element material** (a test and control chart, never a law): the
    /// arbitrary-value witness of the collapse and the declared material of a control field. A
    /// chart may place any exact value, on or off the lattice (a directional-derivative probe
    /// needs off-lattice perturbations); a deposit then moves it by lattice steps. The replaced
    /// arrays' carried remainders are dropped with them.
    ///
    /// **A complex-bilinear block is refused at declaration** (design (d), "Reaction"): a reaction
    /// slice is declared only through its factor pair `(u_ρ, v_ρ)`, so `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ` is
    /// skew and workless, the owner's real-bilinear reaction (`holon::reaction`,
    /// `Holon/Reaction.skewReaction_workless`). A full block `c ⊗ s` has no declaration, since no
    /// such block is power-neutral for both `c` and `i c` unless it is zero
    /// (`Holon/Reaction.bilinear_reaction_workless_iff_zero`). The guarantee is structural, the
    /// parameter's type; the doctest fails with a type mismatch (`E0308`):
    ///
    /// ```compile_fail,E0308
    /// use holonics::hnn::Constitution;
    /// use holonics::ratio::linear::ExactRatMatrix;
    /// // A full block is not a declarable slice: slices are factor pairs (u, v).
    /// fn block(theta: Constitution, n: ExactRatMatrix) -> Constitution {
    ///     theta.with_element(0, n.clone(), n.clone(), vec![n]).unwrap()
    /// }
    /// ```
    pub fn with_element(
        mut self,
        ring: usize,
        passive: ExactRatMatrix,
        contrast: ExactRatMatrix,
        slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    ) -> Result<Self, HnnError> {
        let material = &mut self.rings[ring];
        let n = material.standing.len();
        if passive.rows() != n
            || contrast.rows() != n
            || contrast.columns() != n
            || slices.len() != n
            || slices.iter().any(|(u, v)| u.len() != n || v.len() != n)
        {
            return Err(HnnError::Shape {
                what: "ring element material",
                expected: n,
                found: passive.rows(),
            });
        }
        material.passive = passive;
        material.contrast = NormalLaw::with_prior(contrast);
        material.slices = slices;
        for part in [Carrier::Passive, Carrier::Slices] {
            self.carries.remove(&(Locus::Element(ring), part));
        }
        Ok(self)
    }

    /// **Replace one contact's channel factors** (a test and control chart, never a law).
    pub fn with_channel(
        mut self,
        contact: usize,
        storage: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
    ) -> Result<Self, HnnError> {
        let material = &mut self.contacts[contact];
        let k = material.storage.rows();
        for factor in [&storage, &stiffness, &dissipation] {
            if factor.rows() != k {
                return Err(HnnError::Shape {
                    what: "contact factor rows (the channel width)",
                    expected: k,
                    found: factor.rows(),
                });
            }
        }
        material.storage = storage;
        material.stiffness = stiffness;
        material.dissipation = dissipation;
        for family in 0..3 {
            self.carries
                .remove(&(Locus::Channel(contact), Carrier::Factor(family)));
        }
        Ok(self)
    }

    /// **Replace one ring's standing, source port or receiving map** (a test and control chart).
    pub fn with_ports(
        mut self,
        ring: usize,
        standing: Option<Vec<Rat>>,
        source: Option<ExactRatMatrix>,
        receiving: Option<ExactRatMatrix>,
    ) -> Result<Self, HnnError> {
        let material = &mut self.rings[ring];
        if let Some(standing) = standing {
            if standing.len() != material.standing.len() {
                return Err(HnnError::Shape {
                    what: "standing q_g",
                    expected: material.standing.len(),
                    found: standing.len(),
                });
            }
            material.standing = standing;
            self.carries
                .remove(&(Locus::Standing(ring), Carrier::Standing));
        }
        if let Some(source) = source {
            material.source = Some(NormalLaw::with_prior(source));
        }
        if let Some(receiving) = receiving {
            material.receiving = Some(NormalLaw::with_prior(receiving));
        }
        Ok(self)
    }

    /// **Replace a receiving ring's landmark tree** (a test and control chart): refused off a
    /// receiving ring, or for a tree of another declaration than the ring's.
    pub fn with_tree(mut self, ring: usize, tree: Landmarks) -> Result<Self, HnnError> {
        let slot = self
            .rings
            .get_mut(ring)
            .and_then(|material| material.tree.as_mut())
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        if slot.declaration() != tree.declaration() {
            return Err(HnnError::Shape {
                what: "a landmark tree against the receiving ring's declared tree (its depth)",
                expected: slot.declaration().depth,
                found: tree.declaration().depth,
            });
        }
        *slot = tree;
        Ok(self)
    }

    /// **Replace one source ring's pair port at a declared offset** (a test and control chart).
    pub fn with_pair(
        mut self,
        ring: usize,
        offset: usize,
        pair: PairPort,
    ) -> Result<Self, HnnError> {
        let slot = self.rings[ring]
            .pairs
            .iter_mut()
            .find(|(declared, _)| *declared == offset)
            .ok_or(HnnError::Offset { offset })?;
        if pair.rank() != slot.1.rank()
            || pair.outputs().first().map(Vec::len) != slot.1.outputs().first().map(Vec::len)
            || pair.current_reads().first().map(Vec::len)
                != slot.1.current_reads().first().map(Vec::len)
        {
            return Err(HnnError::Shape {
                what: "pair port shape",
                expected: slot.1.rank(),
                found: pair.rank(),
            });
        }
        slot.1 = pair;
        for family in 0..3 {
            self.carries
                .remove(&(Locus::SourcePort(ring), Carrier::Pair { offset, family }));
        }
        Ok(self)
    }

    /// **The constitution's exact bits by carrier** per retained locus: every numerator and
    /// denominator of its lattice entries (values and statistics), of their carried remainders and
    /// of its solved charts at their lattices.
    pub fn carrier_bits_by_locus(&self) -> Vec<(Locus, CarrierBits)> {
        let values = |values: &mut dyn Iterator<Item = &Rat>| -> u64 { values.map(bits).sum() };
        let mut loci: Vec<(Locus, CarrierBits)> = Vec::new();
        for (g, material) in self.rings.iter().enumerate() {
            let mut element = material.contrast.carrier_bits();
            element.entries += values(
                &mut material
                    .passive
                    .entries()
                    .iter()
                    .chain(material.slices.iter().flat_map(|(u, v)| u.iter().chain(v)))
                    .chain([&material.passive_scale, &material.slice_scale]),
            );
            loci.push((Locus::Element(g), element));
            loci.push((
                Locus::Standing(g),
                CarrierBits {
                    entries: values(
                        &mut material.standing.iter().chain([&material.standing_scale]),
                    ),
                    ..CarrierBits::default()
                },
            ));
            if material.source.is_some() || !material.pairs.is_empty() {
                let mut source = material
                    .source
                    .as_ref()
                    .map(NormalLaw::carrier_bits)
                    .unwrap_or_default();
                source.entries += values(
                    &mut material
                        .pairs
                        .iter()
                        .flat_map(|(_, pair)| {
                            pair.outputs()
                                .iter()
                                .chain(pair.current_reads())
                                .chain(pair.earlier_reads())
                                .flatten()
                        })
                        .chain([&material.pair_scale]),
                );
                loci.push((Locus::SourcePort(g), source));
            }
            if let Some(receiving) = &material.receiving {
                let mut parts = receiving.carrier_bits();
                parts.entries += material.tree.as_ref().map_or(0, Landmarks::bits);
                loci.push((Locus::ReceivingMap(g), parts));
            }
        }
        for (a, material) in self.contacts.iter().enumerate() {
            loci.push((
                Locus::Channel(a),
                CarrierBits {
                    entries: values(
                        &mut material
                            .storage
                            .entries()
                            .iter()
                            .chain(material.stiffness.entries())
                            .chain(material.dissipation.entries())
                            .chain(&material.scales),
                    ),
                    ..CarrierBits::default()
                },
            ));
        }
        for ((locus, _), carry) in &self.carries {
            if let Some((_, parts)) = loci.iter_mut().find(|(l, _)| l == locus) {
                parts.remainders += carry.bits();
            }
        }
        loci.retain(|(locus, _)| !self.released.contains(locus));
        loci
    }

    /// **The constitution's exact bits** per retained locus: the sum of its carriers.
    pub fn bits_by_locus(&self) -> Vec<(Locus, u64)> {
        self.carrier_bits_by_locus()
            .into_iter()
            .map(|(locus, parts)| (locus, parts.total()))
            .collect()
    }

    /// The constitution's bits by carrier, over its retained loci.
    pub fn carrier_bits(&self) -> CarrierBits {
        let mut total = CarrierBits::default();
        for (_, parts) in self.carrier_bits_by_locus() {
            total.add(parts);
        }
        total
    }

    /// The constitution's exact bits: the sum over its retained loci.
    pub fn exact_bits(&self) -> u64 {
        self.carrier_bits().total()
    }

    /// **Every carried remainder**, exact, with its locus, its array and its entry (a reading of
    /// the lattice law: each lies in `[−2^(−L_ℓ−1), 2^(−L_ℓ−1))`, Lean `carried_remainder_bounded`).
    pub fn carried_remainders(&self) -> Vec<(Locus, Carrier, usize, Rat)> {
        let mut carried: Vec<(Locus, Carrier, usize, Rat)> = self
            .carries
            .iter()
            .flat_map(|((locus, array), carry)| {
                carry
                    .0
                    .iter()
                    .map(|(entry, r)| (*locus, *array, *entry, r.clone()))
            })
            .collect();
        for (g, material) in self.rings.iter().enumerate() {
            for (locus, law) in [
                (Locus::Element(g), Some(&material.contrast)),
                (Locus::SourcePort(g), material.source.as_ref()),
                (Locus::ReceivingMap(g), material.receiving.as_ref()),
            ] {
                if let Some(law) = law {
                    for (array, carry) in [
                        (Carrier::Map, &law.map_carry),
                        (Carrier::Gram, &law.gram_carry),
                    ] {
                        carried.extend(
                            carry
                                .0
                                .iter()
                                .map(|(entry, r)| (locus, array, *entry, r.clone())),
                        );
                    }
                }
            }
        }
        carried
    }

    /// **The carried trajectory** `Θ + r`: every carried remainder added back onto its entry (a
    /// reading chart, never published: it is off the lattice, and carries no remainder). Reading it
    /// against `Θ` measures what the carried remainders move at a receiver; with the released
    /// residuals it is the exact accumulation of what reached each locus.
    pub fn with_remainders(&self) -> Result<Self, HnnError> {
        let mut exact = self.clone();
        for (locus, array, entry, r) in self.carried_remainders() {
            let ring = match locus {
                Locus::Element(g)
                | Locus::Standing(g)
                | Locus::SourcePort(g)
                | Locus::ReceivingMap(g)
                | Locus::Junction(g) => g,
                Locus::Channel(a) | Locus::Conductance(a) => a,
            };
            let add = |values: &mut [Rat]| -> Result<(), HnnError> {
                let expected = values.len();
                let slot = values.get_mut(entry).ok_or(HnnError::Shape {
                    what: "a carried remainder's entry",
                    expected,
                    found: entry,
                })?;
                *slot += &r;
                Ok(())
            };
            let add_matrix = |matrix: &mut ExactRatMatrix| -> Result<(), HnnError> {
                let mut values = matrix.entries().to_vec();
                add(&mut values)?;
                *matrix = flat_matrix(matrix.rows(), matrix.columns(), values)?;
                Ok(())
            };
            match (locus, array) {
                (Locus::Channel(_), Carrier::Factor(index)) => {
                    let material = &mut exact.contacts[ring];
                    add_matrix(match index {
                        0 => &mut material.storage,
                        1 => &mut material.stiffness,
                        _ => &mut material.dissipation,
                    })?;
                }
                (Locus::Channel(_), Carrier::FactorScale(index)) => {
                    add(std::slice::from_mut(
                        &mut exact.contacts[ring].scales[index],
                    ))?;
                }
                (_, Carrier::Passive) => add_matrix(&mut exact.rings[ring].passive)?,
                (_, Carrier::PassiveScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].passive_scale))?
                }
                (_, Carrier::SliceScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].slice_scale))?
                }
                (_, Carrier::StandingScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].standing_scale))?
                }
                (_, Carrier::PairScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].pair_scale))?
                }
                (_, Carrier::Standing) => add(&mut exact.rings[ring].standing)?,
                (_, Carrier::Slices) => {
                    let material = &mut exact.rings[ring];
                    let n = material.standing.len();
                    let (rho, side, i) = (entry / (2 * n), (entry / n) % 2, entry % n);
                    let (u, v) = &mut material.slices[rho];
                    let slot = if side == 0 { &mut u[i] } else { &mut v[i] };
                    *slot += &r;
                }
                (_, Carrier::Pair { offset, family }) => {
                    let material = &mut exact.rings[ring];
                    let slot = material
                        .pairs
                        .iter_mut()
                        .find(|(declared, _)| *declared == offset)
                        .ok_or(HnnError::Offset { offset })?;
                    let mut families = [
                        slot.1.outputs().to_vec(),
                        slot.1.current_reads().to_vec(),
                        slot.1.earlier_reads().to_vec(),
                    ];
                    let width = families[family].first().map_or(1, Vec::len).max(1);
                    families[family][entry / width][entry % width] += &r;
                    let [outputs, current, earlier] = families;
                    slot.1 = PairPort::new(outputs, current, earlier)?;
                }
                (_, Carrier::Map | Carrier::Gram) => {
                    let material = &mut exact.rings[ring];
                    let law = match locus {
                        Locus::SourcePort(_) => material.source.as_mut(),
                        Locus::ReceivingMap(_) => material.receiving.as_mut(),
                        _ => Some(&mut material.contrast),
                    }
                    .ok_or(HnnError::MissingSourcePort { ring })?;
                    if array == Carrier::Map {
                        add_matrix(&mut law.map)?;
                    } else {
                        let n = law.gram.len();
                        law.gram[entry / n][entry % n] += &r;
                    }
                }
                (_, Carrier::Factor(_) | Carrier::FactorScale(_)) => {}
            }
        }
        exact.carries.clear();
        for material in &mut exact.rings {
            for law in [
                Some(&mut material.contrast),
                material.source.as_mut(),
                material.receiving.as_mut(),
            ]
            .into_iter()
            .flatten()
            {
                law.map_carry = Carry::default();
                law.gram_carry = Carry::default();
            }
        }
        Ok(exact)
    }

    /// `L_R`, the finest admitted receiver grain the chart rule reads.
    pub fn grain(&self) -> u128 {
        self.grain
    }

    /// **The chart rule of a normal law's locus** ([`ChartRule`]): its lattice and `L_R`.
    pub fn chart_rule(&self, locus: Locus) -> Result<ChartRule, HnnError> {
        Ok(ChartRule::new(self.lattice(locus)?, self.grain))
    }

    /// The declared lattice of a learned locus.
    pub fn lattice(&self, locus: Locus) -> Result<Lattice, HnnError> {
        self.lattices
            .get(&locus)
            .copied()
            .ok_or(HnnError::Lattice { locus })
    }

    /// **Whether every retained entry lies on its locus's lattice** (Lean `run_onLattice`): the
    /// maps, factors and statistics; the solved charts live on their own lattices `2^(−L_s)ℤ` by
    /// construction (integer coordinates), and the remainders are the carried residuals.
    pub fn on_lattice(&self) -> bool {
        let retained = |locus: Locus| !self.released.contains(&locus);
        let all = |lattice: Option<&Lattice>, values: &mut dyn Iterator<Item = &Rat>| {
            let Some(lattice) = lattice else {
                return false;
            };
            for value in values {
                if !lattice.contains(value) {
                    return false;
                }
            }
            true
        };
        let rings = self.rings.iter().enumerate().all(|(g, material)| {
            let element = self.lattices.get(&Locus::Element(g));
            let standing = self.lattices.get(&Locus::Standing(g));
            let source = self.lattices.get(&Locus::SourcePort(g));
            let receiving = self.lattices.get(&Locus::ReceivingMap(g));
            (!retained(Locus::Element(g))
                || (all(
                    element,
                    &mut material
                        .passive
                        .entries()
                        .iter()
                        .chain(material.slices.iter().flat_map(|(u, v)| u.iter().chain(v)))
                        .chain([&material.passive_scale, &material.slice_scale]),
                ) && element.is_some_and(|l| material.contrast.on_lattice(l))))
                && (!retained(Locus::Standing(g))
                    || all(
                        standing,
                        &mut material.standing.iter().chain([&material.standing_scale]),
                    ))
                && (!retained(Locus::SourcePort(g))
                    || material.source.is_none() && material.pairs.is_empty()
                    || (all(
                        source,
                        &mut material
                            .pairs
                            .iter()
                            .flat_map(|(_, pair)| {
                                pair.outputs()
                                    .iter()
                                    .chain(pair.current_reads())
                                    .chain(pair.earlier_reads())
                                    .flatten()
                            })
                            .chain([&material.pair_scale]),
                    ) && material
                        .source
                        .as_ref()
                        .is_none_or(|law| source.is_some_and(|l| law.on_lattice(l)))))
                && material
                    .receiving
                    .as_ref()
                    .is_none_or(|law| receiving.is_some_and(|l| law.on_lattice(l)))
        });
        let contacts = self.contacts.iter().enumerate().all(|(a, material)| {
            !retained(Locus::Channel(a))
                || all(
                    self.lattices.get(&Locus::Channel(a)),
                    &mut material
                        .storage
                        .entries()
                        .iter()
                        .chain(material.stiffness.entries())
                        .chain(material.dissipation.entries())
                        .chain(&material.scales),
                )
        });
        rings && contacts
    }

    /// The contact storage forms `(C_a, K_a)` per contact, as symmetric forms.
    fn storage_forms(&self) -> Result<Vec<[ExactRatMatrix; 2]>, HnnError> {
        self.contacts
            .iter()
            .map(|material| Ok([gram(&material.storage)?, gram(&material.stiffness)?]))
            .collect()
    }

    /// **The successor of a staged deposit** (design (c), `deposit`): each linear locus's prox
    /// step over its window's samples, each factor family's preconditioned step, the commit
    /// advanced, the energy-growth bound certified, and the budget checked on the successor's
    /// exact bits before anything is published. Refused with [`HnnError::ConstitutionBudget`]
    /// past `B_Θ`, with [`HnnError::StaleDeposit`] when the deposit was computed at another commit,
    /// and with [`HnnError::ReleasedLocus`] when it names a released locus.
    pub fn deposited(&self, deposit: &Deposit) -> Result<(Self, DepositReading), HnnError> {
        if deposit.commit() != self.commit {
            return Err(HnnError::StaleDeposit {
                staged: deposit.commit(),
                published: self.commit,
            });
        }
        let mut next = self.clone();
        let (proxy, eta) = (self.steps.proxy.clone(), self.steps.factor.clone());
        // The deposit's steps by locus, each with its place in the deposit's order (its linear
        // steps, then its factor steps, then its class-mass steps).
        let mut groups: BTreeMap<Locus, Vec<(usize, LocusStep<'_>)>> = BTreeMap::new();
        for (index, step) in deposit.linear().iter().enumerate() {
            groups
                .entry(step.locus.locus())
                .or_default()
                .push((index, LocusStep::Linear(step)));
        }
        let linear = deposit.linear().len();
        for (index, step) in deposit.factors().iter().enumerate() {
            groups
                .entry(step.gradient.locus())
                .or_default()
                .push((linear + index, LocusStep::Factor(step)));
        }
        let factors = linear + deposit.factors().len();
        for (index, step) in deposit.landmarks().iter().enumerate() {
            groups
                .entry(Locus::ReceivingMap(step.ring))
                .or_default()
                .push((factors + index, LocusStep::Landmark(step)));
        }
        // Each locus's material and carried remainders, taken apart: a locus's steps read and
        // write only its own, so the loci run together (`hnn::realization`), each in its
        // steps' order with its own budgeted carry, at the clock it would advance it to.
        let mut local: BTreeMap<Locus, Carries> = groups
            .keys()
            .map(|locus| (*locus, Carries::new()))
            .collect();
        let mut rest = Carries::new();
        for (key, carry) in std::mem::take(&mut next.carries) {
            match local.get_mut(&key.0) {
                Some(map) => {
                    map.insert(key, carry);
                }
                None => {
                    rest.insert(key, carry);
                }
            }
        }
        let mut materials = LocusMaterial::split(&mut next.rings, &mut next.contacts, &groups);
        let regions: Vec<_> = groups
            .iter()
            .zip(local)
            .map(|((locus, steps), (_, carries))| (*locus, steps, materials.remove(locus), carries))
            .collect();
        let done: Vec<LocusDeposit> = regions
            .into_par_iter()
            .map(|(locus, steps, mut material, mut carries)| {
                self.deposit_at(locus, steps, material.as_mut(), &mut carries, &proxy, &eta)
                    .map(|at| (locus, carries, at))
            })
            .collect();
        drop(materials);
        // The refusal is the first in the deposit's order: the one the steps taken in that order
        // meet first.
        let (mut deposited, mut refusals) = (Vec::with_capacity(done.len()), Vec::new());
        for region in done {
            match region {
                Ok(region) => deposited.push(region),
                Err(refusal) => refusals.push(refusal),
            }
        }
        if let Some((_, refusal)) = refusals.into_iter().min_by_key(|(index, _)| *index) {
            return Err(refusal);
        }
        let mut strokes: BTreeMap<Locus, BudgetedCarry> = BTreeMap::new();
        let mut charts: Vec<(Locus, ChartReading)> = Vec::new();
        next.carries = rest;
        for (locus, carries, (at, read)) in deposited {
            next.carries.extend(carries);
            strokes.insert(locus, at);
            charts.extend(read.into_iter().map(|reading| (locus, reading)));
        }
        next.carries.retain(|_, carry| !carry.0.is_empty());
        next.commit += 1;
        // The clocks of the loci whose update was nonzero advance; the released residuals and the
        // stepped entries are read off the budgeted carries.
        let (mut released, mut stepped) = (Vec::new(), 0u64);
        for (locus, at) in &strokes {
            if at.moved() {
                next.clocks.insert(*locus, at.clock());
            }
            stepped += at.stepped();
            released.extend(
                at.released()
                    .into_iter()
                    .map(|(carrier, entry, residual)| (*locus, carrier, entry, residual)),
            );
        }
        let released_bits = released.iter().map(|(.., residual)| bits(residual)).sum();
        // The storage forms are the contacts' C_a and K_a; the reaction material, the ports and the
        // standing store nothing, so a deposit that moves only them has ε_k = 0.
        let (before, after) = (self.storage_forms()?, next.storage_forms()?);
        let growth = certify_growth(&before, &after)?;
        if let Some(epsilon) = &growth {
            let (initial, reached) = (joint_form(&before)?, joint_form(&after)?);
            next.bound
                .commit(&initial, &reached, epsilon, Rat::zero())?;
        }
        let bits = next.exact_bits();
        if bits > self.budget {
            let predecessor = self.bits_by_locus();
            let mut grown: Vec<(Locus, i128)> = next
                .bits_by_locus()
                .into_iter()
                .map(|(locus, after)| {
                    let before = predecessor
                        .iter()
                        .find(|(l, _)| *l == locus)
                        .map_or(0, |(_, bits)| *bits);
                    (locus, i128::from(after) - i128::from(before))
                })
                .collect();
            grown.sort_by(|a, b| b.1.cmp(&a.1));
            return Err(HnnError::ConstitutionBudget {
                bits,
                budget: self.budget,
                commit: self.commit,
                loci: grown.into_iter().take(4).map(|(locus, _)| locus).collect(),
            });
        }
        let reading = DepositReading {
            growth,
            product: next.bound.product().clone(),
            commit: next.commit,
            bits,
            budget: self.budget,
            loci: deposit.loci(),
            released,
            released_bits,
            stepped,
            charts,
            landmarks: deposit.landmarks().len() as u64,
        };
        Ok((next, reading))
    }

    /// **One locus's steps of a deposit**, in the deposit's order, on the locus's material and
    /// carried remainders alone, with the locus's budgeted carry opened at the clock the deposit
    /// would advance it to, and its normal law's chart readings. A refusal returns with the place of
    /// the step that met it in the deposit's order.
    fn deposit_at(
        &self,
        locus: Locus,
        steps: &[(usize, LocusStep<'_>)],
        mut material: Option<&mut LocusMaterial<'_>>,
        carries: &mut Carries,
        proxy: &Rat,
        eta: &Rat,
    ) -> Result<(BudgetedCarry, Vec<ChartReading>), (usize, HnnError)> {
        let mut stroke: Option<BudgetedCarry> = None;
        let mut charts = Vec::new();
        let budgeted = |stroke: &mut Option<BudgetedCarry>| -> Result<(), HnnError> {
            if stroke.is_none() {
                *stroke = Some(BudgetedCarry::new(
                    self.lattice(locus)?,
                    self.clock(locus) + 1,
                ));
            }
            Ok(())
        };
        for (index, step) in steps {
            let refused = |refusal: HnnError| (*index, refusal);
            if self.released.contains(&locus) {
                return Err(refused(HnnError::ReleasedLocus { locus }));
            }
            match step {
                LocusStep::Linear(step) => {
                    let law = material
                        .as_deref_mut()
                        .and_then(|material| material.law(step.locus))
                        .ok_or(HnnError::MissingSourcePort {
                            ring: match step.locus {
                                LinearLocus::SourcePort(g)
                                | LinearLocus::Contrast(g)
                                | LinearLocus::Receiving(g) => g,
                            },
                        })
                        .map_err(refused)?;
                    budgeted(&mut stroke).map_err(refused)?;
                    let at = stroke.as_mut().expect("opened above");
                    let rule = self.chart_rule(locus).map_err(refused)?;
                    let (next, reading) = law
                        .deposited(&step.samples, proxy, &rule, at)
                        .map_err(refused)?;
                    *law = next;
                    charts.extend(reading);
                }
                LocusStep::Factor(step) => {
                    budgeted(&mut stroke).map_err(refused)?;
                    let at = stroke.as_mut().expect("opened above");
                    let material = material
                        .as_deref_mut()
                        .ok_or(HnnError::Lattice { locus })
                        .map_err(refused)?;
                    factor_step(material, carries, step, eta, at).map_err(refused)?;
                }
                LocusStep::Landmark(step) => {
                    // The tree carries no lattice remainder, so the stroke is opened for the locus's
                    // reading and nothing moves its clock.
                    budgeted(&mut stroke).map_err(refused)?;
                    let tree = material
                        .as_deref_mut()
                        .and_then(LocusMaterial::tree)
                        .ok_or(HnnError::MissingReceivingMap { ring: step.ring })
                        .map_err(refused)?;
                    tree.deposit(&step.address, step.class).map_err(refused)?;
                }
            }
        }
        stroke
            .map(|at| (at, charts))
            .ok_or(HnnError::Lattice { locus })
            .map_err(|refusal| (0, refusal))
    }

    /// **Release loci** (the collapse's only mutator, `hnn::retention`): each released locus's
    /// learned material becomes the zero map and its statistics are dropped; it counts no bits and
    /// no reading reads it.
    pub(crate) fn release(&mut self, loci: &BTreeSet<Locus>) -> Result<(), HnnError> {
        for locus in loci {
            match *locus {
                Locus::Element(g) => {
                    let material = &mut self.rings[g];
                    let n = material.standing.len();
                    material.passive = ExactRatMatrix::zero(n, material.passive.columns())?;
                    material.contrast = NormalLaw::with_prior(ExactRatMatrix::zero(n, n)?);
                    material.slices = vec![(vec![Rat::zero(); n], vec![Rat::zero(); n]); n];
                }
                Locus::Standing(g) => {
                    let material = &mut self.rings[g];
                    material.standing = vec![Rat::zero(); material.standing.len()];
                }
                Locus::SourcePort(g) => {
                    let material = &mut self.rings[g];
                    if let Some(source) = &material.source {
                        let (m, n) = (source.map.rows(), source.map.columns());
                        material.source = Some(NormalLaw::with_prior(ExactRatMatrix::zero(m, n)?));
                    }
                    for (_, pair) in &mut material.pairs {
                        let zero = |family: &[Vec<Rat>]| -> Vec<Vec<Rat>> {
                            family.iter().map(|x| vec![Rat::zero(); x.len()]).collect()
                        };
                        *pair = PairPort::new(
                            zero(pair.outputs()),
                            zero(pair.current_reads()),
                            zero(pair.earlier_reads()),
                        )?;
                    }
                }
                Locus::Channel(a) => {
                    let material = &mut self.contacts[a];
                    let k = material.storage.rows();
                    material.storage = ExactRatMatrix::zero(k, material.storage.columns())?;
                    material.stiffness = ExactRatMatrix::zero(k, material.stiffness.columns())?;
                    material.dissipation = ExactRatMatrix::zero(k, material.dissipation.columns())?;
                }
                // The receiving map is never released; junctions and conductances are declared.
                Locus::ReceivingMap(_) | Locus::Junction(_) | Locus::Conductance(_) => {}
            }
            self.released.insert(*locus);
        }
        // A released locus leaves whole, with its carried remainders and its clock (Lean
        // `carriedRel`); the retained loci keep theirs.
        let kept = |locus: &Locus| !loci.contains(locus) || matches!(locus, Locus::ReceivingMap(_));
        self.carries.retain(|(locus, _), _| kept(locus));
        self.clocks.retain(|locus, _| kept(locus));
        Ok(())
    }
}

/// One locus's deposited carried remainders, budgeted carry and chart readings, or the refusal its
/// steps met with the place of the refusing step in the deposit's order.
type LocusDeposit = Result<(Locus, Carries, (BudgetedCarry, Vec<ChartReading>)), (usize, HnnError)>;

/// One step of a deposit at its locus.
#[derive(Clone, Copy)]
enum LocusStep<'d> {
    Linear(&'d LinearStep),
    Factor(&'d FactorStep),
    Landmark(&'d LandmarkStep),
}

/// [definition; agent-inferred] **One locus's material, borrowed apart from the rest** of the
/// successor a deposit builds (the module header's loci): the element's passive factor, contrast
/// port and slices with their statistics (and the ring's width, which the slices' carry indexes
/// by); the standing and its statistic; the source port with the pair ports and their statistic;
/// the receiving map with the receiving parametron's landmark tree; a contact's channel factors. No
/// two loci share a part, so their steps run together.
enum LocusMaterial<'a> {
    Element {
        passive: &'a mut ExactRatMatrix,
        passive_scale: &'a mut Rat,
        contrast: &'a mut NormalLaw,
        slices: &'a mut Vec<(Vec<Rat>, Vec<Rat>)>,
        slice_scale: &'a mut Rat,
        width: usize,
    },
    Standing {
        standing: &'a mut Vec<Rat>,
        scale: &'a mut Rat,
    },
    SourcePort {
        source: &'a mut Option<NormalLaw>,
        pairs: &'a mut Vec<(usize, PairPort)>,
        scale: &'a mut Rat,
    },
    ReceivingMap {
        receiving: &'a mut Option<NormalLaw>,
        tree: &'a mut Option<Landmarks>,
    },
    Channel(&'a mut ContactMaterial),
}

impl<'a> LocusMaterial<'a> {
    /// Each locus the steps name, its material borrowed apart.
    fn split<S>(
        rings: &'a mut [RingMaterial],
        contacts: &'a mut [ContactMaterial],
        named: &BTreeMap<Locus, S>,
    ) -> BTreeMap<Locus, Self> {
        let mut materials = BTreeMap::new();
        for (g, material) in rings.iter_mut().enumerate() {
            let RingMaterial {
                standing,
                standing_scale,
                passive,
                passive_scale,
                contrast,
                slices,
                slice_scale,
                source,
                pairs,
                pair_scale,
                receiving,
                tree,
            } = material;
            let width = standing.len();
            if named.contains_key(&Locus::Element(g)) {
                materials.insert(
                    Locus::Element(g),
                    LocusMaterial::Element {
                        passive,
                        passive_scale,
                        contrast,
                        slices,
                        slice_scale,
                        width,
                    },
                );
            }
            if named.contains_key(&Locus::Standing(g)) {
                materials.insert(
                    Locus::Standing(g),
                    LocusMaterial::Standing {
                        standing,
                        scale: standing_scale,
                    },
                );
            }
            if named.contains_key(&Locus::SourcePort(g)) {
                materials.insert(
                    Locus::SourcePort(g),
                    LocusMaterial::SourcePort {
                        source,
                        pairs,
                        scale: pair_scale,
                    },
                );
            }
            if named.contains_key(&Locus::ReceivingMap(g)) {
                materials.insert(
                    Locus::ReceivingMap(g),
                    LocusMaterial::ReceivingMap { receiving, tree },
                );
            }
        }
        for (a, material) in contacts.iter_mut().enumerate() {
            if named.contains_key(&Locus::Channel(a)) {
                materials.insert(Locus::Channel(a), LocusMaterial::Channel(material));
            }
        }
        materials
    }

    /// The normal law a linear step deposits on, when this locus carries it.
    fn law(&mut self, locus: LinearLocus) -> Option<&mut NormalLaw> {
        match (locus, self) {
            (LinearLocus::SourcePort(_), LocusMaterial::SourcePort { source, .. }) => {
                source.as_mut()
            }
            (LinearLocus::Contrast(_), LocusMaterial::Element { contrast, .. }) => Some(contrast),
            (LinearLocus::Receiving(_), LocusMaterial::ReceivingMap { receiving, .. }) => {
                receiving.as_mut()
            }
            _ => None,
        }
    }

    /// The receiving parametron's landmark tree, when this locus carries it.
    fn tree(&mut self) -> Option<&mut Landmarks> {
        match self {
            LocusMaterial::ReceivingMap { tree, .. } => tree.as_mut(),
            _ => None,
        }
    }
}

/// **One factor family's carried step** (module header): `h_x` carried to `h_x'`, then
/// `Δx = (η_x / h_x') G_x` carried onto the family's entries, on the family's locus's material and
/// carried remainders.
fn factor_step(
    material: &mut LocusMaterial<'_>,
    carries: &mut Carries,
    step: &FactorStep,
    eta: &Rat,
    at: &mut BudgetedCarry,
) -> Result<(), HnnError> {
    let locus = step.gradient.locus();
    let energy = &step.energy;
    match (&step.gradient, material) {
        (
            FactorGradient::Passive { gradient, .. },
            LocusMaterial::Element {
                passive,
                passive_scale,
                ..
            },
        ) => {
            let rate = advance(
                carries,
                at,
                (locus, Carrier::PassiveScale),
                passive_scale,
                energy,
                eta,
            )?;
            **passive = carried_matrix(
                carries.entry((locus, Carrier::Passive)).or_default(),
                at,
                Carrier::Passive,
                passive,
                &rate_matrix(&rate, gradient)?,
                "a passive factor gradient",
            )?;
        }
        (
            FactorGradient::Slices { gradient, .. },
            LocusMaterial::Element {
                slices,
                slice_scale,
                width,
                ..
            },
        ) => {
            let rate = advance(
                carries,
                at,
                (locus, Carrier::SliceScale),
                slice_scale,
                energy,
                eta,
            )?;
            let n = *width;
            let carry = carries.entry((locus, Carrier::Slices)).or_default();
            for (rho, ((u, v), (du, dv))) in slices.iter_mut().zip(gradient).enumerate() {
                for (side, (x, dx)) in [(u, du), (v, dv)].into_iter().enumerate() {
                    for (i, (x, dx)) in x.iter_mut().zip(dx).enumerate() {
                        carry.deposit(
                            at,
                            Carrier::Slices,
                            (2 * rho + side) * n + i,
                            x,
                            &rate_times(&rate, dx),
                        );
                    }
                }
            }
        }
        (
            FactorGradient::Standing { gradient, .. },
            LocusMaterial::Standing { standing, scale },
        ) => {
            let rate = advance(
                carries,
                at,
                (locus, Carrier::StandingScale),
                scale,
                energy,
                eta,
            )?;
            let carry = carries.entry((locus, Carrier::Standing)).or_default();
            for (i, (x, dx)) in standing.iter_mut().zip(gradient).enumerate() {
                carry.deposit(at, Carrier::Standing, i, x, &rate_times(&rate, dx));
            }
        }
        (
            FactorGradient::PairPort {
                offset,
                outputs,
                current,
                earlier,
                ..
            },
            LocusMaterial::SourcePort { pairs, scale, .. },
        ) => {
            let rate = advance(carries, at, (locus, Carrier::PairScale), scale, energy, eta)?;
            let slot = pairs
                .iter_mut()
                .find(|(declared, _)| declared == offset)
                .ok_or(HnnError::Offset { offset: *offset })?;
            let mut family = |index: usize, base: &[Vec<Rat>], delta: &[Vec<Rat>]| {
                let carrier = Carrier::Pair {
                    offset: *offset,
                    family: index,
                };
                carried_rows(
                    carries.entry((locus, carrier)).or_default(),
                    at,
                    carrier,
                    base,
                    delta,
                    &rate,
                )
            };
            let outputs = family(0, slot.1.outputs(), outputs);
            let current = family(1, slot.1.current_reads(), current);
            let earlier = family(2, slot.1.earlier_reads(), earlier);
            slot.1 = PairPort::new(outputs, current, earlier)?;
        }
        (
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. },
            LocusMaterial::Channel(material),
        ) => {
            let index = match &step.gradient {
                FactorGradient::Storage { .. } => 0,
                FactorGradient::Stiffness { .. } => 1,
                _ => 2,
            };
            let rate = advance(
                carries,
                at,
                (locus, Carrier::FactorScale(index)),
                &mut material.scales[index],
                energy,
                eta,
            )?;
            let factor = match index {
                0 => &mut material.storage,
                1 => &mut material.stiffness,
                _ => &mut material.dissipation,
            };
            *factor = carried_matrix(
                carries.entry((locus, Carrier::Factor(index))).or_default(),
                at,
                Carrier::Factor(index),
                factor,
                &rate_matrix(&rate, gradient)?,
                "a channel factor gradient",
            )?;
        }
        // A factor step's locus is its gradient's, so its material is this locus's.
        _ => return Err(HnnError::Lattice { locus }),
    }
    Ok(())
}

fn joint_form(
    forms: &[[ExactRatMatrix; 2]],
) -> Result<crate::ratio::linear::inertia::SymmetricForm, HnnError> {
    let blocks: Vec<&ExactRatMatrix> = forms.iter().flat_map(|pair| pair.iter()).collect();
    let n: usize = blocks.iter().map(|block| block.rows()).sum();
    let mut rows = vec![vec![Rat::zero(); n]; n];
    let mut at = 0;
    for block in blocks {
        for i in 0..block.rows() {
            for j in 0..block.columns() {
                rows[at + i][at + j] = block.get(i, j)?.clone();
            }
        }
        at += block.rows();
    }
    let joint = ExactRatMatrix::shaped(n, n, rows)?;
    Ok(matrix_form(&joint).map_err(crate::holon::HolonError::from)?)
}

/// The least `ε ∈ {0} ∪ {2^k : −20 ≤ k ≤ 40}` certifying `Q_(k+1) ⪯ (1 + ε) Q_k` on every contact's
/// storage and stiffness form, or `None` when none does (a reading of the deposit's energy growth).
///
/// [definition; agent-inferred] Read block by block: the joint form is block-diagonal, so it is
/// certified at `ε` exactly when every block is (its negative inertia is the blocks' sum), and the
/// least joint `ε` is the largest of the blocks' least. Each block's `Q_k` is a Gram (`C = c cᵀ`,
/// `K = b bᵀ`), so `(1 + ε) Q_k − Q_(k+1)` only gains the PSD term `(ε′ − ε) Q_k` as `ε` grows to
/// `ε′`: a block's certified candidates are upward closed, and its least is found by bisection over
/// the ordered candidates. An unchanged block certifies at `0`.
fn certify_growth(
    before: &[[ExactRatMatrix; 2]],
    after: &[[ExactRatMatrix; 2]],
) -> Result<Option<Rat>, HnnError> {
    let candidates: Vec<Rat> = std::iter::once(Rat::zero())
        .chain((-20i32..=40).map(|k| {
            if k < 0 {
                Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
            } else {
                Rat::from_integer(BigInt::one() << k as usize)
            }
        }))
        .collect();
    let last = candidates.len() - 1;
    let mut least = 0usize;
    for (old, new) in before.iter().flatten().zip(after.iter().flatten()) {
        if old == new {
            continue;
        }
        let form = |m: &ExactRatMatrix| matrix_form(m).map_err(crate::holon::HolonError::from);
        let (old, new) = (form(old)?, form(new)?);
        let certifies = |index: usize| {
            CommittedEnergyBound::certify_deposit(&old, &new, &candidates[index]).is_ok()
        };
        if certifies(least) {
            continue;
        }
        if !certifies(last) {
            return Ok(None);
        }
        // `lo` fails and `hi` certifies.
        let (mut lo, mut hi) = (least, last);
        while hi - lo > 1 {
            let middle = lo + (hi - lo) / 2;
            if certifies(middle) {
                hi = middle;
            } else {
                lo = middle;
            }
        }
        least = hi;
    }
    Ok(Some(candidates[least].clone()))
}

impl ConstitutionRead for Constitution {
    fn standing(&self, ring: usize) -> &[Rat] {
        &self.rings[ring].standing
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        &self.rings[ring].passive
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        self.rings[ring].contrast.map()
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        &self.rings[ring].slices
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.rings[ring].source.as_ref().map(NormalLaw::map)
    }
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort> {
        self.rings[ring]
            .pairs
            .iter()
            .find(|(declared, _)| *declared == offset)
            .map(|(_, pair)| pair)
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].storage
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].stiffness
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].dissipation
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.rings[ring].receiving.as_ref().map(NormalLaw::map)
    }
    fn landmarks(&self, ring: usize) -> Option<&Landmarks> {
        self.rings[ring].tree.as_ref()
    }
}
