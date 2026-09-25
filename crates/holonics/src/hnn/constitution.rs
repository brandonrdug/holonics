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
//! on a receiving ring its receiving map `R`. Per contact `a`: its channel's square factors
//! (`C_a = c_a c_aᵀ`, `K_a = b_a b_aᵀ`, `D_a = F_a F_aᵀ`). The junction admittance `Y_g` and the
//! contact conductance `G_a` (`Y_a`, `β_a`, the screws) are declared on the field in campaign 1; the
//! collapse names them as loci, but they carry no learned value.
//!
//! [definition] **Deposition** (design (a), `deposit`; Lean `HNN/Normal`), the exact update `Δ` of
//! each locus at the predecessor's lattice-valued operands:
//!
//! ```text
//! ΔH_U = Σ_t w f_t f_tᵀ ,            ΔW_U = γ_U Σ_t w g_t (H_U'⁻¹ f_t)ᵀ ,  H_U' the carried successor Gram    per linear locus (E_g, R, W_c)
//! Δh_x = Σ_t w |f_t|² ,              Δx = η_x G_x / h_x' ,                 h_x' the carried successor statistic  per factor family
//! ```
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
//! carried, and the solved chart `H⁻¹` of the carried Gram: by Sherman–Morrison when a deposit
//! applies its rank-one terms exactly (integer counts at `E`), and by one exact inversion when the
//! split moved it otherwise. [proved-derived; formal-checked] **The carried Gram stays positive
//! definite with no clamp** (Lean `carried_gram_posDef`, `carried_gram_posDef_rule`): every entry
//! of `H` is within one unit of the exact Gram `H_exact = I + Σ w f fᵀ ⪰ I`
//! (`within_one_unit_since_founding`), so `|vᵀ(H − H_exact)v| ≤ u(Σ|v_i|)² ≤ n·u·|v|²` for its
//! width `n`, and since the lattice rule's `X_ℓ` is at least `n`, `n·u ≤ 1/(2L_R)` and
//! `H ⪰ (1 − 1/(2L_R)) I` since the locus's founding. `B` is not carried: under `W H = B` it is
//! `W H`, and the prox step `W' = W + γ G H'⁻¹` (Lean `HNN/Normal.normal_prox_step`) needs only
//! `W`, `H'` and `G`. The factor carriers keep `C`, `K`, `D` and `−W_s` positive semidefinite as
//! squares, with no clamp and no projection (Lean `factorCarrier_psd`). [agent-inferred] `h_x` is a
//! statistic like `H`: it accumulates over deposits, starting at 1, so a factor step is
//! preconditioned by its family's own feature energy.
//!
//! [definition] **The budget and stop rule** (design (d), R3 §5): the successor is computed exactly
//! and its exact bits (every numerator and denominator: the lattice entries, the carried remainders,
//! the statistics and the solved charts) are counted before publication. Past `B_Θ` the deposit is
//! refused with [`HnnError::ConstitutionBudget`], naming the loci that grew most; the predecessor
//! stays published. The lattice bounds the entries' bits (`lattice_bits_bounded`) and the clock the
//! remainders' (`remainder_rat_bits_bounded`); [`Constitution::carrier_bits`] reads the three parts
//! separately, and [`DepositReading`] the released residuals and their bits. The deposit clocks,
//! like the commit counter, are counters of `⌈log₂ m⌉` bits and are not counted against `B_Θ`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Normal.normal_prox_step` at the carried Gram, with `HNN/LatticeDeposit.within_one_unit_since_founding` | [`NormalLaw`]: `W` is the prox iterate at the carried Gram `H'` (`B` is not carried, so `W` is not the minimizer of the accumulated `J(W)`), and `H` stays within one unit of the exact statistic `I + Σ w f fᵀ` |
//! | `HNN/Normal.normal_prox_step`, `depositLocus_solves` | [`NormalLaw::deposited`] (the exact step at the carried Gram) |
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

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::moment::PairPort;
use crate::hnn::port::Deposit;
use crate::hnn::propagation::gram;
use crate::holon::deposition::CommittedEnergyBound;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{Chart, IntegralMatrix, integral, lcm, matrix_form, row_dot};
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
    /// Returns whether the step applied `Δ` exactly (`q·2^(−L) = Δ`).
    fn deposit(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        index: usize,
        entry: &mut Rat,
        update: &Rat,
    ) -> bool {
        if update.is_zero() {
            return true;
        }
        at.moved = true;
        let (staged, applied) = at
            .staged
            .remove(&(carrier, index))
            .unwrap_or_else(|| (Rat::zero(), BigInt::zero()));
        let previous = self.0.remove(&index).unwrap_or_else(Rat::zero);
        let precision = at.precision();
        let exponent = at.lattice.exponent + precision;
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
        let (quotient, coordinate) = at.lattice.div_rem_coordinate(&point, precision);
        let remainder = Rat::new(coordinate, BigInt::one() << exponent as usize);
        let exactly = if staged.is_zero() {
            residual.is_zero() && remainder == previous
        } else {
            &remainder + &residual == previous + staged
        };
        *entry += Rat::new(quotient.clone(), at.lattice.scale());
        if !remainder.is_zero() {
            self.0.insert(index, remainder);
        }
        let applied = applied + quotient;
        if !residual.is_zero() || !applied.is_zero() {
            at.staged.insert((carrier, index), (residual, applied));
        }
        exactly
    }

    /// Carry a whole flat array's update, entry by entry. Returns whether every step was exact.
    fn deposit_all(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        entries: &mut [Rat],
        updates: &[Rat],
    ) -> bool {
        let mut exact = true;
        for (index, (entry, update)) in entries.iter_mut().zip(updates).enumerate() {
            exact &= self.deposit(at, carrier, index, entry, update);
        }
        exact
    }

    /// The remainder at an entry.
    fn at(&self, index: usize) -> Rat {
        self.0.get(&index).cloned().unwrap_or_else(Rat::zero)
    }

    fn bits(&self) -> u64 {
        self.0.values().map(bits).sum()
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
/// (maps, factors, statistics), their carried remainders, and the solved charts `H⁻¹` of the
/// carried Grams; each value counted by its numerator's and denominator's bits.
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
/// remainders, and the solved chart `H⁻¹` of the carried Gram. `B = W H` is not carried (module
/// header). Its law is the prox step at the carried Gram (Lean `HNN/Normal.normal_prox_step`,
/// `W' = W + γ G H'⁻¹`) with the carried Gram within one unit of the exact statistic since the
/// locus's founding (`HNN/LatticeDeposit.within_one_unit_since_founding`): `W` is the prox iterate,
/// not the minimizer of the accumulated objective `tr(WHWᵀ) − 2tr(WBᵀ) + C`, which
/// `normalStatistic_standing` states for an exact `(H, B)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalLaw {
    map: ExactRatMatrix,
    gram: Vec<Vec<Rat>>,
    solved: Vec<Vec<Rat>>,
    map_carry: Carry,
    gram_carry: Carry,
}

impl NormalLaw {
    /// **The unit prior at a map**: `H_0 = I` (so `B_0 = W_0`), no remainder.
    pub fn with_prior(map: ExactRatMatrix) -> Self {
        let n = map.columns();
        let identity: Vec<Vec<Rat>> = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| if i == j { Rat::one() } else { Rat::zero() })
                    .collect()
            })
            .collect();
        Self {
            gram: identity.clone(),
            solved: identity,
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

    /// `H⁻¹`, the solved chart of the carried Gram.
    pub fn solved(&self) -> ExactRatMatrix {
        rows_matrix(&self.solved)
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

    /// **The carried prox step** over a window's samples (Lean `HNN/Normal.normal_prox_step` at
    /// the carried operands, `HNN/LatticeDeposit.carry`): `ΔH = Σ w f fᵀ` carried onto `H` gives
    /// `H'`; `ΔW = γ Σ w g (H'⁻¹ f)ᵀ`, so `(W + ΔW) H' = W H' + γ Σ w g fᵀ` exactly; `ΔW` is carried
    /// onto `W`, each at the budgeted carry `at` of the locus's deposit (its residuals staged there).
    /// `H'⁻¹` follows by exact rank-one (Sherman–Morrison) solves when `H'` took `ΔH` exactly
    /// (`q·2^(−L) = Δ` at every entry), and by one exact inversion otherwise; a singular carried Gram
    /// is refused.
    ///
    /// [definition; agent-inferred] **The sums are read in the integral chart**: each sample's
    /// feature, covector and reach is charted once as integers over its least common denominator
    /// (`ratio::linear::vector::integral`), each sum of rank-one terms is formed over integers and
    /// each entry normalized once (`ΔW` by `IntegralMatrix::outer_sum`, the symmetric `ΔH` on its
    /// upper triangle and mirrored), and each reach `H'⁻¹ f` is one normalized integer dot per row
    /// over the feature's support. A reduced ratio is canonical, so every value equals the termwise
    /// rational sum's (receipt: `cargo run --release -p holonics --example hnn_lattice_growth --
    /// equality chain 32 declared`, `… chain 32 normal` and `… campaign 8 declared`, on the
    /// notebook's pinned cut: at every deposit every carried entry satisfies the carry's accounting
    /// against the termwise update, and each solved chart equals its termwise Sherman–Morrison
    /// steps or the carried Gram's inverse; `research/notebook/hnn_design/README.md`). The samples'
    /// exact bits (the word's receiving reads and the
    /// ratio's covectors, thousands of bits each) made the termwise sums, several `gcd`s per term,
    /// the cost; what remains is one normalization per entry of the update, whose residual the carry
    /// releases exactly.
    pub fn deposited(
        &self,
        samples: &[Sample],
        proxy: &Rat,
        at: &mut BudgetedCarry,
    ) -> Result<Self, HnnError> {
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
        let active: Vec<(&Sample, Vec<usize>, Chart)> = samples
            .iter()
            .filter(|sample| !sample.weight.is_zero())
            .map(|sample| {
                let support: Vec<usize> =
                    (0..n).filter(|j| !sample.feature[*j].is_zero()).collect();
                (sample, support)
            })
            .filter(|(_, support)| !support.is_empty())
            .map(|(sample, support)| (sample, support, integral(&sample.feature)))
            .collect();
        if active.is_empty() {
            return Ok(self.clone());
        }
        let mut next = self.clone();
        // ΔH = Σ w f fᵀ, carried onto H.
        let gram_update = gram_sum(
            n,
            active
                .iter()
                .map(|(sample, _, feature)| (&sample.weight, feature)),
        );
        let mut gram: Vec<Rat> = self.gram.iter().flatten().cloned().collect();
        let exact = next
            .gram_carry
            .deposit_all(at, Carrier::Gram, &mut gram, &gram_update);
        next.gram = gram.chunks(n).map(<[Rat]>::to_vec).collect();
        // `H⁻¹ f` over the feature's support, one normalized integer dot per row.
        let reach = |solved: &[Vec<Rat>], support: &[usize], (values, denominator): &Chart| {
            let values: Vec<BigInt> = support.iter().map(|&j| values[j].clone()).collect();
            solved
                .iter()
                .map(|row| {
                    let row: Vec<Rat> = support.iter().map(|&j| row[j].clone()).collect();
                    row_dot(&row, &values, denominator)
                })
                .collect::<Vec<Rat>>()
        };
        // H'⁻¹ of the carried Gram.
        if exact {
            for (sample, support, feature) in &active {
                let solved = reach(&next.solved, support, feature);
                let denominator = Rat::one()
                    + &sample.weight
                        * support
                            .iter()
                            .map(|&j| &sample.feature[j] * &solved[j])
                            .sum::<Rat>();
                let factor = &sample.weight / denominator;
                for i in 0..n {
                    if solved[i].is_zero() {
                        continue;
                    }
                    let scaled = &factor * &solved[i];
                    for j in 0..n {
                        if !solved[j].is_zero() {
                            next.solved[i][j] -= &scaled * &solved[j];
                        }
                    }
                }
            }
        } else {
            next.solved = rows_matrix(&next.gram).inverse()?.to_rows();
        }
        // ΔW = γ Σ w g (H'⁻¹ f)ᵀ at the carried successor's H'⁻¹, carried onto W.
        let terms: Vec<(Rat, Chart, Chart)> = active
            .iter()
            .filter(|(sample, ..)| !sample.covector.iter().all(Zero::is_zero))
            .map(|(sample, support, feature)| {
                (
                    proxy * &sample.weight,
                    integral(&sample.covector),
                    integral(&reach(&next.solved, support, feature)),
                )
            })
            .collect();
        let map_update: Vec<Rat> = IntegralMatrix::outer_sum(
            m,
            n,
            terms
                .iter()
                .map(|(weight, covector, reach)| (weight, covector, reach)),
        )
        .to_rows()
        .into_iter()
        .flatten()
        .collect();
        let mut map = self.map.entries().to_vec();
        next.map_carry
            .deposit_all(at, Carrier::Map, &mut map, &map_update);
        next.map = flat_matrix(m, n, map)?;
        Ok(next)
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
            solved: self.solved.iter().flatten().map(bits).sum(),
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
/// once; the form is symmetric, so the lower triangle is its mirror.
fn gram_sum<'a>(n: usize, terms: impl IntoIterator<Item = (&'a Rat, &'a Chart)>) -> Vec<Rat> {
    let terms: Vec<(&Rat, &Chart, BigInt)> = terms
        .into_iter()
        .map(|(weight, feature)| (weight, feature, weight.denom() * &feature.1 * &feature.1))
        .collect();
    let denominator = terms
        .iter()
        .fold(BigInt::one(), |common, (.., scale)| lcm(&common, scale));
    let mut numerators = vec![BigInt::zero(); n * n];
    for (weight, (values, _), scale) in &terms {
        let factor = weight.numer() * (&denominator / scale);
        for i in 0..n {
            if values[i].is_zero() {
                continue;
            }
            let left = &values[i] * &factor;
            for j in i..n {
                if !values[j].is_zero() {
                    numerators[i * n + j] += &left * &values[j];
                }
            }
        }
    }
    let mut entries = vec![Rat::zero(); n * n];
    for i in 0..n {
        for j in i..n {
            let numerator = std::mem::take(&mut numerators[i * n + j]);
            if numerator.is_zero() {
                continue;
            }
            let value = Rat::new(numerator, denominator.clone());
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
/// lattice coordinate moved (`q ≠ 0`, review R5). The release is reported, never silent.
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
    /// | `E_g` on a source ring | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | `E_g^(δ)`, rank `2d_g` | `e_ρ = 0`; `a_ρ`, `b_ρ` from the sign generator | factor steps |
    /// | `R` on a receiving ring | the sign generator times ½ | normal law, `H_0 = I`, `B_0 = R_0` |
    /// | `W_c,g` | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | `W_s,g = −f fᵀ` | `f = ½I` | factor step |
    /// | slices | `u_ρ = e_ρ`, `v_ρ = e_(ρ+1)`: the skew cyclic shift | factor steps |
    /// | `q_g` | 0 (every sheet class `+1`) | the lock chart's preconditioned step |
    /// | `c_a`, `b_a`, `F_a` | `I`, `½I`, `½I` | factor steps |
    ///
    /// The sign generator's locus codes: `R` of ring `g` is kind 1; the pair port's current and
    /// earlier reads of ring `g` at the `o`-th declared offset are kind 2 and 3 with part `o`.
    ///
    /// Every initial value (0, ±½, 1, the unit vectors) lies on every lattice `L ≥ 1`, and each
    /// locus takes the field's declared lattice ([`Field::lattice`]).
    pub fn initial(field: &Field, steps: Steps, budget: u64) -> Result<Self, HnnError> {
        let lattices = field.lattices().clone();
        let a = field.alphabet();
        let receivers: BTreeSet<usize> = field.receivers().iter().map(|r| r.ring).collect();
        let rings = field
            .rings()
            .iter()
            .enumerate()
            .map(|(g, ring)| {
                let n = ring.width();
                let source = field
                    .is_source(g)
                    .then(|| ExactRatMatrix::zero(n, a).map(NormalLaw::with_prior))
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
                    .then(|| {
                        let map = ExactRatMatrix::shaped(
                            2 * a,
                            n,
                            (0..2 * a)
                                .map(|i| {
                                    (0..n)
                                        .map(|j| {
                                            declared_sign(locus_code(1, g, 0), i as u64, j as u64)
                                                * rat(1, 2)
                                        })
                                        .collect()
                                })
                                .collect(),
                        )?;
                        Ok::<_, HnnError>(NormalLaw::with_prior(map))
                    })
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
    /// of its solved charts.
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
                loci.push((Locus::ReceivingMap(g), receiving.carrier_bits()));
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

    /// The declared lattice of a learned locus.
    pub fn lattice(&self, locus: Locus) -> Result<Lattice, HnnError> {
        self.lattices
            .get(&locus)
            .copied()
            .ok_or_else(|| HnnError::Lattice { locus })
    }

    /// **Whether every retained entry lies on its locus's lattice** (Lean `run_onLattice`): the
    /// maps, factors and statistics; the solved charts are read from the carried Grams, and the
    /// remainders are the carried residuals.
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
        // One budgeted carry per locus the deposit names, at the clock it would advance it to.
        let mut strokes: BTreeMap<Locus, BudgetedCarry> = BTreeMap::new();
        for step in deposit.linear() {
            if self.released.contains(&step.locus.locus()) {
                return Err(HnnError::ReleasedLocus {
                    locus: step.locus.locus(),
                });
            }
            let law = match step.locus {
                LinearLocus::SourcePort(g) => next.rings[g].source.as_mut(),
                LinearLocus::Contrast(g) => Some(&mut next.rings[g].contrast),
                LinearLocus::Receiving(g) => next.rings[g].receiving.as_mut(),
            }
            .ok_or(HnnError::MissingSourcePort {
                ring: match step.locus {
                    LinearLocus::SourcePort(g)
                    | LinearLocus::Contrast(g)
                    | LinearLocus::Receiving(g) => g,
                },
            })?;
            let at = self.budgeted(&mut strokes, step.locus.locus())?;
            *law = law.deposited(&step.samples, &proxy, at)?;
        }
        for step in deposit.factors() {
            if self.released.contains(&step.gradient.locus()) {
                return Err(HnnError::ReleasedLocus {
                    locus: step.gradient.locus(),
                });
            }
            let at = self.budgeted(&mut strokes, step.gradient.locus())?;
            next.factor_step(step, &eta, at)?;
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
        };
        Ok((next, reading))
    }

    /// The budgeted carry of one deposit at a locus, opened at the clock the deposit would advance
    /// it to.
    fn budgeted<'a>(
        &self,
        strokes: &'a mut BTreeMap<Locus, BudgetedCarry>,
        locus: Locus,
    ) -> Result<&'a mut BudgetedCarry, HnnError> {
        Ok(match strokes.entry(locus) {
            Entry::Occupied(open) => open.into_mut(),
            Entry::Vacant(slot) => slot.insert(BudgetedCarry::new(
                self.lattice(locus)?,
                self.clock(locus) + 1,
            )),
        })
    }

    /// **One factor family's carried step** (module header): `h_x` carried to `h_x'`, then
    /// `Δx = (η_x / h_x') G_x` carried onto the family's entries.
    fn factor_step(
        &mut self,
        step: &FactorStep,
        eta: &Rat,
        at: &mut BudgetedCarry,
    ) -> Result<(), HnnError> {
        let locus = step.gradient.locus();
        let energy = &step.energy;
        match &step.gradient {
            FactorGradient::Passive { ring, gradient } => {
                let material = &mut self.rings[*ring];
                let rate = advance(
                    &mut self.carries,
                    at,
                    (locus, Carrier::PassiveScale),
                    &mut material.passive_scale,
                    energy,
                    eta,
                )?;
                material.passive = carried_matrix(
                    self.carries.entry((locus, Carrier::Passive)).or_default(),
                    at,
                    Carrier::Passive,
                    &material.passive,
                    &rate_matrix(&rate, gradient)?,
                    "a passive factor gradient",
                )?;
            }
            FactorGradient::Slices { ring, gradient } => {
                let material = &mut self.rings[*ring];
                let rate = advance(
                    &mut self.carries,
                    at,
                    (locus, Carrier::SliceScale),
                    &mut material.slice_scale,
                    energy,
                    eta,
                )?;
                let n = material.standing.len();
                let carry = self.carries.entry((locus, Carrier::Slices)).or_default();
                for (rho, ((u, v), (du, dv))) in
                    material.slices.iter_mut().zip(gradient).enumerate()
                {
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
            FactorGradient::Standing { ring, gradient } => {
                let material = &mut self.rings[*ring];
                let rate = advance(
                    &mut self.carries,
                    at,
                    (locus, Carrier::StandingScale),
                    &mut material.standing_scale,
                    energy,
                    eta,
                )?;
                let carry = self.carries.entry((locus, Carrier::Standing)).or_default();
                for (i, (x, dx)) in material.standing.iter_mut().zip(gradient).enumerate() {
                    carry.deposit(at, Carrier::Standing, i, x, &rate_times(&rate, dx));
                }
            }
            FactorGradient::PairPort {
                ring,
                offset,
                outputs,
                current,
                earlier,
            } => {
                let material = &mut self.rings[*ring];
                let rate = advance(
                    &mut self.carries,
                    at,
                    (locus, Carrier::PairScale),
                    &mut material.pair_scale,
                    energy,
                    eta,
                )?;
                let slot = material
                    .pairs
                    .iter_mut()
                    .find(|(declared, _)| declared == offset)
                    .ok_or(HnnError::Offset { offset: *offset })?;
                let mut family = |index: usize, base: &[Vec<Rat>], delta: &[Vec<Rat>]| {
                    let carrier = Carrier::Pair {
                        offset: *offset,
                        family: index,
                    };
                    carried_rows(
                        self.carries.entry((locus, carrier)).or_default(),
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
            FactorGradient::Storage { contact, gradient }
            | FactorGradient::Stiffness { contact, gradient }
            | FactorGradient::Dissipation { contact, gradient } => {
                let index = match &step.gradient {
                    FactorGradient::Storage { .. } => 0,
                    FactorGradient::Stiffness { .. } => 1,
                    _ => 2,
                };
                let material = &mut self.contacts[*contact];
                let rate = advance(
                    &mut self.carries,
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
                    self.carries
                        .entry((locus, Carrier::Factor(index)))
                        .or_default(),
                    at,
                    Carrier::Factor(index),
                    factor,
                    &rate_matrix(&rate, gradient)?,
                    "a channel factor gradient",
                )?;
            }
        }
        Ok(())
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
}
