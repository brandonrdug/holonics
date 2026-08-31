import ElementaryHolonics.Millennium.MillenniumCoupling
import ElementaryHolonics.Millennium.Pivots
import ElementaryHolonics.Millennium.MestreHeightLattice
import ElementaryHolonics.RH.WeilPositivity

/-!
# The coupling instantiated: one receiver form, four rows, actual carriers

`MillenniumCoupling` proves the shared theorems for a `ReceiverForm` — positive, definite,
coercive, the null cone a subspace, the gap free in finite dimensions, positivity transported
along realizations — and its six-row table names the form each Millennium row is asking about.
Until now the table was prose: no Navier–Stokes, Riemann, or Birch–Swinnerton-Dyer file imported
the coupling.  This file instantiates the form on actual carriers from four rows and lets the
shared theorems do the work.

* **The constructor.**  `matrixForm A hA` is the receiver form of a symmetric real matrix on the
  Euclidean carrier, with `matrixForm_reading`: the diagonal reading is the quadratic
  `Σᵢⱼ Aᵢⱼ vᵢ vⱼ`.
* **Riemann — the Gram of the spectral readings.**  `gramForm w` is the Gram form of any finite
  family of readings `w : Fin n → carrier`; its reading is `‖Σ cᵢ wᵢ‖²`, so it is positive, and it
  is definite exactly when the readings are linearly independent — the coupling's
  *definite ⟺ separating* on the nose (`gramForm_definite_iff_linearIndependent`).  With
  `weilReadings` — the readings `√m_ρ · ĝᵢ(γ_ρ)` of a family of Weil squares at finitely many
  zeros — the Gram entry is `Σ_ρ m_ρ ĝᵢ(γ_ρ) ĝⱼ(γ_ρ)`, the truncated zero receiver of
  `RH.WeilPositivity` on the pair, which under RH is the nonnegative real that theorem returns.
  The `12 × 12` Gram the exact driver measured from the primes is this form.
* **Navier–Stokes — the dissipation.**  `stokesForm k` is `Σ kᵢ² vᵢ²` on a finite family of
  Fourier modes: the Stokes Dirichlet form.  With every mode of frequency at least one it is
  coercive with gap exactly `1` (`stokesForm_coercive`): the row's "dissipation is coercive" is a
  theorem on the mode carrier, and the gap is the first mode.  The transport term is the
  antisymmetric part the coupling already proved invisible.
* **Yang–Mills — the transfer.**  `transferForm u` is `LatticeNet`'s single-link temporal coupling
  `!![1, u; u, 1]` as a receiver form: coercive with gap `1 − |u|` for `|u| < 1`
  (`transferForm_coercive`), with the null direction `(1, −1)` at `u = 1` — the vacuum in the
  radical, so no gap there (`transferForm_not_coercive_at_one`) — and not positive at `u = 2`
  (`transferForm_not_positive_at_two`): the sign moves with the coupling, which is the can-fail
  control.
* **Birch–Swinnerton-Dyer — the height.**  `mestreForm` is the exact rank-12 Shioda height Gram of
  the Mestre K3 family as a receiver form; positive and definite from the sum of twelve squares,
  hence coercive by `theGapIsFreeInFiniteDimensions`: the regulator lattice has a gap.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.RealizedMillenniumForms

open Soma.Holonics.Millennium.MillenniumCoupling
open Finset

/-- The Euclidean carrier on `n` coordinates. -/
abbrev Carrier (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## The constructor: a symmetric matrix as a receiver form -/

/-- The linear map `v ↦ A v` on the Euclidean carrier. -/
def matrixMap {n : ℕ} (A : Fin n → Fin n → ℝ) : Carrier n →ₗ[ℝ] Carrier n where
  toFun x := WithLp.toLp 2 (fun i => ∑ j, A i j * x.ofLp j)
  map_add' := by
    intro x y
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext i
    simp [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem matrixMap_apply {n : ℕ} (A : Fin n → Fin n → ℝ) (x : Carrier n) (i : Fin n) :
    (matrixMap A x).ofLp i = ∑ j, A i j * x.ofLp j := rfl

/-- [definition] The receiver form of a symmetric coefficient array. -/
def matrixForm {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    ReceiverForm (Carrier n) where
  T := LinearMap.toContinuousLinearMap (matrixMap A)
  selfAdjoint := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [LinearMap.coe_toContinuousLinearMap', matrixMap_apply, RCLike.inner_apply,
      conj_trivial]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA i j]
    ring

/-- [proved-derived; formal-checked] The diagonal reading of a matrix form is its quadratic. -/
theorem matrixForm_reading {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (v : Carrier n) :
    (matrixForm A hA).B v v = ∑ i, ∑ j, A i j * v.ofLp i * v.ofLp j := by
  rw [ReceiverForm.B, PiLp.inner_apply]
  simp only [matrixForm, LinearMap.coe_toContinuousLinearMap', matrixMap_apply, RCLike.inner_apply,
    conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared Euclidean norm is the coordinate sum of squares. -/
theorem norm_sq_carrier {n : ℕ} (v : Carrier n) : ‖v‖ ^ 2 = ∑ i, v.ofLp i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, sq_abs]

/-! ## Riemann: the Gram of the spectral readings -/

/-- [definition] The Gram form of a finite family of readings. -/
def gramForm {n m : ℕ} (w : Fin n → Carrier m) : ReceiverForm (Carrier n) :=
  matrixForm (fun i j => inner ℝ (w i) (w j)) (fun i j => real_inner_comm (w j) (w i))

/-- [proved-derived; formal-checked] The Gram reading is the squared norm of the realized
combination: the form is a pullback of the anchor along `c ↦ Σ cᵢ wᵢ`. -/
theorem gramForm_reading {n m : ℕ} (w : Fin n → Carrier m) (c : Carrier n) :
    (gramForm w).B c c = ‖∑ i, c.ofLp i • w i‖ ^ 2 := by
  rw [gramForm, matrixForm_reading, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- [proved-derived; formal-checked] Every Gram form is positive. -/
theorem gramForm_positive {n m : ℕ} (w : Fin n → Carrier m) : (gramForm w).IsPositive := by
  intro c
  rw [gramForm_reading]
  positivity

/-- [proved-derived; formal-checked] **Definite exactly when the readings separate**: the Gram
form is definite iff the reading family is linearly independent. -/
theorem gramForm_definite_iff_linearIndependent {n m : ℕ} (w : Fin n → Carrier m) :
    (gramForm w).IsDefinite ↔ LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hdef g hg i
    have hzero : (gramForm w).B (WithLp.toLp 2 g) (WithLp.toLp 2 g) = 0 := by
      rw [gramForm_reading]
      simp only [WithLp.ofLp_toLp]
      rw [hg]
      simp
    have := hdef _ hzero
    have := congrArg (fun x : Carrier n => x.ofLp i) this
    simpa using this
  · intro hli c hc
    rw [gramForm_reading] at hc
    have hsum : ∑ i, c.ofLp i • w i = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc
      exact norm_eq_zero.mp this
    ext i
    exact hli (fun i => c.ofLp i) hsum i

/-- [definition] The readings of a family of Weil squares at finitely many zeros: reading `i` at
zero `ρ` is `√m_ρ · ĝᵢ(γ_ρ)`, so that the Gram entries are the truncated zero receivers. -/
def weilReadings {n m : ℕ} (mult : Fin m → ℝ) (gamma : Fin m → ℝ) (g : Fin n → ℝ → ℝ) :
    Fin n → Carrier m :=
  fun i => WithLp.toLp 2 (fun ρ => Real.sqrt (mult ρ) * g i (gamma ρ))

/-- [proved-derived; formal-checked] The Gram entry of two Weil readings is the multiplicity-weighted
spectral sum `Σ_ρ m_ρ ĝᵢ(γ_ρ) ĝⱼ(γ_ρ)` — the truncated zero receiver on the pair. -/
theorem weilReadings_gram {n m : ℕ} (mult : Fin m → ℝ) (hmult : ∀ ρ, 0 ≤ mult ρ)
    (gamma : Fin m → ℝ) (g : Fin n → ℝ → ℝ) (i j : Fin n) :
    inner ℝ (weilReadings mult gamma g i) (weilReadings mult gamma g j) =
      ∑ ρ, mult ρ * g i (gamma ρ) * g j (gamma ρ) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [weilReadings, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  have h := Real.mul_self_sqrt (hmult ρ)
  linear_combination (g i (gamma ρ) * g j (gamma ρ)) * h

/-! ## Navier–Stokes: the Stokes dissipation on a family of modes -/

/-- [definition] The Stokes Dirichlet form `Σ kᵢ² vᵢ²` on modes of frequency `kᵢ`. -/
def stokesForm {n : ℕ} (k : Fin n → ℝ) : ReceiverForm (Carrier n) :=
  matrixForm (fun i j => if i = j then k i ^ 2 else 0) (by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h])

theorem stokesForm_reading {n : ℕ} (k : Fin n → ℝ) (v : Carrier n) :
    (stokesForm k).B v v = ∑ i, k i ^ 2 * v.ofLp i ^ 2 := by
  rw [stokesForm, matrixForm_reading]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hji
    simp [Ne.symm hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- [proved-derived; formal-checked] **The dissipation is coercive and the gap is the first
mode**: with every mode of frequency at least one, the Stokes form has gap `1`. -/
theorem stokesForm_coercive {n : ℕ} (k : Fin n → ℝ) (hk : ∀ i, 1 ≤ k i ^ 2) :
    (stokesForm k).IsCoercive := by
  refine ⟨1, one_pos, ?_⟩
  intro v
  rw [stokesForm_reading, norm_sq_carrier, one_mul]
  apply Finset.sum_le_sum
  intro i _
  have := hk i
  nlinarith [sq_nonneg (v.ofLp i)]

/-! ## Yang–Mills: the single-link transfer coupling -/

/-- [definition] `LatticeNet`'s temporal coupling `!![1, u; u, 1]` as a receiver form. -/
def transferForm (u : ℝ) : ReceiverForm (Carrier 2) :=
  matrixForm (fun i j => if i = j then 1 else u) (by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h])

theorem transferForm_reading (u : ℝ) (v : Carrier 2) :
    (transferForm u).B v v = v.ofLp 0 ^ 2 + 2 * u * (v.ofLp 0 * v.ofLp 1) + v.ofLp 1 ^ 2 := by
  rw [transferForm, matrixForm_reading, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp
  ring

/-- [proved-derived; formal-checked] **The transfer coupling has gap `1 − |u|` for `|u| < 1`.** -/
theorem transferForm_coercive (u : ℝ) (hu : |u| < 1) : (transferForm u).IsCoercive := by
  refine ⟨1 - |u|, by linarith, ?_⟩
  intro v
  rw [transferForm_reading, norm_sq_carrier, Fin.sum_univ_two]
  have h1 : 2 * u * (v.ofLp 0 * v.ofLp 1) ≥ -(|u| * (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2)) := by
    have hab : |v.ofLp 0 * v.ofLp 1| ≤ (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|v.ofLp 0| - |v.ofLp 1|), sq_abs (v.ofLp 0), sq_abs (v.ofLp 1),
        abs_nonneg (v.ofLp 0), abs_nonneg (v.ofLp 1)]
    have := abs_mul u (v.ofLp 0 * v.ofLp 1)
    have hle := neg_abs_le (u * (v.ofLp 0 * v.ofLp 1))
    have hprod : |u| * |v.ofLp 0 * v.ofLp 1| ≤ |u| * ((v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hab (abs_nonneg u)
    nlinarith [this, hle, hprod]
  nlinarith [h1, abs_nonneg u, sq_nonneg (v.ofLp 0), sq_nonneg (v.ofLp 1)]

/-- The balanced-opposite direction `(1, −1)`. -/
def antiDiagonal : Carrier 2 := WithLp.toLp 2 ![1, -1]

theorem antiDiagonal_ne_zero : antiDiagonal ≠ 0 := by
  intro h
  have := congrArg (fun x : Carrier 2 => x.ofLp 0) h
  simp [antiDiagonal] at this

/-- [proved-derived; formal-checked] **At `u = 1` the balanced direction is in the null cone**, so
the vacuum lies in the radical and the form has no gap: `theGapForcesDefiniteness` refuses it. -/
theorem transferForm_not_coercive_at_one : ¬ (transferForm 1).IsCoercive := by
  intro hcoer
  have hdef := (transferForm 1).theGapForcesDefiniteness hcoer
  have hnull : (transferForm 1).B antiDiagonal antiDiagonal = 0 := by
    rw [transferForm_reading]
    simp [antiDiagonal]
    norm_num
  exact antiDiagonal_ne_zero (hdef antiDiagonal hnull)

/-- [proved-derived; formal-checked] **At `u = 2` the sign moves**: the reading on the balanced
direction is `−2`, so the form is not positive — the can-fail control of `LatticeNet` in the
coupling's own vocabulary. -/
theorem transferForm_not_positive_at_two : ¬ (transferForm 2).IsPositive := by
  intro hpos
  have := hpos antiDiagonal
  rw [transferForm_reading] at this
  simp [antiDiagonal] at this
  norm_num at this


/-! ## Birch–Swinnerton-Dyer: the rank-12 height Gram of the Mestre K3 family -/

/-- The exact Shioda height Gram on the twelve independent sections (`MestreHeightLattice`),
over `ℝ`. -/
def mestreGram : Fin 12 → Fin 12 → ℝ :=
  ![![(3 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), (3/2 : ℝ)],
    ![(1 : ℝ), (4 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ)],
    ![(2 : ℝ), (3 : ℝ), (5 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (3/2 : ℝ)],
    ![(1 : ℝ), (2 : ℝ), (2 : ℝ), (4 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ)],
    ![(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), (5 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (3/2 : ℝ)],
    ![(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (4 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ)],
    ![(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), (5 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (5/2 : ℝ)],
    ![(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (4 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ)],
    ![(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), (5 : ℝ), (2 : ℝ), (3 : ℝ), (3/2 : ℝ)],
    ![(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), (4 : ℝ), (3 : ℝ), (1 : ℝ)],
    ![(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), (5 : ℝ), (5/2 : ℝ)],
    ![(3/2 : ℝ), (2 : ℝ), (3/2 : ℝ), (1 : ℝ), (3/2 : ℝ), (2 : ℝ), (5/2 : ℝ), (1 : ℝ), (3/2 : ℝ), (1 : ℝ), (5/2 : ℝ), (13/4 : ℝ)]]

set_option maxHeartbeats 4000000 in
theorem mestreGram_symm : ∀ i j, mestreGram i j = mestreGram j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The height form over `ℝ`, the same polynomial as `MestreHeightLattice.Q`. -/
def QR (x : Fin 12 → ℝ) : ℝ :=
  (3 : ℝ) * x 0 * x 0 + (1 : ℝ) * x 0 * x 1 + (2 : ℝ) * x 0 * x 2 + (1 : ℝ) * x 0 * x 3 + (2 : ℝ) * x 0 * x 4 + (1 : ℝ) * x 0 * x 5 + (2 : ℝ) * x 0 * x 6 + (1 : ℝ) * x 0 * x 7 + (2 : ℝ) * x 0 * x 8 + (1 : ℝ) * x 0 * x 9 + (2 : ℝ) * x 0 * x 10 + (3/2 : ℝ) * x 0 * x 11 + (1 : ℝ) * x 1 * x 0 + (4 : ℝ) * x 1 * x 1 + (3 : ℝ) * x 1 * x 2 + (2 : ℝ) * x 1 * x 3 + (2 : ℝ) * x 1 * x 4 + (2 : ℝ) * x 1 * x 5 + (2 : ℝ) * x 1 * x 6 + (2 : ℝ) * x 1 * x 7 + (2 : ℝ) * x 1 * x 8 + (2 : ℝ) * x 1 * x 9 + (2 : ℝ) * x 1 * x 10 + (2 : ℝ) * x 1 * x 11 + (2 : ℝ) * x 2 * x 0 + (3 : ℝ) * x 2 * x 1 + (5 : ℝ) * x 2 * x 2 + (2 : ℝ) * x 2 * x 3 + (3 : ℝ) * x 2 * x 4 + (2 : ℝ) * x 2 * x 5 + (3 : ℝ) * x 2 * x 6 + (2 : ℝ) * x 2 * x 7 + (3 : ℝ) * x 2 * x 8 + (2 : ℝ) * x 2 * x 9 + (3 : ℝ) * x 2 * x 10 + (3/2 : ℝ) * x 2 * x 11 + (1 : ℝ) * x 3 * x 0 + (2 : ℝ) * x 3 * x 1 + (2 : ℝ) * x 3 * x 2 + (4 : ℝ) * x 3 * x 3 + (3 : ℝ) * x 3 * x 4 + (2 : ℝ) * x 3 * x 5 + (2 : ℝ) * x 3 * x 6 + (2 : ℝ) * x 3 * x 7 + (2 : ℝ) * x 3 * x 8 + (2 : ℝ) * x 3 * x 9 + (2 : ℝ) * x 3 * x 10 + (1 : ℝ) * x 3 * x 11 + (2 : ℝ) * x 4 * x 0 + (2 : ℝ) * x 4 * x 1 + (3 : ℝ) * x 4 * x 2 + (3 : ℝ) * x 4 * x 3 + (5 : ℝ) * x 4 * x 4 + (2 : ℝ) * x 4 * x 5 + (3 : ℝ) * x 4 * x 6 + (2 : ℝ) * x 4 * x 7 + (3 : ℝ) * x 4 * x 8 + (2 : ℝ) * x 4 * x 9 + (3 : ℝ) * x 4 * x 10 + (3/2 : ℝ) * x 4 * x 11 + (1 : ℝ) * x 5 * x 0 + (2 : ℝ) * x 5 * x 1 + (2 : ℝ) * x 5 * x 2 + (2 : ℝ) * x 5 * x 3 + (2 : ℝ) * x 5 * x 4 + (4 : ℝ) * x 5 * x 5 + (3 : ℝ) * x 5 * x 6 + (2 : ℝ) * x 5 * x 7 + (2 : ℝ) * x 5 * x 8 + (2 : ℝ) * x 5 * x 9 + (2 : ℝ) * x 5 * x 10 + (2 : ℝ) * x 5 * x 11 + (2 : ℝ) * x 6 * x 0 + (2 : ℝ) * x 6 * x 1 + (3 : ℝ) * x 6 * x 2 + (2 : ℝ) * x 6 * x 3 + (3 : ℝ) * x 6 * x 4 + (3 : ℝ) * x 6 * x 5 + (5 : ℝ) * x 6 * x 6 + (2 : ℝ) * x 6 * x 7 + (3 : ℝ) * x 6 * x 8 + (2 : ℝ) * x 6 * x 9 + (3 : ℝ) * x 6 * x 10 + (5/2 : ℝ) * x 6 * x 11 + (1 : ℝ) * x 7 * x 0 + (2 : ℝ) * x 7 * x 1 + (2 : ℝ) * x 7 * x 2 + (2 : ℝ) * x 7 * x 3 + (2 : ℝ) * x 7 * x 4 + (2 : ℝ) * x 7 * x 5 + (2 : ℝ) * x 7 * x 6 + (4 : ℝ) * x 7 * x 7 + (3 : ℝ) * x 7 * x 8 + (2 : ℝ) * x 7 * x 9 + (2 : ℝ) * x 7 * x 10 + (1 : ℝ) * x 7 * x 11 + (2 : ℝ) * x 8 * x 0 + (2 : ℝ) * x 8 * x 1 + (3 : ℝ) * x 8 * x 2 + (2 : ℝ) * x 8 * x 3 + (3 : ℝ) * x 8 * x 4 + (2 : ℝ) * x 8 * x 5 + (3 : ℝ) * x 8 * x 6 + (3 : ℝ) * x 8 * x 7 + (5 : ℝ) * x 8 * x 8 + (2 : ℝ) * x 8 * x 9 + (3 : ℝ) * x 8 * x 10 + (3/2 : ℝ) * x 8 * x 11 + (1 : ℝ) * x 9 * x 0 + (2 : ℝ) * x 9 * x 1 + (2 : ℝ) * x 9 * x 2 + (2 : ℝ) * x 9 * x 3 + (2 : ℝ) * x 9 * x 4 + (2 : ℝ) * x 9 * x 5 + (2 : ℝ) * x 9 * x 6 + (2 : ℝ) * x 9 * x 7 + (2 : ℝ) * x 9 * x 8 + (4 : ℝ) * x 9 * x 9 + (3 : ℝ) * x 9 * x 10 + (1 : ℝ) * x 9 * x 11 + (2 : ℝ) * x 10 * x 0 + (2 : ℝ) * x 10 * x 1 + (3 : ℝ) * x 10 * x 2 + (2 : ℝ) * x 10 * x 3 + (3 : ℝ) * x 10 * x 4 + (2 : ℝ) * x 10 * x 5 + (3 : ℝ) * x 10 * x 6 + (2 : ℝ) * x 10 * x 7 + (3 : ℝ) * x 10 * x 8 + (3 : ℝ) * x 10 * x 9 + (5 : ℝ) * x 10 * x 10 + (5/2 : ℝ) * x 10 * x 11 + (3/2 : ℝ) * x 11 * x 0 + (2 : ℝ) * x 11 * x 1 + (3/2 : ℝ) * x 11 * x 2 + (1 : ℝ) * x 11 * x 3 + (3/2 : ℝ) * x 11 * x 4 + (2 : ℝ) * x 11 * x 5 + (5/2 : ℝ) * x 11 * x 6 + (1 : ℝ) * x 11 * x 7 + (3/2 : ℝ) * x 11 * x 8 + (1 : ℝ) * x 11 * x 9 + (5/2 : ℝ) * x 11 * x 10 + (13/4 : ℝ) * x 11 * x 11

def L0 (x : Fin 12 → ℝ) : ℝ := x 0 + (1/3 : ℝ) * x 1 + (2/3 : ℝ) * x 2 + (1/3 : ℝ) * x 3 + (2/3 : ℝ) * x 4 + (1/3 : ℝ) * x 5 + (2/3 : ℝ) * x 6 + (1/3 : ℝ) * x 7 + (2/3 : ℝ) * x 8 + (1/3 : ℝ) * x 9 + (2/3 : ℝ) * x 10 + (1/2 : ℝ) * x 11
def L1 (x : Fin 12 → ℝ) : ℝ := x 1 + (7/11 : ℝ) * x 2 + (5/11 : ℝ) * x 3 + (4/11 : ℝ) * x 4 + (5/11 : ℝ) * x 5 + (4/11 : ℝ) * x 6 + (5/11 : ℝ) * x 7 + (4/11 : ℝ) * x 8 + (5/11 : ℝ) * x 9 + (4/11 : ℝ) * x 10 + (9/22 : ℝ) * x 11
def L2 (x : Fin 12 → ℝ) : ℝ := x 2 + (1/8 : ℝ) * x 3 + (3/8 : ℝ) * x 4 + (1/8 : ℝ) * x 5 + (3/8 : ℝ) * x 6 + (1/8 : ℝ) * x 7 + (3/8 : ℝ) * x 8 + (1/8 : ℝ) * x 9 + (3/8 : ℝ) * x 10 + (-5/24 : ℝ) * x 11
def L3 (x : Fin 12 → ℝ) : ℝ := x 3 + (13/23 : ℝ) * x 4 + (7/23 : ℝ) * x 5 + (5/23 : ℝ) * x 6 + (7/23 : ℝ) * x 7 + (5/23 : ℝ) * x 8 + (7/23 : ℝ) * x 9 + (5/23 : ℝ) * x 10 + (-1/23 : ℝ) * x 11
def L4 (x : Fin 12 → ℝ) : ℝ := x 4 + (1/15 : ℝ) * x 5 + (4/15 : ℝ) * x 6 + (1/15 : ℝ) * x 7 + (4/15 : ℝ) * x 8 + (1/15 : ℝ) * x 9 + (4/15 : ℝ) * x 10 + (1/10 : ℝ) * x 11
def L5 (x : Fin 12 → ℝ) : ℝ := x 5 + (7/13 : ℝ) * x 6 + (3/13 : ℝ) * x 7 + (2/13 : ℝ) * x 8 + (3/13 : ℝ) * x 9 + (2/13 : ℝ) * x 10 + (9/26 : ℝ) * x 11
def L6 (x : Fin 12 → ℝ) : ℝ := x 6 + (1/24 : ℝ) * x 7 + (5/24 : ℝ) * x 8 + (1/24 : ℝ) * x 9 + (5/24 : ℝ) * x 10 + (1/3 : ℝ) * x 11
def L7 (x : Fin 12 → ℝ) : ℝ := x 7 + (31/59 : ℝ) * x 8 + (11/59 : ℝ) * x 9 + (7/59 : ℝ) * x 10 + (-8/59 : ℝ) * x 11
def L8 (x : Fin 12 → ℝ) : ℝ := x 8 + (1/35 : ℝ) * x 9 + (6/35 : ℝ) * x 10 + (1/210 : ℝ) * x 11
def L9 (x : Fin 12 → ℝ) : ℝ := x 9 + (43/83 : ℝ) * x 10 + (-19/166 : ℝ) * x 11
def L10 (x : Fin 12 → ℝ) : ℝ := x 10 + (7/12 : ℝ) * x 11
def L11 (x : Fin 12 → ℝ) : ℝ := x 11

set_option maxHeartbeats 4000000 in
/-- The twelve-square identity over `ℝ`. -/
theorem QR_sumOfSquares (x : Fin 12 → ℝ) :
    QR x = (3 : ℝ) * L0 x ^ 2 + (11/3 : ℝ) * L1 x ^ 2 + (24/11 : ℝ) * L2 x ^ 2 + (23/8 : ℝ) * L3 x ^ 2 + (45/23 : ℝ) * L4 x ^ 2 + (13/5 : ℝ) * L5 x ^ 2 + (24/13 : ℝ) * L6 x ^ 2 + (59/24 : ℝ) * L7 x ^ 2 + (105/59 : ℝ) * L8 x ^ 2 + (83/35 : ℝ) * L9 x ^ 2 + (144/83 : ℝ) * L10 x ^ 2 + (7/12 : ℝ) * L11 x ^ 2 := by
  simp only [QR, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11]
  ring

theorem QR_nonneg (x : Fin 12 → ℝ) : 0 ≤ QR x := by
  rw [QR_sumOfSquares]
  have s0 := sq_nonneg (L0 x)
  have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x)
  have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x)
  have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x)
  have s7 := sq_nonneg (L7 x)
  have s8 := sq_nonneg (L8 x)
  have s9 := sq_nonneg (L9 x)
  have s10 := sq_nonneg (L10 x)
  have s11 := sq_nonneg (L11 x)
  linarith

set_option maxHeartbeats 4000000 in
theorem QR_anisotropic (x : Fin 12 → ℝ) (h : QR x = 0) : x = 0 := by
  rw [QR_sumOfSquares] at h
  have s0 := sq_nonneg (L0 x)
  have s1 := sq_nonneg (L1 x)
  have s2 := sq_nonneg (L2 x)
  have s3 := sq_nonneg (L3 x)
  have s4 := sq_nonneg (L4 x)
  have s5 := sq_nonneg (L5 x)
  have s6 := sq_nonneg (L6 x)
  have s7 := sq_nonneg (L7 x)
  have s8 := sq_nonneg (L8 x)
  have s9 := sq_nonneg (L9 x)
  have s10 := sq_nonneg (L10 x)
  have s11 := sq_nonneg (L11 x)
  have h11 : L11 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h10 : L10 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h9 : L9 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h8 : L8 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h7 : L7 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h6 : L6 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h5 : L5 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h4 : L4 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h3 : L3 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h2 : L2 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h1 : L1 x = 0 := sq_eq_zero_iff.mp (by linarith)
  have h0 : L0 x = 0 := sq_eq_zero_iff.mp (by linarith)
  unfold L0 at h0
  unfold L1 at h1
  unfold L2 at h2
  unfold L3 at h3
  unfold L4 at h4
  unfold L5 at h5
  unfold L6 at h6
  unfold L7 at h7
  unfold L8 at h8
  unfold L9 at h9
  unfold L10 at h10
  unfold L11 at h11
  have c11 : x 11 = 0 := by linarith
  have c10 : x 10 = 0 := by linarith
  have c9 : x 9 = 0 := by linarith
  have c8 : x 8 = 0 := by linarith
  have c7 : x 7 = 0 := by linarith
  have c6 : x 6 = 0 := by linarith
  have c5 : x 5 = 0 := by linarith
  have c4 : x 4 = 0 := by linarith
  have c3 : x 3 = 0 := by linarith
  have c2 : x 2 = 0 := by linarith
  have c1 : x 1 = 0 := by linarith
  have c0 : x 0 = 0 := by linarith
  funext i
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

/-- [definition] **The height form as a receiver form.** -/
def mestreForm : ReceiverForm (Carrier 12) := matrixForm mestreGram mestreGram_symm

set_option maxHeartbeats 4000000 in
theorem mestreForm_reading (v : Carrier 12) : mestreForm.B v v = QR v.ofLp := by
  rw [mestreForm, matrixForm_reading]
  simp [Fin.sum_univ_succ, mestreGram, QR]
  ring

theorem mestreForm_positive : mestreForm.IsPositive := by
  intro v
  rw [mestreForm_reading]
  exact QR_nonneg _

theorem mestreForm_definite : mestreForm.IsDefinite := by
  intro v hv
  rw [mestreForm_reading] at hv
  have := QR_anisotropic _ hv
  ext i
  have := congrFun this i
  simpa using this

/-- [proved-derived; formal-checked] **The regulator lattice has a gap**: the rank-12 height form is
coercive, by the coupling's `theGapIsFreeInFiniteDimensions`. -/
theorem mestreForm_coercive : mestreForm.IsCoercive :=
  mestreForm.theGapIsFreeInFiniteDimensions mestreForm_positive mestreForm_definite

section AuditHeight

#print axioms mestreForm_coercive

end AuditHeight

section Audit

#print axioms matrixForm_reading
#print axioms gramForm_definite_iff_linearIndependent
#print axioms weilReadings_gram
#print axioms stokesForm_coercive
#print axioms transferForm_coercive
#print axioms transferForm_not_coercive_at_one
#print axioms transferForm_not_positive_at_two

end Audit

end Soma.Holonics.Millennium.RealizedMillenniumForms
