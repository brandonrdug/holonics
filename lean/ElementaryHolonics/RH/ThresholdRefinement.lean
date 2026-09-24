import Mathlib
import ElementaryHolonics.RH.DeBruijnSeal
import ElementaryHolonics.RH.HeatFlowOfPolynomials

/-!
# Threshold refinement and the quadratic sharpness witness

The value `1/8` is the first Gaussian/strip time supplied by the `N²` average:
`cosh (u/(2N)) ^ N² → exp (u²/8)`.  It is an upper bound obtained by taking an
infimum over the actual `seamTimes`; it is not an iteration rule for the threshold.
The conditional refinement below records the additional rule that would be needed
to descend the seam times to zero.
-/

noncomputable section

namespace Soma.Holonics.RH.ThresholdRefinement

open Set Filter Topology Complex
open Polynomial
open Soma.Holonics.RH.RealZeroTimes
open Soma.Holonics.RH.DeBruijnLimit
open Soma.Holonics.RH.DeBruijnSeal
open Soma.Holonics.RH.LinePreservation

/-! ## A genuine conditional descent on the actual seam set -/

/-- Every positive seam time can be halved, as an additional geometric closure law. -/
def HalfClosed : Prop := ∀ ⦃τ : ℝ⦄, τ ∈ seamTimes → 0 < τ → τ / 2 ∈ seamTimes

theorem half_iter_mem (hhalf : HalfClosed) :
    ∀ n : ℕ, (1 / 8 : ℝ) / (2 : ℝ) ^ n ∈ seamTimes := by
  intro n
  induction n with
  | zero => norm_num [eighth_mem_seamTimes]
  | succ n ih =>
      have hpos : 0 < (1 / 8 : ℝ) / (2 : ℝ) ^ n := by positivity
      simpa [pow_succ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        hhalf ih hpos

/-- If the actual seam set is closed under positive halving, then its threshold is zero,
and hence the Riemann Hypothesis holds by the existing threshold equivalence. -/
theorem lambda_eq_zero_of_halfClosed (hhalf : HalfClosed) : Λ_DN = 0 := by
  have hle : Λ_DN ≤ 0 := by
    have hlim : Tendsto (fun n : ℕ => (1 / 8 : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [div_eq_mul_inv, one_div] using hpow.const_mul (1 / 8 : ℝ)
    have hclosed : IsClosed (Ici Λ_DN) := isClosed_Ici
    have hmem : ∀ n : ℕ, (1 / 8 : ℝ) / (2 : ℝ) ^ n ∈ Ici Λ_DN := by
      intro n
      exact (seamTimes_eq_Ici ▸ half_iter_mem hhalf n)
    have : (0 : ℝ) ∈ Ici Λ_DN := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
    exact this
  exact le_antisymm hle Soma.Holonics.RH.DescentZeros.Λ_DN_nonneg

theorem riemannHypothesis_of_halfClosed (hhalf : HalfClosed) : RiemannHypothesis := by
  exact DeBruijnSeal.riemannHypothesis_iff_Λ_DN_eq.mpr (lambda_eq_zero_of_halfClosed hhalf)

/-! ## The direct square refinement -/

/-- Squaring is required only on the positive unit part of the actual seam set. -/
def SquareClosed : Prop :=
  ∀ ⦃τ : ℝ⦄, τ ∈ seamTimes → 0 < τ → τ < 1 → τ ^ 2 ∈ seamTimes

theorem squareClosed_of_RH (hRH : RiemannHypothesis) : SquareClosed := by
  rw [← zero_mem_iff] at hRH
  intro τ hτ hτpos hτlt
  exact seamTimes_upset hRH (by positivity)

/-- On the known interval `Λ_DN ∈ [0,1/8]`, square closure is equivalent to RH.
The proof applies the closure rule directly to the threshold `Λ_DN`; if it were positive,
then `Λ_DN² < Λ_DN` would contradict its infimality. -/
theorem squareClosed_iff_RH : SquareClosed ↔ RiemannHypothesis := by
  constructor
  · intro hs
    have hmem : Λ_DN ∈ seamTimes :=
      isClosed_seamTimes.csInf_mem ⟨_, eighth_mem_seamTimes⟩ bddBelow_seamTimes
    by_cases hzero : Λ_DN = 0
    · exact DeBruijnSeal.riemannHypothesis_iff_Λ_DN_eq.mpr hzero
    · have hpos : 0 < Λ_DN := lt_of_le_of_ne
        Soma.Holonics.RH.DescentZeros.Λ_DN_nonneg (Ne.symm hzero)
      have hlt : Λ_DN < 1 := lt_of_le_of_lt Λ_DN_le_eighth (by norm_num)
      have hsq : Λ_DN ^ 2 ∈ seamTimes := hs hmem hpos hlt
      have hle : Λ_DN ≤ Λ_DN ^ 2 := csInf_le bddBelow_seamTimes hsq
      nlinarith
  · exact squareClosed_of_RH

/-! ## Why `1/8` is sharp for the generic quadratic strip calculation -/

def quadratic (a t : ℝ) : ℂ[X] := X ^ 2 + Polynomial.C (((a ^ 2 - 2 * t : ℝ) : ℂ))

def quadraticRoot (a t : ℝ) : ℂ := I * Real.sqrt (a ^ 2 - 2 * t)

theorem heat_quadratic_zero (a t : ℝ) :
    Soma.Holonics.RH.HeatFlowOfPolynomials.heat t (quadratic a 0) = quadratic a t := by
  classical
  have hdeg : (quadratic a 0).natDegree = 2 := by
    unfold quadratic
    convert (Polynomial.natDegree_X_pow_add_C (R := ℂ) (n := 2)
      (r := ((a ^ 2 : ℝ) : ℂ))) using 1 <;> ring
  unfold Soma.Holonics.RH.HeatFlowOfPolynomials.heat
  rw [hdeg]
  have hconst : Polynomial.derivative (Polynomial.derivative (Polynomial.C (a : ℂ) ^ 2)) = 0 := by
    simp [pow_two, Polynomial.derivative_mul]
  have hconst4 : (Polynomial.derivative^[4]) (Polynomial.C (a : ℂ) ^ 2) = 0 := by
    simp [Function.iterate_succ_apply', hconst]
  simp only [quadratic]
  norm_num [Finset.sum_range_succ, Polynomial.derivative_X_pow,
    Polynomial.derivative_C, Polynomial.derivative_mul, Function.iterate_succ_apply',
    Function.iterate_zero]
  rw [hconst]
  try simp [Function.iterate_succ_apply', Polynomial.derivative_zero]
  ring_nf

theorem quadratic_eval_zero (a t : ℝ) : (quadratic a t).eval 0 = (a ^ 2 - 2 * t : ℂ) := by
  simp [quadratic]

theorem quadratic_eval_root {a t : ℝ} (h : 0 ≤ a ^ 2 - 2 * t) :
    (quadratic a t).eval (quadraticRoot a t) = 0 := by
  rw [quadratic]
  simp only [eval_add, eval_pow, eval_X, eval_C, quadraticRoot]
  have hs : (Real.sqrt (a ^ 2 - 2 * t) : ℂ) ^ 2 =
      (a ^ 2 - 2 * t : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt h]
    push_cast
    ring
  rw [mul_pow, Complex.I_sq, hs]
  push_cast
  ring

theorem quadratic_root_im_pos {a t : ℝ} (h : 0 < a ^ 2 - 2 * t) :
    0 < (quadraticRoot a t).im := by
  simp [quadraticRoot, Real.sqrt_pos.2 h]

theorem quadratic_half_eval_zero : (quadratic (1 / 2) (1 / 8)).eval 0 = (0 : ℂ) := by
  rw [quadratic_eval_zero]
  norm_num

theorem quadratic_sixteenth_eval_zero :
    (quadratic (1 / 2) (1 / 16)).eval 0 = (1 / 8 : ℂ) := by
  rw [quadratic_eval_zero]
  norm_num

theorem quadratic_thirtysecond_eval_zero :
    (quadratic (1 / 2) (1 / 32)).eval 0 = (3 / 16 : ℂ) := by
  rw [quadratic_eval_zero]
  norm_num

theorem quadratic_sixtyfourth_eval_zero :
    (quadratic (1 / 2) (1 / 64)).eval 0 = (7 / 32 : ℂ) := by
  rw [quadratic_eval_zero]
  norm_num

theorem quadratic_sixteenth_has_offReal_root :
    (quadraticRoot (1 / 2) (1 / 16)).im > 0 ∧
      (quadratic (1 / 2) (1 / 16)).eval (quadraticRoot (1 / 2) (1 / 16)) = 0 := by
  constructor
  · apply quadratic_root_im_pos
    norm_num
  · apply quadratic_eval_root
    norm_num

theorem quadratic_thirtysecond_has_offReal_root :
    (quadraticRoot (1 / 2) (1 / 32)).im > 0 ∧
      (quadratic (1 / 2) (1 / 32)).eval (quadraticRoot (1 / 2) (1 / 32)) = 0 := by
  constructor
  · apply quadratic_root_im_pos
    norm_num
  · apply quadratic_eval_root
    norm_num

theorem quadratic_sixtyfourth_has_offReal_root :
    (quadraticRoot (1 / 2) (1 / 64)).im > 0 ∧
      (quadratic (1 / 2) (1 / 64)).eval (quadraticRoot (1 / 2) (1 / 64)) = 0 := by
  constructor
  · apply quadratic_root_im_pos
    norm_num
  · apply quadratic_eval_root
    norm_num

theorem quadratic_half_eq_X_sq : quadratic (1 / 2) (1 / 8) = X ^ 2 := by
  rw [quadratic]
  congr 1
  norm_num

end Soma.Holonics.RH.ThresholdRefinement
