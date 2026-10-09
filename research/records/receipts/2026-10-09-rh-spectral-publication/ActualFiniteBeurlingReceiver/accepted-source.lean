module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false

/-!
Actual finite ordinary-Mobius receiver, on the reciprocal coordinate y=1/x.
The physical step is chi_(0,1] on x>0. Ordinary fractional part is retained
at integers. No Mellin identity, norm convergence, RH, or Mertens estimate
is a premise. PREPARED SOURCE: native acceptance is a separate receipt.

The consumer is the Nyman-Beurling residual, not another RH-equivalence
port. The cached finite convolution owner used by the Farey arithmetic
join supplies the exact floor partition. Its consequence is a physical
tail down to x=1/N, not merely the elementary tail beyond x=1.
-/

noncomputable section
namespace Holonics.Zeta.ActualFiniteBeurlingReceiver

open Finset
open scoped Classical BigOperators

def harmonicMobius (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / n

def floorRead (N : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) * (⌊y / n⌋₊ : ℝ)

def phaseRead (N : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) * Int.fract (y / n)

def reciprocalResidual (N : ℕ) (y : ℝ) : ℝ :=
  (if 1 ≤ y then 1 else 0) + phaseRead N y

/-- On x>0 this is chi_(0,1](x) + sum_(n<=N) mu(n){1/(nx)}. -/
def physicalResidual (N : ℕ) (x : ℝ) : ℝ :=
  reciprocalResidual N x⁻¹

/-- The reciprocal chart is joined to the actual fractional-part receiver,
including the x=1 endpoint. There is no abstract surrogate source. -/
theorem actual_nb_receiver (N : ℕ) {x : ℝ} (hx : 0 < x) :
    physicalResidual N x = (if x ≤ 1 then 1 else 0) +
      ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) *
        Int.fract (1 / ((n : ℝ) * x)) := by
  have hstep : (1 : ℝ) ≤ x⁻¹ ↔ x ≤ 1 := by
    rw [inv_eq_one_div, le_div_iff₀ hx]
    simp
  unfold physicalResidual reciprocalResidual phaseRead
  simp only [hstep]
  congr 1
  apply sum_congr rfl
  intro n _
  have he : x⁻¹ / (n : ℝ) = 1 / ((n : ℝ) * x) := by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [he]

/-- Exact finite divisor partition, with the empty N=0 case retained. -/
theorem actual_mobius_floor_partition (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ArithmeticFunction.moebius n * (N / n : ℕ)) =
      if N = 0 then (0 : ℤ) else 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℤ) N
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  by_cases hN : N = 0
  · simp [hN]
  · have hmem : (1 : ℕ) ∈ Ioc 0 N := by
      simp only [mem_Ioc]
      omega
    simp [ArithmeticFunction.one_apply, hmem, hN]

/-- Every actual floor address through floor(y) is present; all later ones
are zero. The cutoff and the pointwise step endpoint are explicit. -/
theorem actual_truncated_floor_partition (N : ℕ) {y : ℝ}
    (hy : 0 ≤ y) (hcut : ⌊y⌋₊ ≤ N) :
    floorRead N y = if 1 ≤ y then 1 else 0 := by
  unfold floorRead
  simp_rw [Nat.floor_div_natCast]
  have hsub : Ioc 0 ⌊y⌋₊ ⊆ Ioc 0 N := by
    intro n hn
    simp only [mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hcut⟩
  have he :
      (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) * (⌊y⌋₊ / n : ℕ)) =
        ∑ n ∈ Ioc 0 ⌊y⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊y⌋₊ / n : ℕ) := by
    apply (sum_subset hsub ?_).symm
    intro n hn hnot
    have hn0 : 0 < n := (mem_Ioc.mp hn).1
    have hlt : ⌊y⌋₊ < n := by
      simp only [mem_Ioc, hn0, true_and, not_le] at hnot
      exact hnot
    simp [Nat.div_eq_of_lt hlt]
  rw [he]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (actual_mobius_floor_partition ⌊y⌋₊)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Int.cast_ite, Int.cast_zero, Int.cast_one] at h
  rw [h]
  by_cases hy1 : 1 ≤ y
  · have hfloor : ⌊y⌋₊ ≠ 0 := by
      have := (Nat.one_le_floor_iff y).mpr hy1
      omega
    simp [hy1, hfloor]
  · have hfloor : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hy1)
    simp [hy1, hfloor]

theorem phaseRead_eq_linear_sub_floor (N : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    phaseRead N y = y * harmonicMobius N - floorRead N y := by
  unfold phaseRead harmonicMobius floorRead
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have harg : 0 ≤ y / (n : ℝ) := div_nonneg hy (Nat.cast_nonneg _)
  rw [Int.fract, ← natCast_floor_eq_intCast_floor harg]
  ring

/-- The actual untapered source has no residual floor term on 0<=y<=N.
This is a pointwise arithmetic identity, not a convergence estimate. -/
theorem actual_reciprocal_phase_residual (N : ℕ) {y : ℝ}
    (hy : 0 ≤ y) (hyN : y ≤ N) :
    reciprocalResidual N y = y * harmonicMobius N := by
  unfold reciprocalResidual
  rw [phaseRead_eq_linear_sub_floor N hy,
    actual_truncated_floor_partition N hy (Nat.floor_le_of_le hyN)]
  ring

/-- The exact exterior receiver is present as far down as 1/N.
No denominator is zero because N>0 forces x>=1/N>0. -/
theorem actual_nb_tail_pointwise {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : 1 / (N : ℝ) ≤ x) :
    physicalResidual N x = harmonicMobius N / x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hxpos : 0 < x := (one_div_pos.mpr hNr).trans_le hx
  have hxN : (1 : ℝ) ≤ x * (N : ℝ) := (div_le_iff₀ hNr).mp hx
  have hyN : x⁻¹ ≤ (N : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hxpos).mpr
    nlinarith
  have h := actual_reciprocal_phase_residual N (inv_nonneg.mpr hxpos.le) hyN
  simpa only [physicalResidual, div_eq_mul_inv, mul_comm] using h

end Holonics.Zeta.ActualFiniteBeurlingReceiver

#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_truncated_floor_partition
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_reciprocal_phase_residual
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_nb_receiver
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_nb_tail_pointwise
