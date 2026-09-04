import ElementaryHolonics.Mathematics.CopsonDeBruijnOrbitConvergence
import Mathlib.Analysis.PSeries

/-!
# Rationalized drift error and harmonic exclusion

The exact normalized recurrence is compared with its limiting autonomous drift on a declared
compact positive interval.  The error is explicitly `O(1/(n+2))`.  Reusable harmonic-tail
lemmas then exclude a fixed signed harmonic drift behind a persistent lower or upper barrier.

No convergence or asymptotic branch is assumed or stored in this owner.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Filter Topology
open scoped BigOperators

/-! ## Exact compact-positive drift approximation -/

/-- The limiting autonomous drift. -/
def limitingNormalizedDrift (x v : ℝ) : ℝ :=
  x - (v ^ 2 + 1) / (2 * v)

/-- The normalized square-root residue after removing the source term. -/
def normalizedRootResidue (x : ℝ) (n : ℕ) : ℝ :=
  normalizedRecurrenceValue x (n + 1) - x / (n + 2 : ℝ)

theorem normalizedRootResidue_nonneg {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    0 ≤ normalizedRootResidue x n := by
  rw [normalizedRootResidue, normalizedRecurrenceValue_succ_sub_source recurrence]
  exact Real.sqrt_nonneg _

/-- The finite scaled drift after rationalizing the principal square-root residue. -/
theorem normalized_scaled_drift_eq {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    (n + 2 : ℝ) *
        (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) =
      x - (normalizedRecurrenceValue x n ^ 2 + 1) /
        (normalizedRecurrenceValue x n + normalizedRootResidue x n) := by
  let m : ℝ := n + 2
  let v := normalizedRecurrenceValue x n
  let s := normalizedRootResidue x n
  have hm : 0 < m := by dsimp [m]; positivity
  have hv : 0 < v := normalizedRecurrenceValue_pos recurrence n
  have hs : 0 ≤ s := normalizedRootResidue_nonneg recurrence n
  have hdenom : 0 < v + s := add_pos_of_pos_of_nonneg hv hs
  have hsq0 := normalizedRecurrenceValue_succ_sub_source_sq recurrence n
  have hsq : s ^ 2 = ((m - 1) * v ^ 2 - 1) / m := by
    dsimp [s, m, v, normalizedRootResidue]
    rw [show (n + 2 : ℝ) - 1 = n + 1 by ring]
    exact hsq0
  have hw : normalizedRecurrenceValue x (n + 1) = x / m + s := by
    dsimp [s, m, normalizedRootResidue]
    ring
  rw [hw]
  change m * (x / m + s - v) = x - (v ^ 2 + 1) / (v + s)
  field_simp [hm.ne', hdenom.ne'] at hsq ⊢
  nlinarith

/-- The exact positive error between the autonomous drift and the scaled finite drift. -/
theorem limitingDrift_sub_scaledDrift_eq {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    limitingNormalizedDrift x (normalizedRecurrenceValue x n) -
        (n + 2 : ℝ) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) =
      (normalizedRecurrenceValue x n ^ 2 + 1) ^ 2 /
        (2 * normalizedRecurrenceValue x n * (n + 2 : ℝ) *
          (normalizedRecurrenceValue x n + normalizedRootResidue x n) ^ 2) := by
  let m : ℝ := n + 2
  let v := normalizedRecurrenceValue x n
  let s := normalizedRootResidue x n
  have hm : 0 < m := by dsimp [m]; positivity
  have hv : 0 < v := normalizedRecurrenceValue_pos recurrence n
  have hs : 0 ≤ s := normalizedRootResidue_nonneg recurrence n
  have hdenom : 0 < v + s := add_pos_of_pos_of_nonneg hv hs
  have hscaled := normalized_scaled_drift_eq recurrence n
  have hsq0 := normalizedRecurrenceValue_succ_sub_source_sq recurrence n
  have hsq : s ^ 2 = ((m - 1) * v ^ 2 - 1) / m := by
    dsimp [s, m, v, normalizedRootResidue]
    rw [show (n + 2 : ℝ) - 1 = n + 1 by ring]
    exact hsq0
  rw [hscaled]
  change (x - (v ^ 2 + 1) / (2 * v)) -
      (x - (v ^ 2 + 1) / (v + s)) =
    (v ^ 2 + 1) ^ 2 / (2 * v * m * (v + s) ^ 2)
  field_simp [hm.ne', hv.ne', hdenom.ne'] at hsq ⊢
  nlinarith

theorem abs_scaledDrift_sub_limitingDrift_eq {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    |(n + 2 : ℝ) *
        (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
      limitingNormalizedDrift x (normalizedRecurrenceValue x n)| =
      (normalizedRecurrenceValue x n ^ 2 + 1) ^ 2 /
        (2 * normalizedRecurrenceValue x n * (n + 2 : ℝ) *
          (normalizedRecurrenceValue x n + normalizedRootResidue x n) ^ 2) := by
  have heq := limitingDrift_sub_scaledDrift_eq recurrence n
  have hnonneg : 0 ≤
      (normalizedRecurrenceValue x n ^ 2 + 1) ^ 2 /
        (2 * normalizedRecurrenceValue x n * (n + 2 : ℝ) *
          (normalizedRecurrenceValue x n + normalizedRootResidue x n) ^ 2) := by
    have hv := normalizedRecurrenceValue_pos recurrence n
    have hs := normalizedRootResidue_nonneg recurrence n
    have hm : 0 ≤ (n + 2 : ℝ) := by positivity
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hv.le) hm) (sq_nonneg _))
  rw [← heq, abs_sub_comm, abs_of_nonneg]
  exact sub_nonneg.mpr (by linarith [heq, hnonneg])

/-- Uniform `O(1/(n+2))` drift error on a compact positive interval. -/
theorem abs_scaledDrift_sub_limitingDrift_le
    {x ε M : ℝ} (recurrence : AdmissibleRealRecurrence x) (n : ℕ)
    (hε : 0 < ε)
    (hlower : ε ≤ normalizedRecurrenceValue x n)
    (hupper : normalizedRecurrenceValue x n ≤ M) :
    |(n + 2 : ℝ) *
        (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
      limitingNormalizedDrift x (normalizedRecurrenceValue x n)| ≤
      (M ^ 2 + 1) ^ 2 / (2 * ε ^ 3 * (n + 2 : ℝ)) := by
  rw [abs_scaledDrift_sub_limitingDrift_eq recurrence]
  let v := normalizedRecurrenceValue x n
  let s := normalizedRootResidue x n
  let m : ℝ := n + 2
  have hv : 0 < v := normalizedRecurrenceValue_pos recurrence n
  have hs : 0 ≤ s := normalizedRootResidue_nonneg recurrence n
  have hm : 0 < m := by dsimp [m]; positivity
  have hM : 0 ≤ M := hv.le.trans hupper
  have hvs : ε ≤ v + s := hlower.trans (le_add_of_nonneg_right hs)
  have hnumBase : v ^ 2 + 1 ≤ M ^ 2 + 1 := by
    have hsq : v ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hv.le hM).2 hupper
    linarith
  have hnum : (v ^ 2 + 1) ^ 2 ≤ (M ^ 2 + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnumBase 2
  have hvsSq : ε ^ 2 ≤ (v + s) ^ 2 :=
    pow_le_pow_left₀ hε.le hvs 2
  have hcubic : ε ^ 3 ≤ v * (v + s) ^ 2 := by
    rw [show ε ^ 3 = ε * ε ^ 2 by ring]
    exact mul_le_mul hlower hvsSq (sq_nonneg _) hv.le
  have hdenom : 2 * ε ^ 3 * m ≤ 2 * v * m * (v + s) ^ 2 := by
    have hscale := mul_le_mul_of_nonneg_left hcubic (show 0 ≤ 2 * m by positivity)
    nlinarith only [hscale]
  change (v ^ 2 + 1) ^ 2 / (2 * v * m * (v + s) ^ 2) ≤
    (M ^ 2 + 1) ^ 2 / (2 * ε ^ 3 * m)
  exact div_le_div₀ (sq_nonneg _) hnum (by positivity) hdenom

/-! ## Reusable harmonic-drift exclusion -/

def harmonicTail (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1)

theorem harmonicTail_eq_sub (N M : ℕ) (hNM : N ≤ M) :
    harmonicTail N M =
      (∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1)) -
        ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) hNM
  unfold harmonicTail
  linarith

theorem tendsto_harmonicTail_nat_add (N : ℕ) :
    Tendsto (fun k : ℕ ↦ harmonicTail N (N + k)) atTop atTop := by
  let H : ℕ → ℝ := fun M ↦ ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1)
  have hH : Tendsto H atTop atTop := by
    simpa [H] using Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hadd : Tendsto (fun k : ℕ ↦ H (N + k)) atTop atTop := by
    have hshift : Tendsto (fun k : ℕ ↦ k + N) atTop atTop := tendsto_add_atTop_nat N
    have := hH.comp hshift
    change Tendsto (fun k : ℕ ↦ H (k + N)) atTop atTop at this
    simpa only [add_comm] using this
  have hsub : Tendsto (fun k : ℕ ↦ H (N + k) - H N) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-H N) hadd
  apply hsub.congr'
  filter_upwards [] with k
  rw [harmonicTail_eq_sub N (N + k) (Nat.le_add_right N k)]

theorem value_le_sub_harmonicTail_of_negative_drift
    {v : ℕ → ℝ} {δ : ℝ} (N : ℕ)
    (drift : ∀ n, N ≤ n →
      v (n + 1) ≤ v n - δ / ((n : ℝ) + 1)) :
    ∀ M, N ≤ M → v M ≤ v N - δ * harmonicTail N M := by
  intro M hNM
  induction M, hNM using Nat.le_induction with
  | base => simp [harmonicTail]
  | succ M hNM ih =>
      calc
        v (M + 1) ≤ v M - δ / ((M : ℝ) + 1) := drift M hNM
        _ ≤ (v N - δ * harmonicTail N M) - δ / ((M : ℝ) + 1) :=
          sub_le_sub_right ih _
        _ = v N - δ * harmonicTail N (M + 1) := by
          change v N - δ * (∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1)) -
              δ / ((M : ℝ) + 1) =
            v N - δ * (∑ n ∈ Finset.Ico N (M + 1), 1 / ((n : ℝ) + 1))
          rw [Finset.sum_Ico_succ_top hNM]
          ring

/-- A nonnegative tail cannot pay a fixed positive multiple of every harmonic clock tick. -/
theorem harmonic_negative_drift_impossible
    {v : ℕ → ℝ} {δ : ℝ} (N : ℕ) (hδ : 0 < δ)
    (nonnegative : ∀ n, N ≤ n → 0 ≤ v n)
    (drift : ∀ n, N ≤ n →
      v (n + 1) ≤ v n - δ / ((n : ℝ) + 1)) : False := by
  have ht := tendsto_harmonicTail_nat_add N
  rw [tendsto_atTop_atTop] at ht
  obtain ⟨K, hK⟩ := ht ((v N + 1) / δ + 1)
  have htail := hK K le_rfl
  have hv := value_le_sub_harmonicTail_of_negative_drift N drift (N + K)
    (Nat.le_add_right N K)
  have hvnonneg := nonnegative (N + K) (Nat.le_add_right N K)
  have hmul : v N + 1 < δ * harmonicTail N (N + K) := by
    have hstrict : (v N + 1) / δ < harmonicTail N (N + K) :=
      (lt_add_one ((v N + 1) / δ)).trans_le htail
    rw [div_lt_iff₀ hδ] at hstrict
    simpa [mul_comm] using hstrict
  nlinarith

/-- The same exclusion with an arbitrary persistent lower barrier. -/
theorem harmonic_negative_drift_impossible_of_lower
    {v : ℕ → ℝ} {δ lower : ℝ} (N : ℕ) (hδ : 0 < δ)
    (boundedBelow : ∀ n, N ≤ n → lower ≤ v n)
    (drift : ∀ n, N ≤ n →
      v (n + 1) ≤ v n - δ / ((n : ℝ) + 1)) : False := by
  let shifted : ℕ → ℝ := fun n ↦ v n - lower
  apply harmonic_negative_drift_impossible N hδ (v := shifted)
  · intro n hn
    exact sub_nonneg.mpr (boundedBelow n hn)
  · intro n hn
    dsimp [shifted]
    have := drift n hn
    linarith

/-- A persistently upper-bounded tail cannot receive a fixed positive harmonic drift. -/
theorem harmonic_positive_drift_impossible_of_upper
    {v : ℕ → ℝ} {δ upper : ℝ} (N : ℕ) (hδ : 0 < δ)
    (boundedAbove : ∀ n, N ≤ n → v n ≤ upper)
    (drift : ∀ n, N ≤ n →
      v n + δ / ((n : ℝ) + 1) ≤ v (n + 1)) : False := by
  let reflected : ℕ → ℝ := fun n ↦ upper - v n
  apply harmonic_negative_drift_impossible N hδ (v := reflected)
  · intro n hn
    exact sub_nonneg.mpr (boundedAbove n hn)
  · intro n hn
    dsimp [reflected]
    have := drift n hn
    linarith

section Audit

#print axioms normalized_scaled_drift_eq
#print axioms limitingDrift_sub_scaledDrift_eq
#print axioms abs_scaledDrift_sub_limitingDrift_le
#print axioms tendsto_harmonicTail_nat_add
#print axioms value_le_sub_harmonicTail_of_negative_drift
#print axioms harmonic_negative_drift_impossible
#print axioms harmonic_negative_drift_impossible_of_lower
#print axioms harmonic_positive_drift_impossible_of_upper

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
