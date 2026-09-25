import Mathlib

/-!
# The signed phase sectors of one prime generator

Repeated logarithmic translations have a resolvent response
q u / (1-q u), where q=p^(-1/2) and u is a unit phase of one
translation mode. Its real part has a positive common denominator.
The numerator, not the prime weight, partitions the phase population
into positive and negative sectors.
-/

noncomputable section

namespace Holonics.Zeta.PrimePhasePartition

/-- The scalar response of one repeated generator phase. -/
def phaseResolvent (q : ℝ) (u : ℂ) : ℂ :=
  ((q : ℂ) * u) / (1 - (q : ℂ) * u)

/-- Exact finite repeated-generator law. The remainder is the
unreturned (N+1)-st phase word; passing to the resolvent requires
its convergence, not a numerical truncation. -/
theorem finite_generator_series (z : ℂ) (N : ℕ) :
    (1 - z) * (∑ m ∈ Finset.range N, z ^ (m + 1)) =
      z - z ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [show N + 1 + 1 = N + 2 by omega, pow_succ]
      ring

/-- The common positive denominator in a unit-phase chart. -/
def phaseDenominator (q : ℝ) (u : ℂ) : ℝ :=
  1 - 2 * q * u.re + q ^ 2

theorem phaseDenominator_eq_normSq (q : ℝ) {u : ℂ}
    (hunit : Complex.normSq u = 1) :
    phaseDenominator q u = Complex.normSq (1 - (q : ℂ) * u) := by
  have hcomponents : u.re ^ 2 + u.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hunit
  simp [phaseDenominator, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  nlinarith [hcomponents]

theorem phaseDenominator_pos {q : ℝ} {u : ℂ}
    (hq : 0 < q) (hq1 : q < 1)
    (hunit : Complex.normSq u = 1) :
    0 < phaseDenominator q u := by
  rw [phaseDenominator_eq_normSq q hunit]
  apply Complex.normSq_pos.mpr
  intro hzero
  have hu : (q : ℂ) * u = 1 := sub_eq_zero.mp hzero |>.symm
  have hnorm := congrArg Complex.normSq hu
  rw [Complex.normSq_mul, Complex.normSq_ofReal, hunit] at hnorm
  norm_num at hnorm
  nlinarith

theorem phaseResolvent_real (q : ℝ) {u : ℂ}
    (hunit : Complex.normSq u = 1) :
    (phaseResolvent q u).re =
      (q * u.re - q ^ 2) / phaseDenominator q u := by
  have hcomponents : u.re ^ 2 + u.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hunit
  rw [phaseResolvent, Complex.div_re, ← add_div]
  rw [← phaseDenominator_eq_normSq q hunit]
  congr 1
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  nlinarith [hcomponents]

/-- The positive/negative phase partition is exact: the prime current is
nonnegative exactly when the phase cosine (the real part of u) reaches q. -/
theorem phaseResolvent_nonneg_iff {q : ℝ} {u : ℂ}
    (hq : 0 < q) (hq1 : q < 1)
    (hunit : Complex.normSq u = 1) :
    0 ≤ (phaseResolvent q u).re ↔ q ≤ u.re := by
  rw [phaseResolvent_real q hunit]
  have hden := phaseDenominator_pos hq hq1 hunit
  constructor
  · intro h
    have hnum : 0 ≤ q * u.re - q ^ 2 := by
      rcases div_nonneg_iff.mp h with h | h
      · exact h.1
      · exact False.elim ((not_le_of_gt hden) h.2)
    have hmul : 0 ≤ q * (u.re - q) := by nlinarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hq).mp hmul)
  · intro h
    apply div_nonneg
    · nlinarith [mul_nonneg hq.le (sub_nonneg.mpr h)]
    · exact hden.le

/-- The actual p^(-1/2) coefficient of a prime Euler generator lies in
the resolvent's admitted positive-radius domain. -/
theorem primeRate_pos_lt_one (p : ℕ) (hp : 2 ≤ p) :
    0 < (Real.sqrt p)⁻¹ ∧ (Real.sqrt p)⁻¹ < 1 := by
  have hpreal : (1 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hp)
  have hsqrt : 1 < Real.sqrt p := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hpreal
  have hsqrtpos : 0 < Real.sqrt p := by linarith
  exact ⟨inv_pos.mpr hsqrtpos, (inv_lt_one₀ hsqrtpos).mpr hsqrt⟩

/-- The sign partition instantiated at an actual prime address. -/
theorem prime_phase_nonneg_iff (p : ℕ) (hp : 2 ≤ p)
    {u : ℂ} (hunit : Complex.normSq u = 1) :
    0 ≤ (phaseResolvent (Real.sqrt p)⁻¹ u).re ↔
      (Real.sqrt p)⁻¹ ≤ u.re := by
  obtain ⟨hq, hq1⟩ := primeRate_pos_lt_one p hp
  exact phaseResolvent_nonneg_iff hq hq1 hunit

/-! ## Finite source-conditioned phase populations -/

/-- The positive receiver mass keeps the actual amplitude weight attached
to each admitted phase. -/
noncomputable def positivePhaseMass {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ℝ) (phase : ι → ℂ) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ S.filter (fun i => q ≤ (phase i).re),
    weight i * (phaseResolvent q (phase i)).re

/-- The negative receiver mass is stored as a nonnegative magnitude while
retaining the source addresses of its opposite-hand phase sector. -/
noncomputable def negativePhaseMass {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ℝ) (phase : ι → ℂ) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ S.filter (fun i => ¬ q ≤ (phase i).re),
    weight i * (-(phaseResolvent q (phase i)).re)

/-- Exact finite Jordan partition of one generator's signed response.
The source measure/weight is shared by both sectors; a sector count
without these weights is not the current. -/
theorem finite_phase_distribution
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (phase : ι → ℂ) (weight : ι → ℝ)
    (hunit : ∀ i ∈ S, Complex.normSq (phase i) = 1)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i * (phaseResolvent q (phase i)).re) =
        positivePhaseMass S q phase weight -
          negativePhaseMass S q phase weight ∧
      0 ≤ positivePhaseMass S q phase weight ∧
      0 ≤ negativePhaseMass S q phase weight := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun i => q ≤ (phase i).re)
    (fun i => weight i * (phaseResolvent q (phase i)).re)
  have hnegative :
      negativePhaseMass S q phase weight =
        -(∑ i ∈ S.filter (fun i => ¬ q ≤ (phase i).re),
          weight i * (phaseResolvent q (phase i)).re) := by
    unfold negativePhaseMass
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold positivePhaseMass
    rw [hnegative]
    linarith
  · unfold positivePhaseMass
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨hiS, hiphase⟩ := Finset.mem_filter.mp hi
    exact mul_nonneg (hweight i hiS)
      ((phaseResolvent_nonneg_iff hq hq1 (hunit i hiS)).mpr hiphase)
  · unfold negativePhaseMass
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨hiS, hiphase⟩ := Finset.mem_filter.mp hi
    have hnotresponse : ¬ 0 ≤ (phaseResolvent q (phase i)).re := by
      intro hresponse
      exact hiphase
        ((phaseResolvent_nonneg_iff hq hq1 (hunit i hiS)).mp hresponse)
    have hresponse : (phaseResolvent q (phase i)).re ≤ 0 :=
      le_of_lt (lt_of_not_ge hnotresponse)
    exact mul_nonneg (hweight i hiS) (neg_nonneg.mpr hresponse)

/-- A finite family of source generators can be grouped over one exact
positive denominator. This is the algebraic owner of the joint
positive/negative phase partition; an infinite prime limit requires a
separate source convergence law. -/
theorem finite_common_denominator
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (numerator denominator : ι → ℝ)
    (hden : ∀ i ∈ S, 0 < denominator i) :
    (∑ i ∈ S, numerator i / denominator i) *
        (∏ i ∈ S, denominator i) =
      ∑ i ∈ S, numerator i *
        (∏ j ∈ S.erase i, denominator j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hprod := Finset.mul_prod_erase S denominator hi
  rw [← hprod]
  field_simp [(hden i hi).ne']

/-- Since the collective denominator is positive, the sign of the
joined finite response is exactly the sign of its cross-multiplied
source numerator. -/
theorem finite_common_denominator_nonneg_iff
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (numerator denominator : ι → ℝ)
    (hden : ∀ i ∈ S, 0 < denominator i) :
    0 ≤ ∑ i ∈ S, numerator i / denominator i ↔
      0 ≤ ∑ i ∈ S, numerator i *
        (∏ j ∈ S.erase i, denominator j) := by
  have hprod : 0 < ∏ i ∈ S, denominator i := by
    apply Finset.prod_pos
    intro i hi
    exact hden i hi
  rw [← finite_common_denominator S numerator denominator hden]
  exact (mul_nonneg_iff_of_pos_right hprod).symm

end Holonics.Zeta.PrimePhasePartition

section Audit
open Holonics.Zeta.PrimePhasePartition
#print axioms phaseDenominator_eq_normSq
#print axioms finite_generator_series
#print axioms phaseDenominator_pos
#print axioms phaseResolvent_real
#print axioms phaseResolvent_nonneg_iff
#print axioms prime_phase_nonneg_iff
#print axioms finite_phase_distribution
#print axioms finite_common_denominator
#print axioms finite_common_denominator_nonneg_iff
end Audit
