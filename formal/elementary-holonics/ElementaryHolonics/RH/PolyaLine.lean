import Mathlib
import ElementaryHolonics.RH.ForwardPreservation
import ElementaryHolonics.RH.HeatSemigroup

/-!
# FT4 (iii): the polynomial Pólya step, transported to the seam

A real polynomial `q` with only real roots becomes, through `x = −i(z − ½)`, the entire function
`seamPoly q (z) = q(−i(z − ½))` whose zeros lie on the seam `Re z = ½`. The Euler iterate
`(1 + (λ/N) D²)^N` of `seamPoly q` is `seamPoly` of the `N`-fold heat step
`(heatStep (λ/N))^[N] q` of `ForwardPreservation`, whose roots stay real (`nonreal_heatStep_iterate_le`).
Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.PolyaLine

open Complex Polynomial Finset
open Soma.Holonics.RH.PolyaStep
open Soma.Holonics.RH.ForwardPreservation

/-- The seam function of a real polynomial: `q(−i(z − ½))`. -/
def seamPoly (q : ℝ[X]) (z : ℂ) : ℂ := (q.map ofRealHom).eval (-I * (z - 1 / 2))

theorem seamPoly_add (p q : ℝ[X]) (z : ℂ) : seamPoly (p + q) z = seamPoly p z + seamPoly q z := by
  unfold seamPoly
  rw [Polynomial.map_add, eval_add]

theorem seamPoly_smul (c : ℝ) (q : ℝ[X]) (z : ℂ) : seamPoly (c • q) z = (c : ℂ) * seamPoly q z := by
  unfold seamPoly
  rw [Polynomial.map_smul, eval_smul, smul_eq_mul]
  rfl

theorem seamPoly_sum {ι : Type*} (s : Finset ι) (q : ι → ℝ[X]) (z : ℂ) :
    seamPoly (∑ i ∈ s, q i) z = ∑ i ∈ s, seamPoly (q i) z := by
  unfold seamPoly
  rw [Polynomial.map_sum, eval_finset_sum]

theorem hasDerivAt_seamPoly (q : ℝ[X]) (z : ℂ) :
    HasDerivAt (seamPoly q) (-I * seamPoly (derivative q) z) z := by
  unfold seamPoly
  have h1 : HasDerivAt (fun z : ℂ => -I * (z - 1 / 2)) (-I) z := by
    have := ((hasDerivAt_id' z).sub_const (1 / 2 : ℂ)).const_mul (-I)
    simpa using this
  have h2 := (Polynomial.hasDerivAt (q.map ofRealHom) (-I * (z - 1 / 2))).comp z h1
  rw [derivative_map] at h2
  refine h2.congr_deriv ?_
  ring

theorem deriv_seamPoly (q : ℝ[X]) : deriv (seamPoly q) = fun z => -I * seamPoly (derivative q) z := by
  funext z
  exact (hasDerivAt_seamPoly q z).deriv

theorem differentiable_seamPoly (q : ℝ[X]) : Differentiable ℂ (seamPoly q) :=
  fun z => (hasDerivAt_seamPoly q z).differentiableAt

theorem iteratedDeriv_seamPoly (q : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (seamPoly q) = fun z => (-I) ^ n * seamPoly (derivative^[n] q) z := by
  induction n with
  | zero =>
    funext z
    simp only [iteratedDeriv_zero, pow_zero, one_mul, Function.iterate_zero, id]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_const_mul _ (differentiable_seamPoly _ z), (hasDerivAt_seamPoly _ z).deriv,
      Function.iterate_succ_apply', pow_succ]
    ring

theorem iteratedDeriv_two_mul_seamPoly (q : ℝ[X]) (k : ℕ) (z : ℂ) :
    iteratedDeriv (2 * k) (seamPoly q) z = (-1) ^ k * seamPoly (derivative^[2 * k] q) z := by
  rw [iteratedDeriv_seamPoly]
  simp only
  congr 1
  rw [pow_mul]
  congr 1
  simp [neg_sq]

/-- The Euler iterate of the flow on an entire function. -/
def eulerIter (lam : ℝ) (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ range (N + 1), ((N.choose k : ℂ) * ((lam : ℂ) / N) ^ k) * iteratedDeriv (2 * k) f z

/-- **The Euler iterate of a seam polynomial is the seam polynomial of the heat-step iterate.** -/
theorem eulerIter_seamPoly (lam : ℝ) (N : ℕ) (q : ℝ[X]) (z : ℂ) :
    eulerIter lam N (seamPoly q) z = seamPoly ((heatStep (lam / N))^[N] q) z := by
  rw [heatStep_iterate_eq_sum, seamPoly_sum]
  unfold eulerIter
  apply Finset.sum_congr rfl
  intro k _
  rw [seamPoly_smul, iteratedDeriv_two_mul_seamPoly]
  push_cast
  ring

/-- A root of a real-rooted polynomial's seam function lies on the seam. -/
theorem seamPoly_re {q : ℝ[X]} (hq0 : q ≠ 0) (hq : nonreal q = 0) {z : ℂ} (hz : seamPoly q z = 0) :
    z.re = 1 / 2 := by
  classical
  have hmap : q.map ofRealHom ≠ 0 := by
    intro h
    apply hq0
    exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp h
  have hroot : -I * (z - 1 / 2) ∈ (q.map ofRealHom).roots := by
    rw [mem_roots hmap]
    exact hz
  have hfilter := nonreal_eq_card_filter q
  rw [hq] at hfilter
  have hempty := (Multiset.card_eq_zero.mp hfilter.symm)
  have hnot : ¬ (-I * (z - 1 / 2)).im ≠ 0 := by
    intro h
    have hmem : -I * (z - 1 / 2) ∈ (q.map ofRealHom).roots.filter (fun w => ¬ w.im = 0) :=
      Multiset.mem_filter.mpr ⟨hroot, h⟩
    rw [hempty] at hmem
    exact Multiset.notMem_zero _ hmem
  push_neg at hnot
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im] at hnot
  norm_num at hnot
  linarith

theorem heatStep_ne_zero {lam : ℝ} {p : ℝ[X]} (hp : p ≠ 0) : heatStep lam p ≠ 0 := by
  unfold heatStep
  rcases Nat.lt_or_ge p.natDegree 2 with h | h
  · rw [iterate_derivative_eq_zero h, mul_zero, sub_zero]
    exact hp
  · have hd : (C lam * derivative^[2] p).natDegree < p.natDegree := by
      calc (C lam * derivative^[2] p).natDegree ≤ (derivative^[2] p).natDegree :=
            natDegree_C_mul_le _ _
        _ ≤ p.natDegree - 2 := by
            rw [Function.iterate_succ_apply', Function.iterate_one]
            calc (derivative (derivative p)).natDegree ≤ (derivative p).natDegree - 1 :=
                  natDegree_derivative_le _
              _ ≤ p.natDegree - 1 - 1 := by
                  have := natDegree_derivative_le p
                  omega
              _ = p.natDegree - 2 := by omega
        _ < p.natDegree := by omega
    have hlc : (p - C lam * derivative^[2] p).leadingCoeff = p.leadingCoeff :=
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hd)
    intro h0
    rw [h0, leadingCoeff_zero] at hlc
    exact (leadingCoeff_ne_zero.mpr hp) hlc.symm

theorem heatStep_iterate_ne_zero {lam : ℝ} (N : ℕ) {p : ℝ[X]} (hp : p ≠ 0) :
    (heatStep lam)^[N] p ≠ 0 := by
  induction N with
  | zero => simpa using hp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact heatStep_ne_zero ih

/-- **The heat-step iterates of a real-rooted polynomial stay real-rooted.** -/
theorem nonreal_heatStep_iterate {lam : ℝ} (hlam : 0 ≤ lam) (N : ℕ) {q : ℝ[X]} (hq : nonreal q = 0) :
    nonreal ((heatStep lam)^[N] q) = 0 :=
  le_antisymm (hq ▸ nonreal_heatStep_iterate_le hlam N q) (Nat.zero_le _)

/-- **The Euler iterates of a seam polynomial have their zeros on the seam.** -/
theorem eulerIter_seamPoly_re {lam : ℝ} (hlam : 0 ≤ lam) (N : ℕ) {q : ℝ[X]} (hq0 : q ≠ 0)
    (hq : nonreal q = 0) {z : ℂ} (hz : eulerIter lam N (seamPoly q) z = 0) : z.re = 1 / 2 := by
  rw [eulerIter_seamPoly] at hz
  exact seamPoly_re (heatStep_iterate_ne_zero N hq0)
    (nonreal_heatStep_iterate (by positivity) N hq) hz

end Soma.Holonics.RH.PolyaLine
