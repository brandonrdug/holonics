import ElementaryHolonics.RH.ArchimedeanReceiver
import ElementaryHolonics.RH.Statement
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Weil positivity: under the Riemann hypothesis the spectral receiver of a square is a
nonnegative real

Weil's criterion reads the explicit formula on test functions of the form `h = g ⋆ g̃`, whose
spectral kernel is `ĥ(s) = G(s) · conj(G(1 − s̄))`.  On the critical line `1 − s̄ = s`
(`RiemannXi.criticalLine_fixedLocus`), so `ĥ(½ + iγ) = |G(½ + iγ)|²`, and the zero receiver
`Σ_ρ m_ρ ĥ(ρ)` is a sum of nonnegative reals as soon as every zero is on the line.  This file
proves that half exactly against the receiver of `RH.ExplicitFormulaReceiver`:

* `riemannXi_zero_in_strip` — every zero of the entire `ξ` lies in the open critical strip
  (`ζ ≠ 0` on `Re s ≥ 1` and the reflection `ξ(1 − s) = ξ(s)`);
* `riemannXi_zero_re_of_RH` — under `RiemannHypothesis` every zero of `ξ` has `Re = ½`;
* `truncatedZeroReceiver_nonneg_of_RH` — **under RH, for every Weil square and every disc, the
  truncated zero receiver is a nonnegative real number**.

Together with `ArchimedeanReceiver.truncatedExplicitFormula_of_archimedeanPorts`, the number the
primes compute — `polar − prime − archimedean + boundary` — is therefore forced nonnegative by
RH.  The converse, that positivity on every square forces RH, is Weil's theorem and is recorded
as the named port `HasWeilCriterion`; nothing here asserts it.

Every theorem below is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.WeilPositivity

open Soma.Holonics.RH.ExplicitFormulaReceiver
open Soma.Holonics.RH.RiemannXi
open Complex Metric

/-- [definition] A Weil square: a test chart whose spectral kernel is the pairing of `G` with its
reflection, `ĥ(s) = G(s) · conj(G(1 − s̄))`. -/
structure WeilSquare (T : WeilTestFunction) where
  G : ℂ → ℂ
  square : ∀ s, T.spectralKernel s = G s * (starRingEnd ℂ) (G (1 - (starRingEnd ℂ) s))

/-- [proved-derived; formal-checked] On the critical line the spectral kernel of a Weil square is
`|G|²`. -/
theorem spectralKernel_eq_normSq_on_line {T : WeilTestFunction} (W : WeilSquare T) {s : ℂ}
    (hs : s.re = 1 / 2) : T.spectralKernel s = ((normSq (W.G s) : ℝ) : ℂ) := by
  rw [W.square, (criticalLine_fixedLocus s).mpr hs, Complex.mul_conj]

/-- [proved-derived; formal-checked] `ξ` does not vanish on `Re s ≥ 1`. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [riemannXi_zero_and_one.2]
    norm_num
  · have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [riemannXi_eq_classicalProduct hs0 hs1]
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    have hcompleted : completedRiemannZeta s ≠ 0 := by
      intro h
      apply hzeta
      rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)) hcompleted

/-- [proved-derived; formal-checked] `ξ` does not vanish on `Re s ≤ 0`, by reflection. -/
theorem riemannXi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  apply riemannXi_ne_zero_of_one_le_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- [proved-derived; formal-checked] Every zero of `ξ` lies in the open critical strip. -/
theorem riemannXi_zero_in_strip {s : ℂ} (h : riemannXi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    exact riemannXi_ne_zero_of_re_nonpos (not_lt.mp hle) h
  · by_contra hge
    exact riemannXi_ne_zero_of_one_le_re (not_lt.mp hge) h

/-- [proved-derived; formal-checked] Under the Riemann hypothesis every zero of `ξ` is on the
line. -/
theorem riemannXi_zero_re_of_RH (hRH : RiemannHypothesis) {s : ℂ} (h : riemannXi s = 0) :
    s.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_in_strip h
  have hzeta : riemannZeta s = 0 := (riemannXi_eq_zero_iff_riemannZeta_eq_zero h0 h1).mp h
  apply hRH s hzeta
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro hs1
    rw [hs1] at h1
    norm_num at h1

/-- [proved-derived; formal-checked] The `ξ` divisor of a closed disc is supported on zeros of
`ξ`. -/
theorem riemannXi_eq_zero_of_divisor_ne_zero {c : ℂ} {R : ℝ} {u : ℂ}
    (hu : MeromorphicOn.divisor riemannXi (closedBall c |R|) u ≠ 0) : riemannXi u = 0 := by
  by_contra hne
  have hmem : u ∈ closedBall c |R| :=
    (MeromorphicOn.divisor riemannXi (closedBall c |R|)).supportWithinDomain hu
  have hA : AnalyticAt ℂ riemannXi u := analyticOn_riemannXi Set.univ u (Set.mem_univ u)
  have h0 : analyticOrderAt riemannXi u = 0 := hA.analyticOrderAt_eq_zero.2 hne
  rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem, hA.meromorphicOrderAt_eq,
    h0] at hu
  exact hu rfl

/-- [proved-derived; formal-checked] **Under the Riemann hypothesis the truncated zero receiver of
a Weil square is a nonnegative real**: `Σ_ρ m_ρ ĥ(ρ) = Σ_ρ m_ρ |G(ρ)|²` with every multiplicity
nonnegative and every zero on the line. -/
theorem truncatedZeroReceiver_nonneg_of_RH (hRH : RiemannHypothesis) {T : WeilTestFunction}
    (W : WeilSquare T) (c : ℂ) (R : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ truncatedZeroReceiver T c R = (r : ℂ) := by
  classical
  have hfin : (MeromorphicOn.divisor riemannXi (closedBall c |R|)).support.Finite :=
    (MeromorphicOn.divisor riemannXi (closedBall c |R|)).finiteSupport
      (isCompact_closedBall c |R|)
  have hDnonneg : 0 ≤ MeromorphicOn.divisor riemannXi (closedBall c |R|) :=
    divisor_riemannXi_nonnegative _
  refine ⟨∑ u ∈ hfin.toFinset,
    (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) * normSq (W.G u), ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro u _
    have hDcast : (0 : ℝ) ≤ (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) := by
      exact_mod_cast hDnonneg u
    exact mul_nonneg hDcast (normSq_nonneg _)
  · unfold truncatedZeroReceiver
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · push_cast
      apply Finset.sum_congr rfl
      intro u hu
      have hDu : MeromorphicOn.divisor riemannXi (closedBall c |R|) u ≠ 0 :=
        Function.mem_support.mp (hfin.mem_toFinset.mp hu)
      have hzero : riemannXi u = 0 := riemannXi_eq_zero_of_divisor_ne_zero hDu
      have hline : u.re = 1 / 2 := riemannXi_zero_re_of_RH hRH hzero
      rw [spectralKernel_eq_normSq_on_line W hline]
    · intro u hu
      rw [Function.mem_support] at hu
      have hDu : MeromorphicOn.divisor riemannXi (closedBall c |R|) u ≠ 0 := by
        intro h
        apply hu
        rw [h]
        simp
      exact hfin.mem_toFinset.mpr (Function.mem_support.mpr hDu)

/-- [project-postulate] Weil's criterion, the converse direction: positivity of the zero
receiver on every Weil square and every disc forces the Riemann hypothesis.  A named port. -/
structure HasWeilCriterion : Prop where
  criterion :
    (∀ (T : WeilTestFunction), WeilSquare T → ∀ (c : ℂ) (R : ℝ),
      ∃ r : ℝ, 0 ≤ r ∧ truncatedZeroReceiver T c R = (r : ℂ)) → RiemannHypothesis

/-- [proved-derived; formal-checked] With the port, the Riemann hypothesis is exactly positivity
of the spectral Weil receiver on every square — the positive-form face of the RH row. -/
theorem riemannHypothesis_iff_weilPositivity (port : HasWeilCriterion) :
    RiemannHypothesis ↔
      ∀ (T : WeilTestFunction), WeilSquare T → ∀ (c : ℂ) (R : ℝ),
        ∃ r : ℝ, 0 ≤ r ∧ truncatedZeroReceiver T c R = (r : ℂ) :=
  ⟨fun hRH _ W c R => truncatedZeroReceiver_nonneg_of_RH hRH W c R, port.criterion⟩

section Audit

#print axioms riemannXi_zero_in_strip
#print axioms riemannXi_zero_re_of_RH
#print axioms truncatedZeroReceiver_nonneg_of_RH
#print axioms riemannHypothesis_iff_weilPositivity

end Audit

end Soma.Holonics.RH.WeilPositivity
