import ElementaryHolonics.RH.WeilPositivity

/-!
# The zero comb: reflection symmetry of the xi divisor and the diagonal/cross decomposition of
the Weil receiver

The functional equation `ξ(1 − s) = ξ(s)` and Mathlib's order-under-composition lemma make the
xi divisor symmetric under the reflection `s ↦ 1 − s`; on the centred discs the truncated zero
receiver therefore equals its reflection, i.e. the receiver of the symmetrized kernel.

On a Weil square the receiver splits as a comb: the **on-line diagonal**
`Σ_{Re ρ = ½} m_ρ |G(ρ)|²`, a nonnegative real unconditionally, plus the **off-line cross term**
`Σ_{Re ρ ≠ ½} m_ρ G(ρ) conj(G(1 − ρ̄))`, which vanishes under RH.  Weil positivity on a square
is therefore exactly the statement that the off-line cross term never pushes the receiver off the
nonnegative ray: the same reading as the coherence defect of a feed comb.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroComb

open Soma.Holonics.RH.ExplicitFormulaReceiver
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.WeilPositivity
open Complex Metric

/-! ## Reflection symmetry of the xi divisor -/

theorem riemannXi_comp_reflection : riemannXi ∘ (fun s : ℂ ↦ 1 - s) = riemannXi := by
  funext s
  exact riemannXi_one_sub s

/-- **The meromorphic order of `ξ` is reflection symmetric.** -/
theorem meromorphicOrderAt_riemannXi_one_sub (u : ℂ) :
    meromorphicOrderAt riemannXi (1 - u) = meromorphicOrderAt riemannXi u := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) u := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun s : ℂ ↦ 1 - s) u ≠ 0 := by
    have : deriv (fun s : ℂ ↦ 1 - s) u = -1 := by
      rw [deriv_const_sub, deriv_id'']
    rw [this]
    norm_num
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannXi) hg hg'
  rw [riemannXi_comp_reflection] at h
  exact h.symm

theorem one_sub_mem_closedBall_half_iff {R : ℝ} (u : ℂ) :
    (1 - u) ∈ closedBall (1 / 2 : ℂ) R ↔ u ∈ closedBall (1 / 2 : ℂ) R := by
  simp only [Metric.mem_closedBall, Complex.dist_eq]
  have : (1 - u) - (1 / 2 : ℂ) = -(u - 1 / 2) := by ring
  rw [this, norm_neg]

/-- **The xi divisor on a centred disc is reflection symmetric.** -/
theorem divisor_riemannXi_one_sub {R : ℝ} (u : ℂ) :
    MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R) (1 - u) =
      MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R) u := by
  by_cases hu : u ∈ closedBall (1 / 2 : ℂ) R
  · have hu' : (1 - u) ∈ closedBall (1 / 2 : ℂ) R := (one_sub_mem_closedBall_half_iff u).mpr hu
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu',
      MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu,
      meromorphicOrderAt_riemannXi_one_sub]
  · have hu' : (1 - u) ∉ closedBall (1 / 2 : ℂ) R :=
      fun h ↦ hu ((one_sub_mem_closedBall_half_iff u).mp h)
    rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def, if_neg (fun h ↦ hu' h.2),
      if_neg (fun h ↦ hu h.2)]

/-- **The centred zero receiver equals its reflection.** -/
theorem truncatedZeroReceiver_eq_reflected (T : WeilTestFunction) (R : ℝ) :
    truncatedZeroReceiver T (1 / 2) R =
      ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|) u : ℂ) *
        T.spectralKernel (1 - u) := by
  unfold truncatedZeroReceiver
  symm
  conv_rhs => rw [← finsum_comp_equiv (Equiv.subLeft (1 : ℂ))]
  refine finsum_congr fun a ↦ ?_
  simp only [Equiv.subLeft_apply]
  rw [divisor_riemannXi_one_sub]

/-! ## The diagonal and the cross term of a Weil square -/

variable {T : WeilTestFunction}

/-- The on-line diagonal of a Weil square on a disc: the zeros on the critical line, each paying
its multiplicity times `|G|²`. -/
def onLineDiagonal (W : WeilSquare T) (c : ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u, if u.re = 1 / 2 then
    (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) * normSq (W.G u) else 0

/-- The off-line cross term on a disc: the zeros off the critical line, each paying its
multiplicity times the spectral kernel. -/
def offLineCross (T : WeilTestFunction) (c : ℂ) (R : ℝ) : ℂ :=
  ∑ᶠ u, if u.re = 1 / 2 then 0 else
    (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℂ) * T.spectralKernel u

theorem onLineDiagonal_nonneg (W : WeilSquare T) (c : ℂ) (R : ℝ) :
    0 ≤ onLineDiagonal W c R := by
  unfold onLineDiagonal
  apply finsum_nonneg
  intro u
  split_ifs
  · have hD : (0 : ℝ) ≤ (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) := by
      exact_mod_cast divisor_riemannXi_nonnegative _ u
    exact mul_nonneg hD (normSq_nonneg _)
  · exact le_rfl

/-- **The Weil receiver is a comb: on-line diagonal plus off-line cross term.** -/
theorem truncatedZeroReceiver_eq_diagonal_add_cross (W : WeilSquare T) (c : ℂ) (R : ℝ) :
    truncatedZeroReceiver T c R = (onLineDiagonal W c R : ℂ) + offLineCross T c R := by
  classical
  set D := MeromorphicOn.divisor riemannXi (closedBall c |R|) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c |R|)
  have hsub1 : (Function.support fun u ↦ (D u : ℂ) * T.spectralKernel u) ⊆ hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    apply hfin.mem_toFinset.mpr
    rw [Function.mem_support]
    intro h
    apply hu
    rw [h]
    simp
  have hsub2 : (Function.support fun u ↦ if u.re = 1 / 2 then (D u : ℝ) * normSq (W.G u) else 0) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    apply hfin.mem_toFinset.mpr
    rw [Function.mem_support]
    intro h
    apply hu
    rw [h]
    simp
  have hsub3 : (Function.support fun u ↦ if u.re = 1 / 2 then (0 : ℂ) else
      (D u : ℂ) * T.spectralKernel u) ⊆ hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    apply hfin.mem_toFinset.mpr
    rw [Function.mem_support]
    intro h
    apply hu
    rw [h]
    simp
  unfold truncatedZeroReceiver onLineDiagonal offLineCross
  rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2,
    finsum_eq_sum_of_support_subset _ hsub3]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases hline : u.re = 1 / 2
  · rw [if_pos hline, if_pos hline, spectralKernel_eq_normSq_on_line W hline]
    push_cast
    ring
  · rw [if_neg hline, if_neg hline]
    simp

/-- **Under RH the off-line cross term vanishes.** -/
theorem offLineCross_eq_zero_of_RH (hRH : RiemannHypothesis) (c : ℂ) (R : ℝ) :
    offLineCross T c R = 0 := by
  unfold offLineCross
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  split_ifs with hline
  · rfl
  · by_cases hD : MeromorphicOn.divisor riemannXi (closedBall c |R|) u = 0
    · rw [hD]
      simp
    · exact absurd (riemannXi_zero_re_of_RH hRH (riemannXi_eq_zero_of_divisor_ne_zero hD)) hline

/-- **Weil positivity on a square is exactly a bound on the off-line cross term.** -/
theorem isNonnegativeReal_iff_cross (W : WeilSquare T) (c : ℂ) (R : ℝ) :
    (∃ r : ℝ, 0 ≤ r ∧ truncatedZeroReceiver T c R = (r : ℂ)) ↔
      ∃ x : ℝ, -onLineDiagonal W c R ≤ x ∧ offLineCross T c R = (x : ℂ) := by
  rw [truncatedZeroReceiver_eq_diagonal_add_cross W c R]
  constructor
  · rintro ⟨r, hr, hEq⟩
    refine ⟨r - onLineDiagonal W c R, by linarith, ?_⟩
    have : offLineCross T c R = (r : ℂ) - (onLineDiagonal W c R : ℂ) := by
      rw [← hEq]; ring
    rw [this]
    push_cast
    ring
  · rintro ⟨x, hx, hEq⟩
    refine ⟨onLineDiagonal W c R + x, by linarith, ?_⟩
    rw [hEq]
    push_cast
    ring

section Audit

#print axioms meromorphicOrderAt_riemannXi_one_sub
#print axioms divisor_riemannXi_one_sub
#print axioms truncatedZeroReceiver_eq_reflected
#print axioms truncatedZeroReceiver_eq_diagonal_add_cross
#print axioms isNonnegativeReal_iff_cross

end Audit

end Soma.Holonics.RH.ZeroComb
