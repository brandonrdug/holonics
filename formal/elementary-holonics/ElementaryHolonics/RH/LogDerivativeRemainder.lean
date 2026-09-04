import Mathlib

/-!
# The log-derivative remainder: Landau's bound from Borel--Carathéodory

For `g` analytic and nonvanishing on a disc, with `‖g z‖ ≤ ‖g z₀‖ e^M` on the disc, the analytic
logarithm `h` of `g / g z₀` has real part at most `M` and vanishes at the centre, so
Borel--Carathéodory bounds `‖h‖ ≤ 2M` on the half-radius circle and Cauchy's estimate bounds
`‖h'‖ = ‖g'/g‖ ≤ 8M / r` on the quarter disc.  This is the remainder term of Landau's lemma:
once the zeros are extracted, the log-derivative of `ξ` is the Coulomb flux of its zero comb
plus a remainder of this size.  The constant is the product expansion `8 = 2 · 2 · 2`, one factor
from Borel--Carathéodory and two from the two halvings of the radius.
-/

noncomputable section

namespace Soma.Holonics.RH.LogDerivativeRemainder

open Complex Metric Set

/-- **An analytic logarithm on a disc.** A nonvanishing analytic function on a ball is
`g z₀ · exp h` for an analytic `h` vanishing at the centre with `h' = g'/g`. -/
theorem exists_log {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball z₀ r)) (hne : ∀ z ∈ ball z₀ r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h z₀ = 0 ∧ (∀ z ∈ ball z₀ r, HasDerivAt h (deriv g z / g z) z) ∧
      ∀ z ∈ ball z₀ r, g z = g z₀ * exp (h z) := by
  have hdiv : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball z₀ r) := by
    have hd : DifferentiableOn ℂ (deriv g) (ball z₀ r) :=
      (hg.analyticOnNhd isOpen_ball).deriv.differentiableOn
    exact hd.div hg hne
  obtain ⟨H, hH⟩ := hdiv.isExactOn_ball
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  refine ⟨fun z => H z - H z₀, by simp, fun z hz => (hH z hz).sub_const _, ?_⟩
  -- the function g · exp(−h) has zero derivative on the ball, hence is constant
  set h : ℂ → ℂ := fun z => H z - H z₀ with hhdef
  have hh : ∀ z ∈ ball z₀ r, HasDerivAt h (deriv g z / g z) z :=
    fun z hz => (hH z hz).sub_const _
  set φ : ℂ → ℂ := fun z => g z * exp (-h z) with hφdef
  have hφ : ∀ z ∈ ball z₀ r, HasDerivAt φ 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hexp : HasDerivAt (fun w => exp (-h w)) (exp (-h z) * -(deriv g z / g z)) z :=
      (hh z hz).neg.cexp
    have := hgz.mul hexp
    have hne' := hne z hz
    have hcancel : g z * (deriv g z / g z) = deriv g z := mul_div_cancel₀ _ hne'
    refine this.congr_deriv ?_
    rw [mul_neg, mul_neg, mul_left_comm (g z) (exp (-h z)), hcancel]
    ring
  have hconst : ∀ z ∈ ball z₀ r, φ z = φ z₀ := by
    intro z hz
    apply (convex_ball z₀ r).is_const_of_fderivWithin_eq_zero
      (fun w hw => (hφ w hw).differentiableAt.differentiableWithinAt) _ hz hz₀
    intro w hw
    rw [fderivWithin_of_isOpen isOpen_ball hw, (hφ w hw).hasFDerivAt.fderiv]
    ext
    simp
  intro z hz
  have h1 := hconst z hz
  simp only [hφdef, hhdef, sub_self, neg_zero, exp_zero, mul_one] at h1
  have hexpne : exp (-(H z - H z₀)) ≠ 0 := exp_ne_zero _
  calc g z = g z * exp (-(H z - H z₀)) * exp (H z - H z₀) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ = g z₀ * exp (H z - H z₀) := by rw [h1]

/-- **Landau's remainder bound.** If `g` is analytic and nonvanishing on `ball z₀ r` with
`‖g z‖ ≤ ‖g z₀‖ · e^M` there, then `‖g'/g‖ ≤ 8M / r` on the closed quarter disc. -/
theorem norm_logDeriv_le {g : ℂ → ℂ} {z₀ : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball z₀ r)) (hne : ∀ z ∈ ball z₀ r, g z ≠ 0)
    (hbound : ∀ z ∈ ball z₀ r, ‖g z‖ ≤ ‖g z₀‖ * Real.exp M)
    {z : ℂ} (hz : z ∈ closedBall z₀ (r / 4)) :
    ‖deriv g z / g z‖ ≤ 8 * M / r := by
  obtain ⟨h, hh0, hhd, hgh⟩ := exists_log hr hg hne
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hg₀ : g z₀ ≠ 0 := hne z₀ hz₀
  -- the real part of h is bounded by M on the ball
  have hre : ∀ w ∈ ball z₀ r, (h w).re ≤ M := by
    intro w hw
    have h1 := hbound w hw
    rw [hgh w hw, norm_mul, Complex.norm_exp] at h1
    have hpos : 0 < ‖g z₀‖ := norm_pos_iff.mpr hg₀
    have h2 : Real.exp (h w).re ≤ Real.exp M := le_of_mul_le_mul_left h1 hpos
    exact Real.exp_le_exp.mp h2
  -- h is differentiable on the ball
  have hhdiff : DifferentiableOn ℂ h (ball z₀ r) :=
    fun w hw => (hhd w hw).differentiableAt.differentiableWithinAt
  -- Borel–Carathéodory on the translated ball: ‖h(z₀ + w)‖ ≤ 2 M ‖w‖ / (r − ‖w‖)
  have hBC : ∀ w : ℂ, ‖w‖ < r → ‖h (z₀ + w)‖ ≤ 2 * M * ‖w‖ / (r - ‖w‖) := by
    intro w hw
    set F : ℂ → ℂ := fun w => h (z₀ + w) with hFdef
    have hFd : DifferentiableOn ℂ F (ball 0 r) := by
      intro w hw
      have hmem : z₀ + w ∈ ball z₀ r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact mem_ball_zero_iff.mp hw
      exact ((hhd _ hmem).differentiableAt.comp w
        ((differentiableAt_const _).add differentiableAt_id)).differentiableWithinAt
    have hFre : MapsTo F (ball 0 r) {z | z.re ≤ M} := by
      intro w hw
      have hmem : z₀ + w ∈ ball z₀ r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact mem_ball_zero_iff.mp hw
      exact hre _ hmem
    have hF0 : F 0 = 0 := by simp [hFdef, hh0]
    have := Complex.borelCaratheodory hM hFd hFre hr (mem_ball_zero_iff.mpr hw)
    rw [hF0, norm_zero, zero_mul, zero_div, add_zero] at this
    exact this
  -- on the circle of radius r/4 about z, ‖h‖ ≤ 2 M
  have hcirc : ∀ w ∈ sphere z (r / 4), ‖h w‖ ≤ 2 * M := by
    intro w hw
    have hdist : ‖w - z₀‖ ≤ r / 2 := by
      have h1 : ‖w - z‖ = r / 4 := by rw [mem_sphere_iff_norm] at hw; exact hw
      have h2 : ‖z - z₀‖ ≤ r / 4 := by rw [mem_closedBall_iff_norm] at hz; exact hz
      calc ‖w - z₀‖ = ‖(w - z) + (z - z₀)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ r / 4 + r / 4 := add_le_add h1.le h2
        _ = r / 2 := by ring
    have hlt : ‖w - z₀‖ < r := by linarith
    have := hBC (w - z₀) hlt
    rw [add_sub_cancel] at this
    refine this.trans ?_
    have hpos : 0 < r - ‖w - z₀‖ := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg (w - z₀)]
  -- Cauchy's estimate on the quarter disc
  have hsub : closedBall z (r / 4) ⊆ ball z₀ r := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [mem_ball_iff_norm]
    have h2 : ‖z - z₀‖ ≤ r / 4 := by rw [mem_closedBall_iff_norm] at hz; exact hz
    calc ‖w - z₀‖ = ‖(w - z) + (z - z₀)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ r / 4 + r / 4 := add_le_add hw h2
      _ < r := by linarith
  have hdc : DiffContOnCl ℂ h (ball z (r / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by positivity : r / 4 ≠ 0)]
    exact hhdiff.mono hsub
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc hcirc
  have hzmem : z ∈ ball z₀ r := hsub (mem_closedBall_self (by positivity))
  rw [(hhd z hzmem).deriv] at hcauchy
  calc ‖deriv g z / g z‖ ≤ 2 * M / (r / 4) := hcauchy
    _ = 8 * M / r := by field_simp; ring

end Soma.Holonics.RH.LogDerivativeRemainder
