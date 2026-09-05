import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Exact Gaussian circulation profile

This owner records the elementary radial profile solving the stationary radial balance.  It is
an exact noncompact profile; no periodic solution or stability consequence is asserted.
-/

noncomputable section

open ContDiff Function Set Filter Topology

namespace Soma.Holonics.Millennium.NavierStokesGaussianCirculation

def gaussianRadialRate (mu a beta : ℝ) : ℝ := (a - 2 * beta) / (4 * mu)

def gaussianCirculation (Gamma q s : ℝ) : ℝ := Gamma * (1 - Real.exp (-q * s))

theorem gaussianRadialRate_pos (mu a beta : ℝ) (hmu : 0 < mu) (ha : 2 * beta < a) :
    0 < gaussianRadialRate mu a beta := by
  unfold gaussianRadialRate
  positivity

theorem gaussianCirculation_contDiff (Gamma q : ℝ) :
    ContDiff ℝ ∞ (gaussianCirculation Gamma q) := by
  unfold gaussianCirculation
  fun_prop

theorem gaussianCirculation_zero (Gamma q : ℝ) :
    gaussianCirculation Gamma q 0 = 0 := by
  simp [gaussianCirculation]

theorem hasDerivAt_gaussianCirculation (Gamma q s : ℝ) :
    HasDerivAt (gaussianCirculation Gamma q) (Gamma * q * Real.exp (-q * s)) s := by
  unfold gaussianCirculation
  have harg : HasDerivAt (fun x : ℝ ↦ -q * x) (-q) s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-q)
  have hexp := harg.exp
  have hbase := (hasDerivAt_const s (1 : ℝ)).sub hexp
  have h := hbase.const_mul Gamma
  convert h using 1 <;> try rfl
  ring

theorem hasDerivAt_gaussianCirculation_first (Gamma q s : ℝ) :
    HasDerivAt (fun x ↦ Gamma * q * Real.exp (-q * x))
      (-Gamma * q ^ 2 * Real.exp (-q * s)) s := by
  have harg : HasDerivAt (fun x : ℝ ↦ -q * x) (-q) s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-q)
  have hexp := harg.exp
  have h := hexp.const_mul (Gamma * q)
  convert h using 1 <;> try rfl
  ring

theorem gaussianCirculation_first_second_derivatives (Gamma q s : ℝ) :
    deriv (gaussianCirculation Gamma q) s = Gamma * q * Real.exp (-q * s) ∧
      deriv (fun x ↦ Gamma * q * Real.exp (-q * x)) s =
        -Gamma * q ^ 2 * Real.exp (-q * s) := by
  exact ⟨(hasDerivAt_gaussianCirculation Gamma q s).deriv,
    (hasDerivAt_gaussianCirculation_first Gamma q s).deriv⟩

theorem gaussianCirculation_pos (Gamma q s : ℝ) (hGamma : 0 < Gamma)
    (hq : 0 < q) (hs : 0 < s) :
    0 < gaussianCirculation Gamma q s := by
  unfold gaussianCirculation
  apply mul_pos hGamma
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  nlinarith

theorem gaussianCirculation_limit (Gamma q : ℝ) (hq : 0 < q) :
    Tendsto (gaussianCirculation Gamma q) atTop (𝓝 Gamma) := by
  have harg : Tendsto (fun s : ℝ ↦ -q * s) atTop atBot := by
    exact tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hq) tendsto_id
  have hexp : Tendsto (fun s : ℝ ↦ Real.exp (-q * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub : Tendsto (fun s : ℝ ↦ 1 - Real.exp (-q * s)) atTop (𝓝 1) :=
    by simpa only [sub_zero] using hone.sub hexp
  have hmul := hsub.const_mul Gamma
  unfold gaussianCirculation
  convert hmul using 1
  simp

theorem gaussianCirculation_radial_balance
    (mu a beta Gamma q s : ℝ) (hq : q = gaussianRadialRate mu a beta) :
    2 * s * (beta - a / 2) *
        (Gamma * q * Real.exp (-q * s)) =
      4 * mu * s * (-Gamma * q ^ 2 * Real.exp (-q * s)) := by
  rw [hq]
  unfold gaussianRadialRate
  field_simp
  ring

theorem gaussianCirculation_radial_balance_actual
    (mu a beta Gamma q s : ℝ) (hq : q = gaussianRadialRate mu a beta) :
    2 * s * (beta - a / 2) * deriv (gaussianCirculation Gamma q) s =
      4 * mu * s * deriv (fun x ↦ deriv (gaussianCirculation Gamma q) x) s := by
  have hfirst :
      deriv (gaussianCirculation Gamma q) s = Gamma * q * Real.exp (-q * s) :=
    (hasDerivAt_gaussianCirculation Gamma q s).deriv
  have hsecond :
      (fun x ↦ deriv (gaussianCirculation Gamma q) x) =
        (fun x ↦ Gamma * q * Real.exp (-q * x)) := by
    funext x
    exact (hasDerivAt_gaussianCirculation Gamma q x).deriv
  have hsecond' :
      deriv (fun x ↦ deriv (gaussianCirculation Gamma q) x) s =
        -Gamma * q ^ 2 * Real.exp (-q * s) := by
    rw [hsecond]
    exact (hasDerivAt_gaussianCirculation_first Gamma q s).deriv
  rw [hfirst, hsecond']
  exact gaussianCirculation_radial_balance mu a beta Gamma q s hq

theorem gaussianCirculation_not_compact_support
    (Gamma q : ℝ) (hGamma : 0 < Gamma) (hq : 0 < q) :
    ∀ s, 0 < s → gaussianCirculation Gamma q s ≠ 0 := by
  intro s hs
  exact (ne_of_gt (gaussianCirculation_pos Gamma q s hGamma hq hs))

/-- The axis reads the derivative of circulation, with no division by a collapsed radius. -/
def gaussianAngularVelocity (Gamma q : ℝ) : ℝ → ℝ := dslope (gaussianCirculation Gamma q) 0

theorem gaussianCirculation_analyticAt (Gamma q s : ℝ) :
    AnalyticAt ℝ (gaussianCirculation Gamma q) s := by
  unfold gaussianCirculation
  fun_prop

theorem gaussianAngularVelocity_analyticAt (Gamma q s : ℝ) :
    AnalyticAt ℝ (gaussianAngularVelocity Gamma q) s := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨p, hp⟩ := gaussianCirculation_analyticAt Gamma q 0
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hquot := (gaussianCirculation_analyticAt Gamma q s).div analyticAt_id hs
    have hslope : AnalyticAt ℝ (slope (gaussianCirculation Gamma q) 0) s := by
      have heq : slope (gaussianCirculation Gamma q) 0 = gaussianCirculation Gamma q / id := by
        funext x
        simp only [slope_def_field, gaussianCirculation_zero, sub_zero, Pi.div_apply, id_eq]
      rw [heq]
      exact hquot
    exact hslope.congr (dslope_eventuallyEq_slope_of_ne (gaussianCirculation Gamma q) hs).symm

theorem gaussianAngularVelocity_contDiff (Gamma q : ℝ) :
    ContDiff ℝ ∞ (gaussianAngularVelocity Gamma q) :=
  contDiff_iff_contDiffAt.mpr (fun s ↦ (gaussianAngularVelocity_analyticAt Gamma q s).contDiffAt)

theorem gaussianAngularVelocity_zero (Gamma q : ℝ) :
    gaussianAngularVelocity Gamma q 0 = Gamma * q := by
  rw [gaussianAngularVelocity, dslope_same, (hasDerivAt_gaussianCirculation Gamma q 0).deriv]
  simp

theorem mul_gaussianAngularVelocity (Gamma q s : ℝ) :
    s * gaussianAngularVelocity Gamma q s = gaussianCirculation Gamma q s := by
  change s * dslope (gaussianCirculation Gamma q) 0 s = _
  simpa only [sub_zero, smul_eq_mul, gaussianCirculation_zero] using
    sub_smul_dslope (gaussianCirculation Gamma q) 0 s

theorem gaussianAngularVelocity_deriv_zero (Gamma q : ℝ) :
    deriv (gaussianAngularVelocity Gamma q) 0 = -Gamma * q ^ 2 / 2 := by
  let O := gaussianAngularVelocity Gamma q
  have hO : ContDiff ℝ ∞ O := gaussianAngularVelocity_contDiff Gamma q
  have hd : Differentiable ℝ O := hO.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv O) :=
    (hO.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 2 O).differentiable_deriv_two
  have hfun : gaussianCirculation Gamma q = fun s ↦ s * O s :=
    funext (fun s ↦ (mul_gaussianAngularVelocity Gamma q s).symm)
  have hfirst : (fun s ↦ Gamma * q * Real.exp (-q * s)) =
      fun s ↦ O s + s * deriv O s := by
    funext s
    have hL := hasDerivAt_gaussianCirculation Gamma q s
    rw [hfun] at hL
    have hR := (hasDerivAt_id s).fun_mul (hd s).hasDerivAt
    simpa only [one_mul, id_eq] using hL.unique hR
  have hleft := hasDerivAt_gaussianCirculation_first Gamma q 0
  rw [hfirst] at hleft
  have hright := (hd 0).hasDerivAt.add
    ((hasDerivAt_id (0 : ℝ)).fun_mul (hdd 0).hasDerivAt)
  have heq := hleft.unique hright
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul, id_eq, zero_mul, add_zero] at heq
  change deriv O 0 = _
  linarith

#print axioms gaussianRadialRate_pos
#print axioms gaussianCirculation_contDiff
#print axioms hasDerivAt_gaussianCirculation
#print axioms hasDerivAt_gaussianCirculation_first
#print axioms gaussianCirculation_first_second_derivatives
#print axioms gaussianCirculation_pos
#print axioms gaussianCirculation_limit
#print axioms gaussianCirculation_radial_balance
#print axioms gaussianCirculation_radial_balance_actual
#print axioms gaussianCirculation_not_compact_support
#print axioms gaussianAngularVelocity_analyticAt
#print axioms gaussianAngularVelocity_contDiff
#print axioms gaussianAngularVelocity_zero
#print axioms mul_gaussianAngularVelocity
#print axioms gaussianAngularVelocity_deriv_zero

end Soma.Holonics.Millennium.NavierStokesGaussianCirculation
