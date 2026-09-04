import ElementaryHolonics.Millennium.NavierStokesIntegralEnstrophy
import Mathlib.Topology.Order.ProjIcc

/-!
# Logarithmic Grönwall transport

This owner isolates the scalar Osgood estimate used in logarithmic continuation arguments.  A
positive receiver `H` is transported through the chart `log H`; the apparently nonlinear rate
`H' <= K H log H + F H` then becomes the ordinary time-dependent Grönwall inequality
`(log H)' <= K log H + F`.

The returned bound is exact at the level of that scalar inequality.  In the homogeneous case it is
the familiar double exponential
`H(t) <= exp (log (H(a)) * exp (integral_a^t K))`.  This module makes no claim that a
Navier--Stokes field supplies the hypotheses; a future high-order energy owner must establish that
attachment separately.
-/

noncomputable section

open Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

/-! ## The logarithmic receiver -/

/-- Extend a coefficient continuously from one addressed compact interval by freezing its endpoint
values outside that interval.  This is an apparatus for applying the global-continuity scalar
lemma; every returned interval integral below is proved independent of the extension. -/
def intervalContinuousExtension
    (a b : ℝ) (hab : a ≤ b) (K : ℝ → ℝ) : ℝ → ℝ :=
  Set.IccExtend hab (fun t : Icc a b => K t.1)

/-- A coefficient continuous on the addressed interval has a globally continuous frozen-endpoint
extension. -/
theorem continuous_intervalContinuousExtension
    {a b : ℝ} (hab : a ≤ b) {K : ℝ → ℝ}
    (hK : ContinuousOn K (Icc a b)) :
    Continuous (intervalContinuousExtension a b hab K) := by
  exact hK.restrict.Icc_extend'

/-- The frozen-endpoint extension is exactly the source coefficient on its addressed interval. -/
@[simp]
theorem intervalContinuousExtension_eq
    {a b : ℝ} (hab : a ≤ b) (K : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    intervalContinuousExtension a b hab K t = K t := by
  exact Set.IccExtend_of_mem hab (fun s : Icc a b => K s.1) ht

/-- The time-dependent logarithmic Grönwall receiver, including an additive rate after passage
through the logarithmic chart. -/
def logarithmicTimeDependentGronwallBound
    (a initial : ℝ) (K F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (timeDependentGronwallBound a (Real.log initial) K F t)

/-- A scalar inequality of the form
`H' <= K H log H + F H`, with `H >= 1`, returns the exponential of the exact
time-dependent Grönwall bound for `log H`.

The lower bound by one simultaneously makes the logarithmic chart nonsingular and records the
nonnegative initial logarithm needed by later accumulated-budget estimates. -/
theorem le_logarithmicTimeDependentGronwallBound
    {H H' K F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (H' t) t)
    (hHone : ∀ t ∈ Icc a b, 1 ≤ H t)
    (hK : Continuous K) (hF : Continuous F)
    (hrate : ∀ t ∈ Icc a b,
      H' t ≤ K t * H t * Real.log (H t) + F t * H t) :
    ∀ t ∈ Icc a b,
      H t ≤ logarithmicTimeDependentGronwallBound a (H a) K F t := by
  have hlogDeriv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => Real.log (H s)) (H' t / H t) t := by
    intro t ht
    exact (hH t ht).log (by linarith [hHone t ht])
  have hlogRate : ∀ t ∈ Icc a b,
      H' t / H t ≤ K t * Real.log (H t) + F t := by
    intro t ht
    have hpositive : 0 < H t := lt_of_lt_of_le zero_lt_one (hHone t ht)
    rw [div_le_iff₀ hpositive]
    calc
      H' t ≤ K t * H t * Real.log (H t) + F t * H t := hrate t ht
      _ = (K t * Real.log (H t) + F t) * H t := by ring
  have hlogBound := le_timeDependentGronwallBound
    (E := fun s => Real.log (H s)) (E' := fun s => H' s / H s)
    (K := K) (F := F) hab hlogDeriv hK hF hlogRate
  intro t ht
  have hpositive : 0 < H t := lt_of_lt_of_le zero_lt_one (hHone t ht)
  calc
    H t = Real.exp (Real.log (H t)) := (Real.exp_log hpositive).symm
    _ ≤ Real.exp
        (timeDependentGronwallBound a (Real.log (H a)) K F t) :=
      Real.exp_le_exp.mpr (hlogBound t ht)
    _ = logarithmicTimeDependentGronwallBound a (H a) K F t := rfl

/-! ## Homogeneous double-exponential form -/

/-- The homogeneous Osgood/BKM scalar estimate with the actual accumulated coefficient.

No supremum replaces `K`: its interval integral remains visible in the returned receiver. -/
theorem le_exp_log_mul_exp_integral_of_deriv_le_mul_log
    {H H' K : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (H' t) t)
    (hHone : ∀ t ∈ Icc a b, 1 ≤ H t)
    (hK : Continuous K)
    (hrate : ∀ t ∈ Icc a b,
      H' t ≤ K t * H t * Real.log (H t)) :
    ∀ t ∈ Icc a b,
      H t ≤ Real.exp
        (Real.log (H a) * Real.exp (∫ s in a..t, K s)) := by
  have hbound := le_logarithmicTimeDependentGronwallBound
    (H := H) (H' := H') (K := K) (F := fun _ => 0)
    hab hH hHone hK continuous_const (by
      intro t ht
      simpa using hrate t ht)
  intro t ht
  simpa [logarithmicTimeDependentGronwallBound,
    timeDependentGronwallBound, cumulativeRate, mul_comm] using hbound t ht

/-- The homogeneous logarithmic estimate needs continuity only on the interval whose consequence
is requested.  A frozen-endpoint extension feeds the preceding scalar theorem, while exact
interval congruence removes that extension from the returned bound. -/
theorem le_exp_log_mul_exp_integral_of_deriv_le_mul_log_of_continuousOn
    {H H' K : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (H' t) t)
    (hHone : ∀ t ∈ Icc a b, 1 ≤ H t)
    (hK : ContinuousOn K (Icc a b))
    (hrate : ∀ t ∈ Icc a b,
      H' t ≤ K t * H t * Real.log (H t)) :
    ∀ t ∈ Icc a b,
      H t ≤ Real.exp
        (Real.log (H a) * Real.exp (∫ s in a..t, K s)) := by
  let Kext : ℝ → ℝ := intervalContinuousExtension a b hab K
  have hKext : Continuous Kext :=
    continuous_intervalContinuousExtension hab hK
  have hrateExt : ∀ t ∈ Icc a b,
      H' t ≤ Kext t * H t * Real.log (H t) := by
    intro t ht
    simpa [Kext, intervalContinuousExtension_eq hab K ht] using hrate t ht
  have hbound := le_exp_log_mul_exp_integral_of_deriv_le_mul_log
    hab hH hHone hKext hrateExt
  intro t ht
  have hintegral : (∫ s in a..t, Kext s) = ∫ s in a..t, K s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact intervalContinuousExtension_eq hab K ⟨hs.1, hs.2.trans ht.2⟩
  simpa [hintegral] using hbound t ht

/-- A uniform upper budget for the accumulated logarithmic rate returns a time-uniform
double-exponential bound on the whole compact interval. -/
theorem le_exp_log_mul_exp_of_integral_budget
    {H H' K : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (H' t) t)
    (hHone : ∀ t ∈ Icc a b, 1 ≤ H t)
    (hK : Continuous K)
    (hrate : ∀ t ∈ Icc a b,
      H' t ≤ K t * H t * Real.log (H t))
    (hbudget : ∀ t ∈ Icc a b, (∫ s in a..t, K s) ≤ M) :
    ∀ t ∈ Icc a b,
      H t ≤ Real.exp (Real.log (H a) * Real.exp M) := by
  intro t ht
  have hactual := le_exp_log_mul_exp_integral_of_deriv_le_mul_log
    hab hH hHone hK hrate t ht
  have hlogNonneg : 0 ≤ Real.log (H a) :=
    Real.log_nonneg (hHone a (left_mem_Icc.mpr hab))
  have hinside :
      Real.log (H a) * Real.exp (∫ s in a..t, K s) ≤
        Real.log (H a) * Real.exp M :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hbudget t ht)) hlogNonneg
  exact hactual.trans (Real.exp_le_exp.mpr hinside)

/-- The time-uniform logarithmic estimate likewise needs only interval-local continuity of the
coefficient.  This is the form consumed by half-open lifespan arguments. -/
theorem le_exp_log_mul_exp_of_integral_budget_of_continuousOn
    {H H' K : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (H' t) t)
    (hHone : ∀ t ∈ Icc a b, 1 ≤ H t)
    (hK : ContinuousOn K (Icc a b))
    (hrate : ∀ t ∈ Icc a b,
      H' t ≤ K t * H t * Real.log (H t))
    (hbudget : ∀ t ∈ Icc a b, (∫ s in a..t, K s) ≤ M) :
    ∀ t ∈ Icc a b,
      H t ≤ Real.exp (Real.log (H a) * Real.exp M) := by
  intro t ht
  have hactual :=
    le_exp_log_mul_exp_integral_of_deriv_le_mul_log_of_continuousOn
      hab hH hHone hK hrate t ht
  have hlogNonneg : 0 ≤ Real.log (H a) :=
    Real.log_nonneg (hHone a (left_mem_Icc.mpr hab))
  have hinside :
      Real.log (H a) * Real.exp (∫ s in a..t, K s) ≤
        Real.log (H a) * Real.exp M :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hbudget t ht)) hlogNonneg
  exact hactual.trans (Real.exp_le_exp.mpr hinside)

section Audit

#print axioms le_logarithmicTimeDependentGronwallBound
#print axioms le_exp_log_mul_exp_integral_of_deriv_le_mul_log
#print axioms le_exp_log_mul_exp_integral_of_deriv_le_mul_log_of_continuousOn
#print axioms le_exp_log_mul_exp_of_integral_budget
#print axioms le_exp_log_mul_exp_of_integral_budget_of_continuousOn

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
