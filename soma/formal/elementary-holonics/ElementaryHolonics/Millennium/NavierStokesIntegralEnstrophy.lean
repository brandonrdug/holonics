import ElementaryHolonics.Millennium.NavierStokesFiniteTimeContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time-dependent finite-slab enstrophy transport

The preceding finite-time owner closes the enstrophy differential inequality with constants on
each compact interior interval.  This module retains the actual time morphology: a continuous
Jacobian envelope `K(t)` and continuous curl-forcing envelope `F(t)` enter an integrating-factor
receiver through their interval integrals.

Every Navier--Stokes theorem below is restricted to `0 < a <= t <= b < T`.  Consequently its proof
uses no regularity at the terminal face `T`; the same argument can later attach to a carrier smooth
on `Ico 0 T`.  What is still absent is a restart/gluing theorem turning the returned interior bound
into extension across `T`.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Interval Laplacian

namespace Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## A scalar integrating-factor receiver -/

/-- The accumulated time-dependent rate from `a` to `t`. -/
def cumulativeRate (a : ℝ) (K : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in a..t, K s

/-- The exact Duhamel--Grönwall receiver for time-dependent multiplicative and additive rates. -/
def timeDependentGronwallBound
    (a initial : ℝ) (K F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (cumulativeRate a K t) *
    (initial + ∫ s in a..t,
      F s * Real.exp (-cumulativeRate a K s))

/-- A time-dependent scalar differential inequality returns the exact integrating-factor bound.

Unlike `gronwallBound`, neither coefficient is replaced by a uniform constant.  Continuity is a
convenient sufficient regularity hypothesis for the fundamental theorem of calculus; on a compact
interval it in particular supplies the required time integrability. -/
theorem le_timeDependentGronwallBound
    {E E' K F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (E' t) t)
    (hK : Continuous K) (hF : Continuous F)
    (hrate : ∀ t ∈ Icc a b, E' t ≤ K t * E t + F t) :
    ∀ t ∈ Icc a b,
      E t ≤ timeDependentGronwallBound a (E a) K F t := by
  let A : ℝ → ℝ := fun t => cumulativeRate a K t
  let weightedF : ℝ → ℝ := fun t => F t * Real.exp (-A t)
  let B : ℝ → ℝ := fun t => ∫ s in a..t, weightedF s
  let G : ℝ → ℝ := fun t => E t * Real.exp (-A t) - B t
  have hA : ∀ t, HasDerivAt A (K t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hK.intervalIntegrable a t)
      hK.aestronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hweightedF : Continuous weightedF := by
    have hAcontinuous : Continuous A :=
      (intervalIntegral.differentiable_integral_of_continuous (a := a) hK).continuous
    exact hF.mul (Real.continuous_exp.comp hAcontinuous.neg)
  have hB : ∀ t, HasDerivAt B (weightedF t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hweightedF.intervalIntegrable a t)
      hweightedF.aestronglyMeasurable.stronglyMeasurableAtFilter
      hweightedF.continuousAt
  have hG : ∀ t ∈ Icc a b,
      HasDerivAt G
        (Real.exp (-A t) * (E' t - K t * E t - F t)) t := by
    intro t ht
    have hExp : HasDerivAt (fun s => Real.exp (-A s))
        (Real.exp (-A t) * (-K t)) t := (hA t).neg.exp
    have hproduct := (hE t ht).mul hExp
    have hproduct' : HasDerivAt
        (fun s => E s * Real.exp (-A s))
        (E' t * Real.exp (-A t) + E t * (Real.exp (-A t) * (-K t))) t :=
      hproduct.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => rfl))
    have hdifference := hproduct'.sub (hB t)
    have hdifference' : HasDerivAt
        (fun s => E s * Real.exp (-A s) - B s)
        (E' t * Real.exp (-A t) + E t * (Real.exp (-A t) * (-K t)) - weightedF t) t :=
      hdifference.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => rfl))
    change HasDerivAt
      (fun s => E s * Real.exp (-A s) - B s)
      (Real.exp (-A t) * (E' t - K t * E t - F t)) t
    convert hdifference' using 1
    ring
  have hGcontinuous : ContinuousOn G (Icc a b) := by
    intro t ht
    exact (hG t ht).continuousAt.continuousWithinAt
  have hGantitone : AntitoneOn G (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hGcontinuous
    · intro t ht
      exact (hG t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hrate_t := hrate t (interior_subset ht)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  intro t ht
  have hweighted := hGantitone (left_mem_Icc.mpr hab) ht ht.1
  have hAtBase : A a = 0 := by simp [A, cumulativeRate]
  have hBtBase : B a = 0 := by simp [B]
  have hweighted' :
      E t * Real.exp (-A t) - B t ≤ E a := by
    simpa [G, hAtBase, hBtBase] using hweighted
  have hExpPositive : 0 ≤ Real.exp (A t) := (Real.exp_pos _).le
  have hcancel : Real.exp (-A t) * Real.exp (A t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    E t = (E t * Real.exp (-A t)) * Real.exp (A t) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ (E a + B t) * Real.exp (A t) := by
      apply mul_le_mul_of_nonneg_right _ hExpPositive
      linarith
    _ = timeDependentGronwallBound a (E a) K F t := by
      simp only [timeDependentGronwallBound]
      change (E a + B t) * Real.exp (A t) =
        Real.exp (A t) * (E a + B t)
      ring

/-! ## Attachment to finite periodic Navier--Stokes -/

/-- Continuous time-dependent spatial-Jacobian and curl-forcing envelopes return the full
Duhamel--Grönwall enstrophy bound on every compact interval in the open lifespan. -/
theorem periodicSolutionOn_enstrophy_le_timeDependentGronwallBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K F : ℝ → ℝ) (hKcontinuous : Continuous K) (hFcontinuous : Continuous F)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ F t) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        timeDependentGronwallBound a (periodicEnstrophy velocity a)
          (fun s => 2 * K s) F t := by
  let E : ℝ → ℝ := periodicEnstrophy velocity
  let E' : ℝ → ℝ := periodicEnstrophyRate nu force velocity
  apply le_timeDependentGronwallBound hab
  · intro t ht
    exact periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum solution
      (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hbT)
  · exact continuous_const.mul hKcontinuous
  · exact hFcontinuous
  · intro t ht
    exact periodicSolutionOn_enstrophyRate_le_of_jacobian_and_forcing_bounds
      solution (lt_of_lt_of_le ha ht.1) (lt_of_le_of_lt ht.2 hbT)
        hnu (K t) (F t) (hK t ht) (hforce t ht)

/-- With nonpositive curl-forcing work, an `L¹`-in-time Jacobian envelope controls enstrophy by
the exponential of its actual accumulated mass rather than by a uniform supremum. -/
theorem periodicSolutionOn_enstrophy_le_exp_integral_jacobian
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K : ℝ → ℝ) (hKcontinuous : Continuous K)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ 0) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a *
          Real.exp (∫ s in a..t, 2 * K s) := by
  intro t ht
  have h := periodicSolutionOn_enstrophy_le_timeDependentGronwallBound
    solution ha hab hbT hnu K (fun _ => 0) hKcontinuous continuous_const
      hK hforce t ht
  simpa [timeDependentGronwallBound, cumulativeRate, mul_comm] using h

/-- The periodic enstrophy receiver is nonnegative independently of the equation of motion. -/
theorem periodicEnstrophy_nonneg_receiver (velocity : VelocityField) (t : ℝ) :
    0 ≤ periodicEnstrophy velocity t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
  exact setIntegral_nonneg hcubeMeasurable (fun _ _ => by positivity)

/-- A finite accumulated Jacobian budget gives a uniform enstrophy bound on the compact interior
interval.  This is an estimate receiver only: no claim that it creates terminal trace data or a
longer solution is made. -/
theorem periodicSolutionOn_enstrophy_le_of_integral_jacobian_budget
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K : ℝ → ℝ) (hKcontinuous : Continuous K)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ 0)
    (hbudget : ∀ t ∈ Icc a b, (∫ s in a..t, 2 * K s) ≤ M) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a * Real.exp M := by
  intro t ht
  have hbound := periodicSolutionOn_enstrophy_le_exp_integral_jacobian
    solution ha hab hbT hnu K hKcontinuous hK hforce t ht
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hbudget t ht))
    (periodicEnstrophy_nonneg_receiver velocity a))

section Audit

#print axioms le_timeDependentGronwallBound
#print axioms periodicSolutionOn_enstrophy_le_timeDependentGronwallBound
#print axioms periodicSolutionOn_enstrophy_le_exp_integral_jacobian
#print axioms periodicSolutionOn_enstrophy_le_of_integral_jacobian_budget

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
