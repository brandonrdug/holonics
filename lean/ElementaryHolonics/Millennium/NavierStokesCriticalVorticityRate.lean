import ElementaryHolonics.Millennium.NavierStokesCriticalContinuation
import ElementaryHolonics.Millennium.NavierStokesOverlapUniqueness
import ElementaryHolonics.Millennium.NavierStokesTorusVorticity

/-!
# The genuine critical vorticity rate on an open periodic lifespan

This owner attaches the exact spatial `L∞` vorticity receiver on the genuine three-torus to the
half-open continuation factorization.  The primary object remains the descended vorticity
world-tube.  Its continuous-map norm is one receiver face, characterized exactly by a pointwise
Euclidean bound and totalized outside the open lifespan only so interval integrals have the usual
real-domain type.

No value at the terminal face is asserted.  Continuity is proved only on `Ioo 0 T`, and therefore
on every addressed tail `Ico a T` with `0 < a`.  A finite accumulated-vorticity budget becomes the
abstract critical-rate budget without changing its coefficient.  The logarithmic high-order
differential inequality itself remains an explicit analytic premise.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation

/-- The critical vorticity receiver on its native open time carrier. -/
def criticalVorticityRateOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Ioo 0 T → ℝ :=
  fun t => ‖torusVorticityEvolution solution t‖

/-- The native critical rate varies continuously throughout the open lifespan. -/
theorem continuous_criticalVorticityRateOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (criticalVorticityRateOn solution) :=
  continuous_norm_torusVorticityEvolution solution

/-- A real-domain presentation used only for time integration.  Outside the open lifespan it is
zero; no theorem below claims continuity or physical meaning there. -/
def criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo 0 T then criticalVorticityRateOn solution ⟨t, ht⟩ else 0

/-- On every interior time the real-domain presentation is exactly the native torus norm. -/
@[simp]
theorem criticalVorticityRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    criticalVorticityRate solution t =
      ‖torusVorticityEvolution solution ⟨t, ht⟩‖ := by
  simp [criticalVorticityRate, criticalVorticityRateOn, ht]

/-- The totalized receiver remains nonnegative at every real time. -/
theorem criticalVorticityRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) (t : ℝ) :
    0 ≤ criticalVorticityRate solution t := by
  by_cases ht : t ∈ Ioo 0 T
  · rw [criticalVorticityRate_eq solution ht]
    exact norm_nonneg _
  · simp [criticalVorticityRate, ht]

/-- The real-domain presentation is continuous exactly where the vorticity world-tube lives. -/
theorem continuousOn_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContinuousOn (criticalVorticityRate solution) (Ioo 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply (continuous_criticalVorticityRateOn solution).congr
  intro t
  simp [Set.restrict_apply, criticalVorticityRate, criticalVorticityRateOn, t.2]

/-- Hence every positive addressed tail inherits continuity without any terminal trace. -/
theorem continuousOn_criticalVorticityRate_tail
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) :
    ContinuousOn (criticalVorticityRate solution) (Ico a T) :=
  (continuousOn_criticalVorticityRate solution).mono (by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, ht.2⟩)

/-- The coefficient naturally returned by the periodic logarithmic Hodge estimate.  The constant
part records the low-frequency face; the vorticity part records the scale-critical shells. -/
def augmentedCriticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) (t : ℝ) : ℝ :=
  1 + criticalVorticityRate solution t

/-- The augmented coefficient is continuous on every addressed positive tail. -/
theorem continuousOn_augmentedCriticalVorticityRate_tail
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) :
    ContinuousOn (augmentedCriticalVorticityRate solution) (Ico a T) :=
  continuousOn_const.add (continuousOn_criticalVorticityRate_tail solution ha)

/-- The multiplicative analytic constant carried by the periodic logarithmic Hodge estimate. -/
def scaledAugmentedCriticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (C : ℝ) (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ :=
  C * augmentedCriticalVorticityRate solution t

/-- Scaling by the fixed analytic constant preserves continuity on the addressed tail. -/
theorem continuousOn_scaledAugmentedCriticalVorticityRate_tail
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (C : ℝ) (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) :
    ContinuousOn (scaledAugmentedCriticalVorticityRate C solution) (Ico a T) :=
  continuousOn_const.mul (continuousOn_augmentedCriticalVorticityRate_tail solution ha)

/-- Exact receiver characterization: the scalar critical rate is bounded precisely when every
Euclidean representative of the vorticity slice is bounded. -/
theorem criticalVorticityRate_le_iff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t C : ℝ} (ht : t ∈ Ioo 0 T) :
    criticalVorticityRate solution t ≤ C ↔
      ∀ x : Space, ‖vorticityField velocity x t‖ ≤ C := by
  rw [criticalVorticityRate_eq solution ht]
  exact norm_torusVorticityEvolution_le_iff solution ⟨t, ht⟩ C

/-- A finite accumulated budget for the actual torus vorticity receiver on every strict tail
interval. -/
structure OpenAccumulatedCriticalVorticityBudget
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (M : ℝ) : Prop where
  accumulated_le : ∀ t ∈ Ico a T,
    (∫ s in a..t, criticalVorticityRate solution s) ≤ M

/-- The concrete accumulated-vorticity budget is exactly the critical-rate budget consumed by the
continuation factorization. -/
def OpenAccumulatedCriticalVorticityBudget.toCriticalRateBudget
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M) :
    OpenAccumulatedCriticalRateBudget T a M (criticalVorticityRate solution) where
  accumulated_le := budget.accumulated_le

/-- Adding the low-frequency constant costs only the finite length of the old lifespan.  Thus a
finite integral of the genuine critical vorticity receiver controls the coefficient that appears
in the logarithmic Hodge/BKM estimate. -/
def OpenAccumulatedCriticalVorticityBudget.toAugmentedCriticalRateBudget
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (ha : 0 < a)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M) :
    OpenAccumulatedCriticalRateBudget T a (T - a + M)
      (augmentedCriticalVorticityRate solution) where
  accumulated_le := by
    intro t ht
    have hcontinuous : ContinuousOn (criticalVorticityRate solution) (Icc a t) :=
      (continuousOn_criticalVorticityRate_tail solution ha).mono (by
        intro s hs
        exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
    have hintegrable : IntervalIntegrable (criticalVorticityRate solution) volume a t :=
      hcontinuous.intervalIntegrable_of_Icc ht.1
    have hsplit : (∫ s in a..t, augmentedCriticalVorticityRate solution s) =
        (t - a) + ∫ s in a..t, criticalVorticityRate solution s := by
      simp only [augmentedCriticalVorticityRate]
      rw [intervalIntegral.integral_add intervalIntegrable_const hintegrable]
      simp
    rw [hsplit]
    have hbudget := budget.accumulated_le t ht
    have htT : t ≤ T := ht.2.le
    linarith

/-- A nonnegative fixed analytic constant scales the complete augmented budget without discarding
its low-frequency or vorticity populations. -/
def OpenAccumulatedCriticalVorticityBudget.toScaledAugmentedCriticalRateBudget
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {C : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M) :
    OpenAccumulatedCriticalRateBudget T a (C * (T - a + M))
      (scaledAugmentedCriticalVorticityRate C solution) where
  accumulated_le := by
    intro t ht
    have hscale : (∫ s in a..t, scaledAugmentedCriticalVorticityRate C solution s) =
        C * ∫ s in a..t, augmentedCriticalVorticityRate solution s := by
      simp only [scaledAugmentedCriticalVorticityRate]
      rw [intervalIntegral.integral_const_mul]
    rw [hscale]
    exact mul_le_mul_of_nonneg_left
      ((budget.toAugmentedCriticalRateBudget ha).accumulated_le t ht) hC

/-- Package an explicitly proved high-order differential inequality with the genuine critical
vorticity coefficient.  This removes the formerly abstract `K`; it does not prove the analytic
high-order inequality. -/
def lifespanLogarithmicLawOfCriticalVorticity
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (haT : a < T)
    (hderiv : ∀ t ∈ Ico a T, HasDerivAt H (H' t) t)
    (hone : ∀ t ∈ Ico a T, 1 ≤ H t)
    (hrate : ∀ t ∈ Ico a T,
      H' t ≤ criticalVorticityRate solution t * H t * Real.log (H t)) :
    LifespanLogarithmicHighOrderLaw T a H H'
      (criticalVorticityRate solution) where
  base_pos := ha
  base_lt_terminal := haT
  receiver_derivative := hderiv
  receiver_one := hone
  criticalRate_continuousOn := continuousOn_criticalVorticityRate_tail solution ha
  differential_law := hrate

/-- Package the standard low-frequency-plus-vorticity coefficient produced by a periodic
logarithmic Hodge estimate. -/
def lifespanLogarithmicLawOfAugmentedCriticalVorticity
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (haT : a < T)
    (hderiv : ∀ t ∈ Ico a T, HasDerivAt H (H' t) t)
    (hone : ∀ t ∈ Ico a T, 1 ≤ H t)
    (hrate : ∀ t ∈ Ico a T,
      H' t ≤ augmentedCriticalVorticityRate solution t * H t * Real.log (H t)) :
    LifespanLogarithmicHighOrderLaw T a H H'
      (augmentedCriticalVorticityRate solution) where
  base_pos := ha
  base_lt_terminal := haT
  receiver_derivative := hderiv
  receiver_one := hone
  criticalRate_continuousOn :=
    continuousOn_augmentedCriticalVorticityRate_tail solution ha
  differential_law := hrate

/-- Package the full coefficient `C * (1 + norm(omega)_infinity)` without normalizing away the
constant supplied by the analytic shell estimates. -/
def lifespanLogarithmicLawOfScaledAugmentedCriticalVorticity
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    (C : ℝ)
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (haT : a < T)
    (hderiv : ∀ t ∈ Ico a T, HasDerivAt H (H' t) t)
    (hone : ∀ t ∈ Ico a T, 1 ≤ H t)
    (hrate : ∀ t ∈ Ico a T,
      H' t ≤ scaledAugmentedCriticalVorticityRate C solution t * H t * Real.log (H t)) :
    LifespanLogarithmicHighOrderLaw T a H H'
      (scaledAugmentedCriticalVorticityRate C solution) where
  base_pos := ha
  base_lt_terminal := haT
  receiver_derivative := hderiv
  receiver_one := hone
  criticalRate_continuousOn :=
    continuousOn_scaledAugmentedCriticalVorticityRate_tail C solution ha
  differential_law := hrate

/-- The actual accumulated spatial-vorticity receiver yields the explicit uniform high-order
bound once the corresponding logarithmic differential law has been established. -/
theorem uniformOpenHighOrderBound_of_accumulatedCriticalVorticity
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (criticalVorticityRate solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M) :
    UniformOpenHighOrderBound T a H
      (Real.exp (Real.log (H a) * Real.exp M)) :=
  law.uniformOpenHighOrderBound budget.toCriticalRateBudget

/-- The standard augmented coefficient gives a bound whose exponent pays exactly the finite tail
length in addition to the accumulated vorticity. -/
theorem uniformOpenHighOrderBound_of_augmentedCriticalVorticity
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (augmentedCriticalVorticityRate solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M) :
    UniformOpenHighOrderBound T a H
      (Real.exp (Real.log (H a) * Real.exp (T - a + M))) :=
  law.uniformOpenHighOrderBound
    (budget.toAugmentedCriticalRateBudget law.base_pos)

/-- The concrete critical-vorticity continuation factorization.  The time integral here is the
norm of the descended vorticity field on the genuine three-torus, not an abstract coefficient.
The high-order law, local restart theorem, seam construction, and overlap uniqueness remain
visible analytic inputs. -/
def criticalVorticityContinuationFactorization
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (criticalVorticityRate solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw solution)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) * Real.exp M)) :=
  logarithmicHighOrderContinuationFactorization law budget.toCriticalRateBudget
    restartFromBound spliceLaw unique

/-- The continuation factorization in the coefficient form used by the periodic BKM route. -/
def augmentedCriticalVorticityContinuationFactorization
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (augmentedCriticalVorticityRate solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw solution)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) * Real.exp (T - a + M))) :=
  logarithmicHighOrderContinuationFactorization law
    (budget.toAugmentedCriticalRateBudget law.base_pos)
    restartFromBound spliceLaw unique

/-- Nonnegative viscosity discharges the overlap-uniqueness port by the periodic difference-field
energy theorem.  The only remaining continuation inputs are therefore the logarithmic high-order
law, its local-restart consequence, and the analytic seam. -/
def augmentedCriticalVorticityContinuationFactorization_of_nonnegativeViscosity
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hnu : 0 ≤ nu)
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (augmentedCriticalVorticityRate solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw solution) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) * Real.exp (T - a + M))) :=
  augmentedCriticalVorticityContinuationFactorization law budget restartFromBound spliceLaw
    (openPeriodicOverlapUniqueness_of_nonnegativeViscosity hnu)

/-- The coefficient-complete nonnegative-viscosity factorization.  Its explicit bound retains the
analytic constant multiplying both the finite tail length and the accumulated vorticity. -/
def scaledAugmentedCriticalVorticityContinuationFactorization_of_nonnegativeViscosity
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {C : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (scaledAugmentedCriticalVorticityRate C solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw solution) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) * Real.exp (C * (T - a + M)))) :=
  logarithmicHighOrderContinuationFactorization law
    (budget.toScaledAugmentedCriticalRateBudget hC law.base_pos)
    restartFromBound spliceLaw
    (openPeriodicOverlapUniqueness_of_nonnegativeViscosity hnu)

section Audit

#print axioms continuousOn_criticalVorticityRate
#print axioms criticalVorticityRate_le_iff
#print axioms OpenAccumulatedCriticalVorticityBudget.toCriticalRateBudget
#print axioms OpenAccumulatedCriticalVorticityBudget.toAugmentedCriticalRateBudget
#print axioms OpenAccumulatedCriticalVorticityBudget.toScaledAugmentedCriticalRateBudget
#print axioms lifespanLogarithmicLawOfCriticalVorticity
#print axioms lifespanLogarithmicLawOfAugmentedCriticalVorticity
#print axioms lifespanLogarithmicLawOfScaledAugmentedCriticalVorticity
#print axioms uniformOpenHighOrderBound_of_accumulatedCriticalVorticity
#print axioms uniformOpenHighOrderBound_of_augmentedCriticalVorticity
#print axioms criticalVorticityContinuationFactorization
#print axioms augmentedCriticalVorticityContinuationFactorization
#print axioms augmentedCriticalVorticityContinuationFactorization_of_nonnegativeViscosity
#print axioms scaledAugmentedCriticalVorticityContinuationFactorization_of_nonnegativeViscosity

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
