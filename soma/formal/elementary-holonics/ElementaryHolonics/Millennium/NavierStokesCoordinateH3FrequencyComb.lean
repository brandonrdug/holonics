import ElementaryHolonics.Millennium.NavierStokesQuadraticH3Energy
import ElementaryHolonics.Millennium.NavierStokesVorticityStretchingComb

/-!
# The frequency comb on the differentiated coordinate H³ receiver

The first logarithmic frequency-comb owner used the integral of operator norms of
`iteratedFDeriv`.  The exact differentiated energy owner instead returns the finite
coordinate--Frobenius population `coordinateH3Energy`, together with its genuine rate
`coordinateH3TimeWork`.  Those two receivers are not definitionally equal.

This file rebases the same low/middle/high comb on the receiver that is actually differentiated.
It does not postulate a norm-equivalence bridge.  The remaining analytic attachment is now exactly
the coordinate production estimate against the actual Jacobian envelope.
-/

noncomputable section

open Real Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesFrequencyComb
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

/-! ## The differentiated logarithmic receiver -/

/-- The exact coordinate--Frobenius H³ energy, augmented away from the logarithmic origin. -/
def coordinateLogH3Receiver (velocity : VelocityField) (t : ℝ) : ℝ :=
  Real.exp 1 + coordinateH3Energy velocity t

/-- The augmented coordinate receiver dominates its fixed positive base point. -/
theorem exp_one_le_coordinateLogH3Receiver
    (velocity : VelocityField) (t : ℝ) :
    Real.exp 1 ≤ coordinateLogH3Receiver velocity t := by
  exact le_add_of_nonneg_right (coordinateH3Energy_nonneg velocity t)

/-- The coordinate receiver is at least one. -/
theorem one_le_coordinateLogH3Receiver
    (velocity : VelocityField) (t : ℝ) :
    1 ≤ coordinateLogH3Receiver velocity t :=
  (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
    (exp_one_le_coordinateLogH3Receiver velocity t)

/-- Its natural logarithm is at least one. -/
theorem one_le_log_coordinateLogH3Receiver
    (velocity : VelocityField) (t : ℝ) :
    1 ≤ Real.log (coordinateLogH3Receiver velocity t) := by
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (coordinateLogH3Receiver velocity t) :=
      Real.log_le_log (Real.exp_pos 1)
        (exp_one_le_coordinateLogH3Receiver velocity t)

/-- The logarithmic receiver has the already constructed coordinate time-work derivative. -/
theorem openPeriodicSolutionOn_hasDerivAt_coordinateLogH3Receiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (coordinateLogH3Receiver velocity)
      (coordinateH3TimeWork velocity t) t := by
  have henergy := openPeriodicSolutionOn_hasDerivAt_coordinateH3Energy solution ht
  simpa [coordinateLogH3Receiver] using
    (hasDerivAt_const t (Real.exp 1)).add henergy

/-! ## The comb re-indexed by the coordinate receiver -/

/-- Low/middle/high testimony for the actual Jacobian, with the high tail measured by the
differentiated coordinate receiver. -/
structure OpenCoordinateH3FrequencyComb
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (a : ℝ) (jacobian low middle high : ℝ → ℝ) : Prop where
  jacobian_envelope : ∀ t ∈ Ico a T, ∀ x ∈ unitCube,
    ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ jacobian t
  threeBands : ∀ t ∈ Ico a T,
    ThreeBandCombBound
      (jacobian t) (low t) (middle t) (high t) 1
      (criticalVorticityRate solution t) (coordinateLogH3Receiver velocity t)
      (shellDepth (coordinateLogH3Receiver velocity t))

/-- Balancing the three bands returns the raw dyadic logarithmic estimate. -/
theorem OpenCoordinateH3FrequencyComb.jacobian_le_balancedBands
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    {t : ℝ} (ht : t ∈ Ico a T) :
    jacobian t ≤
      2 + (Real.logb 2 (coordinateLogH3Receiver velocity t) + 1) *
        criticalVorticityRate solution t := by
  exact (comb.threeBands t ht).logarithmic_bound_of_low_le_one
    (one_le_coordinateLogH3Receiver velocity t)

/-- The same exact base-conversion constant used by the original comb turns the dyadic chart into
the natural logarithm required by logarithmic Grönwall. -/
theorem OpenCoordinateH3FrequencyComb.jacobian_le_logarithmicH3
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    {t : ℝ} (ht : t ∈ Ico a T) :
    jacobian t ≤
      combLogConstant * augmentedCriticalVorticityRate solution t *
        Real.log (coordinateLogH3Receiver velocity t) := by
  let H : ℝ := coordinateLogH3Receiver velocity t
  let critical : ℝ := criticalVorticityRate solution t
  let q : ℝ := (Real.log 2)⁻¹
  have hraw := comb.jacobian_le_balancedBands ht
  have hcritical : 0 ≤ critical := criticalVorticityRate_nonneg solution t
  have hlog : 1 ≤ Real.log H := one_le_log_coordinateLogH3Receiver velocity t
  have hq : 0 ≤ q := by
    dsimp [q]
    exact inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hlogb : Real.logb 2 H + 1 ≤ (q + 1) * Real.log H := by
    rw [Real.logb, div_eq_mul_inv]
    dsimp [q]
    nlinarith
  have hmiddle :
      (Real.logb 2 H + 1) * critical ≤
        ((q + 1) * Real.log H) * critical :=
    mul_le_mul_of_nonneg_right hlogb hcritical
  have hconstant : 2 ≤ (q + 3) * Real.log H := by
    have hthree : (3 : ℝ) ≤ q + 3 := by linarith
    have hthreeLog : (3 : ℝ) * 1 ≤ (q + 3) * Real.log H :=
      mul_le_mul hthree hlog (by norm_num) (by linarith)
    norm_num at hthreeLog
    exact (by norm_num : (2 : ℝ) ≤ 3).trans hthreeLog
  have hcriticalTerm :
      ((q + 1) * Real.log H) * critical ≤
        ((q + 3) * Real.log H) * critical := by
    apply mul_le_mul_of_nonneg_right _ hcritical
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ Real.log H)
    linarith
  have hfinal :
      jacobian t ≤ (q + 3) * (1 + critical) * Real.log H := by
    calc
      jacobian t ≤ 2 + (Real.logb 2 H + 1) * critical := hraw
      _ ≤ 2 + ((q + 1) * Real.log H) * critical :=
        add_le_add (le_refl 2) hmiddle
      _ ≤ (q + 3) * Real.log H +
            ((q + 3) * Real.log H) * critical :=
        add_le_add hconstant hcriticalTerm
      _ = (q + 3) * (1 + critical) * Real.log H := by ring
  simpa [combLogConstant, augmentedCriticalVorticityRate, H, critical, q, add_comm]
    using hfinal

/-! ## The actual derivative enters the logarithmic law -/

/-- The coefficient carried from coordinate production through the balanced comb. -/
def coordinateH3CombCriticalRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (productionConstant : ℝ)
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ :=
  scaledAugmentedCriticalVorticityRate
    (productionConstant * combLogConstant) solution t

/-- A coordinate production estimate against the actual Jacobian, followed by the balanced comb,
returns the exact logarithmic differential inequality. -/
theorem OpenCoordinateH3FrequencyComb.coordinateH3TimeWork_le_logarithmic
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    {productionConstant : ℝ} (hproductionConstant : 0 ≤ productionConstant)
    {t : ℝ} (ht : t ∈ Ico a T)
    (hproduction : coordinateH3TimeWork velocity t ≤
      productionConstant * jacobian t * coordinateLogH3Receiver velocity t) :
    coordinateH3TimeWork velocity t ≤
      coordinateH3CombCriticalRate productionConstant solution t *
        coordinateLogH3Receiver velocity t *
          Real.log (coordinateLogH3Receiver velocity t) := by
  have hjacobian := comb.jacobian_le_logarithmicH3 ht
  have hreceiver : 0 ≤ coordinateLogH3Receiver velocity t :=
    (one_le_coordinateLogH3Receiver velocity t).trans' zero_le_one
  have hscaled :
      productionConstant * jacobian t * coordinateLogH3Receiver velocity t ≤
        productionConstant *
            (combLogConstant * augmentedCriticalVorticityRate solution t *
              Real.log (coordinateLogH3Receiver velocity t)) *
          coordinateLogH3Receiver velocity t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hjacobian hproductionConstant) hreceiver
  unfold coordinateH3CombCriticalRate scaledAugmentedCriticalVorticityRate
  calc
    coordinateH3TimeWork velocity t ≤
        productionConstant * jacobian t * coordinateLogH3Receiver velocity t := hproduction
    _ ≤ productionConstant *
          (combLogConstant * augmentedCriticalVorticityRate solution t *
            Real.log (coordinateLogH3Receiver velocity t)) *
        coordinateLogH3Receiver velocity t := hscaled
    _ = (productionConstant * combLogConstant *
          augmentedCriticalVorticityRate solution t) *
        coordinateLogH3Receiver velocity t *
          Real.log (coordinateLogH3Receiver velocity t) := by ring

/-- The genuine derivative, the coordinate production estimate, and the re-indexed frequency comb
form the high-order law consumed by the continuation factorization. -/
def lifespanLogarithmicCoordinateH3LawOfFrequencyComb
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (ha : 0 < a) (haT : a < T)
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    (productionConstant : ℝ) (hproductionConstant : 0 ≤ productionConstant)
    (hproduction : ∀ t ∈ Ico a T,
      coordinateH3TimeWork velocity t ≤
        productionConstant * jacobian t * coordinateLogH3Receiver velocity t) :
    LifespanLogarithmicHighOrderLaw T a
      (coordinateLogH3Receiver velocity) (coordinateH3TimeWork velocity)
      (scaledAugmentedCriticalVorticityRate
        (productionConstant * combLogConstant) solution) :=
  lifespanLogarithmicLawOfScaledAugmentedCriticalVorticity
    (productionConstant * combLogConstant) solution ha haT
    (fun t ht => openPeriodicSolutionOn_hasDerivAt_coordinateLogH3Receiver solution
      ⟨lt_of_lt_of_le ha ht.1, ht.2⟩)
    (fun t _ht => one_le_coordinateLogH3Receiver velocity t) (by
      intro t ht
      simpa [coordinateH3CombCriticalRate] using
        comb.coordinateH3TimeWork_le_logarithmic hproductionConstant ht
          (hproduction t ht))

section Audit

#print axioms openPeriodicSolutionOn_hasDerivAt_coordinateLogH3Receiver
#print axioms OpenCoordinateH3FrequencyComb.jacobian_le_logarithmicH3
#print axioms OpenCoordinateH3FrequencyComb.coordinateH3TimeWork_le_logarithmic
#print axioms lifespanLogarithmicCoordinateH3LawOfFrequencyComb

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
