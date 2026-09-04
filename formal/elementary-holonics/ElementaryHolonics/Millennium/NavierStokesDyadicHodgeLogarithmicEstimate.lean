import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailBalance
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-!
# The actual dyadic Hodge logarithmic Jacobian estimate

**[proved-derived, conditional]** The direct dyadic scale word, the quantitative complete
reconstruction fibre, and a scale-uniform physical-kernel receipt compose into the literal
periodic Beale--Kato--Majda logarithmic Jacobian estimate.  The sole premise in this owner is the
named kernel receipt `UniformDyadicHodgeJacobianKernelBound`; the companion kernel owner must
inhabit it from mixed finite-difference/Abel testimony before the result becomes unconditional.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeLogarithmicEstimate

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailBalance
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy

/-- Conversion from the sixfold base-two depth to the natural logarithmic chart. -/
def dyadicHodgeDepthSlope : ℝ :=
  6 * ((Real.log 2)⁻¹ + 1)

theorem dyadicHodgeDepthSlope_nonneg : 0 ≤ dyadicHodgeDepthSlope := by
  unfold dyadicHodgeDepthSlope
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  positivity

/-- Fixed payment for the complete reconstruction fibre after balancing its actual `H³` tail. -/
def balancedDyadicHodgeTailConstant : ℝ :=
  2 * ((2 * Real.pi) * Real.sqrt 240 * Real.sqrt jacobianTailLatticeMass)

theorem balancedDyadicHodgeTailConstant_nonneg :
    0 ≤ balancedDyadicHodgeTailConstant := by
  unfold balancedDyadicHodgeTailConstant
  positivity

/-- Full matrix, dyadic-depth, and reconstruction-fibre coefficient. -/
def dyadicHodgeLogarithmicConstant (kernelConstant : ℝ) : ℝ :=
  9 * (81 + dyadicHodgeDepthSlope * kernelConstant +
    balancedDyadicHodgeTailConstant)

theorem dyadicHodgeLogarithmicConstant_nonneg
    {kernelConstant : ℝ}
    (hkernel : 0 ≤ kernelConstant) :
    0 ≤ dyadicHodgeLogarithmicConstant kernelConstant := by
  unfold dyadicHodgeLogarithmicConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (add_nonneg (by norm_num)
        (mul_nonneg dyadicHodgeDepthSlope_nonneg hkernel))
      balancedDyadicHodgeTailConstant_nonneg)

/-- **Actual logarithmic Hodge estimate.**  Every spatial derivative receiver is bounded by the
critical vorticity rate times the logarithm of the differentiated coordinate `H³` receiver, with
all low, dyadic-middle, matrix, and complete-tail constants displayed. -/
theorem coordinateJacobianReceiver_le_dyadicHodge_logarithmic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {kernelConstant : ℝ}
    (hkernel : UniformDyadicHodgeJacobianKernelBound kernelConstant) :
    coordinateJacobianReceiver solution t ≤
      dyadicHodgeLogarithmicConstant kernelConstant *
        augmentedCriticalVorticityRate solution t *
          Real.log (coordinateLogH3Receiver velocity t) := by
  let highOrder : ℝ := coordinateLogH3Receiver velocity t
  let critical : ℝ := criticalVorticityRate solution t
  let depth : ℕ := jacobianTailDyadicDepth highOrder
  let tail : ℝ := openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
    (frequencyCube (dyadicHodgeInnerCutoff depth))
  have hraw := coordinateJacobianReceiver_le_of_uniformDyadicKernelBound
    solution ht hkernel depth
  have hcutoff : dyadicHodgeInnerCutoff depth =
      jacobianTailDyadicRadius highOrder := by
    simp [dyadicHodgeInnerCutoff, dyadicRadius, depth,
      jacobianTailDyadicRadius]
  have htailBase := openPeriodicJacobianCoefficientTailMass_balanced_le
    solution ht
  have htail : tail ≤
      (2 * Real.pi) * Real.sqrt 240 * Real.sqrt jacobianTailLatticeMass := by
    dsimp [tail]
    rw [hcutoff]
    exact htailBase
  have hdepth : (depth : ℝ) ≤
      dyadicHodgeDepthSlope * Real.log highOrder := by
    dsimp [depth, highOrder]
    simpa only [dyadicHodgeDepthSlope, mul_assoc] using
      jacobianTailDyadicDepth_coordinateLogH3Receiver_le velocity t
  have hcritical : 0 ≤ critical := by
    dsimp [critical]
    exact criticalVorticityRate_nonneg solution t
  have hlog : 1 ≤ Real.log highOrder := by
    dsimp [highOrder]
    exact one_le_log_coordinateLogH3Receiver velocity t
  have hdepthSlope : 0 ≤ dyadicHodgeDepthSlope :=
    dyadicHodgeDepthSlope_nonneg
  have hkernelNonneg : 0 ≤ kernelConstant := hkernel.1
  have htailConstant : 0 ≤ balancedDyadicHodgeTailConstant :=
    balancedDyadicHodgeTailConstant_nonneg
  have hcriticalAugmented :
      critical ≤ (1 + critical) * Real.log highOrder := by
    calc
      critical ≤ critical * Real.log highOrder := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hlog hcritical
      _ ≤ (1 + critical) * Real.log highOrder := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (by linarith : 0 ≤ Real.log highOrder)
  have hlow : 81 * critical ≤
      81 * ((1 + critical) * Real.log highOrder) :=
    mul_le_mul_of_nonneg_left hcriticalAugmented (by norm_num)
  have hmiddle : (depth : ℝ) * (kernelConstant * critical) ≤
      (dyadicHodgeDepthSlope * kernelConstant) *
        ((1 + critical) * Real.log highOrder) := by
    calc
      (depth : ℝ) * (kernelConstant * critical) ≤
          (dyadicHodgeDepthSlope * Real.log highOrder) *
            (kernelConstant * critical) :=
        mul_le_mul_of_nonneg_right hdepth
          (mul_nonneg hkernelNonneg hcritical)
      _ ≤ (dyadicHodgeDepthSlope * kernelConstant) *
          ((1 + critical) * Real.log highOrder) := by
        have hcriticalOne : critical ≤ 1 + critical := by linarith
        have hscaled := mul_le_mul_of_nonneg_left hcriticalOne
          (mul_nonneg hdepthSlope hkernelNonneg)
        nlinarith [hscaled]
  have honeProduct : 1 ≤ (1 + critical) * Real.log highOrder := by
    calc
      1 ≤ 1 + critical := by linarith
      _ ≤ (1 + critical) * Real.log highOrder := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog (by linarith)
  have htailScaled : 2 * tail ≤
      balancedDyadicHodgeTailConstant *
        ((1 + critical) * Real.log highOrder) := by
    calc
      2 * tail ≤ balancedDyadicHodgeTailConstant := by
        unfold balancedDyadicHodgeTailConstant
        exact mul_le_mul_of_nonneg_left htail (by norm_num)
      _ ≤ balancedDyadicHodgeTailConstant *
          ((1 + critical) * Real.log highOrder) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left honeProduct htailConstant
  have hinside :
      81 * critical +
          (depth : ℝ) * (kernelConstant * critical) + 2 * tail ≤
        (81 + dyadicHodgeDepthSlope * kernelConstant +
          balancedDyadicHodgeTailConstant) *
            ((1 + critical) * Real.log highOrder) := by
    calc
      81 * critical +
          (depth : ℝ) * (kernelConstant * critical) + 2 * tail ≤
        81 * ((1 + critical) * Real.log highOrder) +
          (dyadicHodgeDepthSlope * kernelConstant) *
            ((1 + critical) * Real.log highOrder) +
          balancedDyadicHodgeTailConstant *
            ((1 + critical) * Real.log highOrder) :=
        add_le_add (add_le_add hlow hmiddle) htailScaled
      _ = (81 + dyadicHodgeDepthSlope * kernelConstant +
          balancedDyadicHodgeTailConstant) *
            ((1 + critical) * Real.log highOrder) := by ring
  calc
    coordinateJacobianReceiver solution t ≤
        9 * (81 * critical +
          (depth : ℝ) * (kernelConstant * critical) + 2 * tail) := by
      simpa only [critical, depth, tail] using hraw
    _ ≤ 9 * ((81 + dyadicHodgeDepthSlope * kernelConstant +
          balancedDyadicHodgeTailConstant) *
            ((1 + critical) * Real.log highOrder)) :=
      mul_le_mul_of_nonneg_left hinside (by norm_num)
    _ = dyadicHodgeLogarithmicConstant kernelConstant *
        augmentedCriticalVorticityRate solution t *
          Real.log (coordinateLogH3Receiver velocity t) := by
      dsimp [critical, highOrder]
      unfold dyadicHodgeLogarithmicConstant augmentedCriticalVorticityRate
      ring

/-! ## The direct dyadic BKM law on the actual forty-face receiver -/

/-- The completed coordinate production identity and the direct dyadic Hodge estimate form the
literal logarithmic high-order law.  The only remaining premise is the uniform physical dyadic
kernel bound; no abstract comb or high-order differential inequality is accepted here. -/
def lifespanLogarithmicCoordinateH3LawOfDyadicHodge
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (haT : a < T) (hnu : 0 ≤ nu)
    {kernelConstant : ℝ}
    (hkernel : UniformDyadicHodgeJacobianKernelBound kernelConstant) :
    LifespanLogarithmicHighOrderLaw T a
      (coordinateLogH3Receiver velocity) (coordinateH3TimeWork velocity)
      (scaledAugmentedCriticalVorticityRate
        (10986 * dyadicHodgeLogarithmicConstant kernelConstant) solution) :=
  lifespanLogarithmicLawOfScaledAugmentedCriticalVorticity
    (10986 * dyadicHodgeLogarithmicConstant kernelConstant) solution ha haT
    (fun t ht ↦ openPeriodicSolutionOn_hasDerivAt_coordinateLogH3Receiver solution
      ⟨lt_of_lt_of_le ha ht.1, ht.2⟩)
    (fun t _ht ↦ one_le_coordinateLogH3Receiver velocity t) (by
      intro t ht
      have htInterior : t ∈ Ioo 0 T := ⟨lt_of_lt_of_le ha ht.1, ht.2⟩
      have hproduction :=
        openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_actualJacobian
          solution htInterior hnu
      have hjacobian :=
        coordinateJacobianReceiver_le_dyadicHodge_logarithmic
          solution htInterior hkernel
      have hreceiver : 0 ≤ coordinateLogH3Receiver velocity t :=
        zero_le_one.trans (one_le_coordinateLogH3Receiver velocity t)
      have hscaled :
          10986 * coordinateJacobianReceiver solution t *
              coordinateLogH3Receiver velocity t ≤
            10986 *
                (dyadicHodgeLogarithmicConstant kernelConstant *
                  augmentedCriticalVorticityRate solution t *
                    Real.log (coordinateLogH3Receiver velocity t)) *
              coordinateLogH3Receiver velocity t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hjacobian (by norm_num)) hreceiver
      unfold scaledAugmentedCriticalVorticityRate
      calc
        coordinateH3TimeWork velocity t ≤
            10986 * coordinateJacobianReceiver solution t *
              coordinateLogH3Receiver velocity t := hproduction
        _ ≤ 10986 *
              (dyadicHodgeLogarithmicConstant kernelConstant *
                augmentedCriticalVorticityRate solution t *
                  Real.log (coordinateLogH3Receiver velocity t)) *
            coordinateLogH3Receiver velocity t := hscaled
        _ = (10986 * dyadicHodgeLogarithmicConstant kernelConstant *
              augmentedCriticalVorticityRate solution t) *
            coordinateLogH3Receiver velocity t *
              Real.log (coordinateLogH3Receiver velocity t) := by ring)

section Audit

#print axioms coordinateJacobianReceiver_le_dyadicHodge_logarithmic
#print axioms lifespanLogarithmicCoordinateH3LawOfDyadicHodge

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeLogarithmicEstimate
