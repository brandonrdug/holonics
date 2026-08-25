import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge

/-!
# Cross-difference reconstruction of the vorticity direction remainder

**[proved-derived]** The canonical direction remainder was defined by a scalar projection chart.
This owner returns its geometric carrier.  Crossing the source with the receiver annihilates the
aligned face, and the vector triple-product reconstructs the complete orthogonal remainder whenever
the receiver has nonzero self-pairing.  Thus the cross-difference is a lossless chart for precisely
the direction population seen by stretching.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge

/-- The oriented geometric difference between a receiving direction and one source occurrence. -/
def receiverCrossDifference (receiver source : ComplexVector) : ComplexVector :=
  complexCross receiver source

/-- Crossing annihilates every component aligned with the receiver, so it depends only on the
canonical returned direction difference. -/
theorem receiverCrossDifference_directionRemainder
    (receiver source : ComplexVector) :
    receiverCrossDifference receiver (receiverDirectionRemainder receiver source) =
      receiverCrossDifference receiver source := by
  funext component
  fin_cases component <;>
    simp [receiverCrossDifference, receiverDirectionRemainder, complexCross, crossProduct] <;>
    ring

@[simp]
theorem complexCross_zero_left (v : ComplexVector) :
    complexCross 0 v = 0 := by
  funext component
  fin_cases component <;> simp [complexCross, crossProduct]

@[simp]
theorem complexCross_zero_right (v : ComplexVector) :
    complexCross v 0 = 0 := by
  funext component
  fin_cases component <;> simp [complexCross, crossProduct]

/-- A nonisotropic receiver reconstructs its complete canonical orthogonal remainder from the
double cross.  This is the exact geometric inverse chart. -/
theorem receiverDirectionRemainder_eq_inv_smul_crossDifference_cross
    {receiver source : ComplexVector}
    (hreceiver : complexDot receiver receiver ≠ 0) :
    receiverDirectionRemainder receiver source =
      (complexDot receiver receiver)⁻¹ •
        complexCross (receiverCrossDifference receiver source) receiver := by
  let remainder := receiverDirectionRemainder receiver source
  have horthogonal : complexDot receiver remainder = 0 :=
    complexDot_receiverDirectionRemainder_eq_zero hreceiver
  have hreverseOrthogonal : complexDot remainder receiver = 0 := by
    rw [complexDot, dotProduct_comm]
    exact horthogonal
  have htriple := cross_cross_eq_smul_sub_smul receiver remainder receiver
  change
    complexCross (complexCross receiver remainder) receiver =
      (complexDot receiver receiver) • remainder -
        (complexDot remainder receiver) • receiver at htriple
  rw [hreverseOrthogonal, zero_smul, sub_zero] at htriple
  have hcross : complexCross receiver remainder =
      receiverCrossDifference receiver source := by
    simpa [receiverCrossDifference] using
      receiverCrossDifference_directionRemainder receiver source
  rw [hcross] at htriple
  change remainder = _
  rw [htriple, smul_smul, inv_mul_cancel₀ hreceiver, one_smul]

/-- For an open projection chart, vanishing cross difference is equivalent to vanishing canonical
direction remainder.  No magnitude or scalar projection receiver can make this distinction. -/
theorem receiverCrossDifference_eq_zero_iff_directionRemainder_eq_zero
    {receiver source : ComplexVector}
    (hreceiver : complexDot receiver receiver ≠ 0) :
    receiverCrossDifference receiver source = 0 ↔
      receiverDirectionRemainder receiver source = 0 := by
  constructor
  · intro hcross
    rw [receiverDirectionRemainder_eq_inv_smul_crossDifference_cross hreceiver,
      hcross]
    simp
  · intro hremainder
    rw [← receiverCrossDifference_directionRemainder receiver source, hremainder]
    exact complexCross_zero_right receiver

/-- Exact `L¹` transport through a complex scalar. -/
theorem complexVectorL1_smul (amplitude : ℂ) (v : ComplexVector) :
    complexVectorL1 (amplitude • v) = ‖amplitude‖ * complexVectorL1 v := by
  simp [complexVectorL1]
  ring

/-- The norm of the canonical projection remainder is controlled by its lossless cross chart and
the exact inverse self-pairing aperture. -/
theorem complexVectorL1_receiverDirectionRemainder_le_crossDifference
    {receiver source : ComplexVector}
    (hreceiver : complexDot receiver receiver ≠ 0) :
    complexVectorL1 (receiverDirectionRemainder receiver source) ≤
      ‖(complexDot receiver receiver)⁻¹‖ *
        (complexVectorL1 (receiverCrossDifference receiver source) *
          complexVectorL1 receiver) := by
  rw [receiverDirectionRemainder_eq_inv_smul_crossDifference_cross hreceiver,
    complexVectorL1_smul]
  exact mul_le_mul_of_nonneg_left
    (complexVectorL1_cross_le_mul
      (receiverCrossDifference receiver source) receiver)
    (norm_nonneg _)

/-- The complete finite population of oriented cross differences, retaining every frequency
address. -/
def finiteCrossDirectionMass
    (modes : Finset SpatialFrequency) (receiver : ComplexVector)
    (source : SpatialFrequency → ComplexVector) : ℝ :=
  ∑ frequency ∈ modes,
    complexVectorL1 (receiverCrossDifference receiver (source frequency))

/-- On every open receiver chart, the complete finite canonical-remainder population factors
through the geometric cross-difference population with one exact receiver aperture. -/
theorem finiteDirectionRemainderMass_le_crossDirectionMass
    (modes : Finset SpatialFrequency) {receiver : ComplexVector}
    (source : SpatialFrequency → ComplexVector)
    (hreceiver : complexDot receiver receiver ≠ 0) :
    finiteDirectionRemainderMass modes receiver source ≤
      ‖(complexDot receiver receiver)⁻¹‖ * complexVectorL1 receiver *
        finiteCrossDirectionMass modes receiver source := by
  unfold finiteDirectionRemainderMass finiteCrossDirectionMass
  calc
    (∑ frequency ∈ modes,
        complexVectorL1 (receiverDirectionRemainder receiver (source frequency))) ≤
      ∑ frequency ∈ modes,
        ‖(complexDot receiver receiver)⁻¹‖ *
          (complexVectorL1
              (receiverCrossDifference receiver (source frequency)) *
            complexVectorL1 receiver) := by
      gcongr with frequency hfrequency
      exact complexVectorL1_receiverDirectionRemainder_le_crossDifference hreceiver
    _ = ‖(complexDot receiver receiver)⁻¹‖ * complexVectorL1 receiver *
        ∑ frequency ∈ modes,
          complexVectorL1 (receiverCrossDifference receiver (source frequency)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      ring

/-- The finite stretching reading is now controlled by a geometric cross-difference population,
not by the scalar-projection chart from which it was derived. -/
theorem norm_finiteHodgeStrainReading_le_crossDirectionMass
    (modes : Finset SpatialFrequency) {receiver : ComplexVector}
    (source : SpatialFrequency → ComplexVector)
    (hreceiver : complexDot receiver receiver ≠ 0) :
    ‖finiteHodgeStrainReading modes receiver source‖ ≤
      3 * complexVectorL1 receiver ^ 2 *
        (‖(complexDot receiver receiver)⁻¹‖ * complexVectorL1 receiver *
          finiteCrossDirectionMass modes receiver source) := by
  exact (norm_finiteHodgeStrainReading_le_directionRemainderMass
      modes receiver source).trans
    (mul_le_mul_of_nonneg_left
      (finiteDirectionRemainderMass_le_crossDirectionMass
        modes source hreceiver)
      (mul_nonneg (by positivity) (sq_nonneg _)))

/-- The actual finite cross-direction population for one periodic solution receiver. -/
def openPeriodicFiniteCrossDirectionMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) : ℝ :=
  finiteCrossDirectionMass modes
    (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q)

/-- **[proved-derived; formal-checked]** The complete physical stretching occurrence is bounded
by the lossless cross-difference population plus the exact reconstruction tail.  At zero
vorticity both terms vanish through the receiving factor; elsewhere the triple-product inverse
opens canonically. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_crossDirection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicFiniteCrossDirectionMass solution t q (frequencyCube radius)) +
        ((2 * Real.pi) *
            Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  by_cases hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) = 0
  · have htorus : torusVorticityEvolution solution t q = 0 := by
      change vorticityField velocity (euclideanRepresentative q) t.1 = 0
      simpa [vorticityField] using hvorticity
    have hreceiver : openPeriodicComplexVorticityAt solution t q = 0 := by
      rw [openPeriodicComplexVorticityAt_eq_torusComplexification, htorus]
      rfl
    simp [openPeriodicPhysicalVortexStretchingAt, htorus, hreceiver,
      complexVectorL1]
  · have hreceiver :=
      openPeriodicComplexVorticityAt_self_ne_zero solution t q hvorticity
    have hremainder := finiteDirectionRemainderMass_le_crossDirectionMass
      (frequencyCube radius)
      (openPeriodicTransportedVorticityMode solution t q) hreceiver
    have hfinite :
        3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
            finiteDirectionRemainderMass (frequencyCube radius)
              (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicTransportedVorticityMode solution t q) ≤
          3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
            (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                  (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
              complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
                openPeriodicFiniteCrossDirectionMass solution t q
                  (frequencyCube radius)) := by
      exact mul_le_mul_of_nonneg_left hremainder
        (mul_nonneg (by positivity) (sq_nonneg _))
    exact (abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le
      solution t q radius).trans (add_le_add_left hfinite _)

section Audit

#print axioms receiverCrossDifference_directionRemainder
#print axioms complexCross_zero_left
#print axioms complexCross_zero_right
#print axioms receiverDirectionRemainder_eq_inv_smul_crossDifference_cross
#print axioms receiverCrossDifference_eq_zero_iff_directionRemainder_eq_zero
#print axioms complexVectorL1_smul
#print axioms complexVectorL1_receiverDirectionRemainder_le_crossDifference
#print axioms finiteDirectionRemainderMass_le_crossDirectionMass
#print axioms norm_finiteHodgeStrainReading_le_crossDirectionMass
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_crossDirection

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
