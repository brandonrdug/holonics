import ElementaryHolonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
import ElementaryHolonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
import ElementaryHolonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

/-!
# Test-aware payment of the H2 source-phase current

**[proved-derived; formal-checked]**  The polar split of the actual sharp-source curl does not by
itself bound a signed `H2` production reading: production also carries the derivative-weighted
velocity test occurrence.  This file supplies the sharp finite-dimensional incidence which was
missing from the split.  Every Hermitian source-test reading is bounded by the product of the
explicit `L1` test receiver and the complete phase-plus-aligned source population.  The estimate
then passes to every finite Fourier aperture of the actual compact source.

An exact scaling separator proves that the test receiver cannot be erased.  Even with the
receiver, source, phase fibre, and aligned face fixed, rescaling only the test makes the signed
production arbitrarily large.  Thus the next Navier--Stokes theorem must control the
derivative-weighted test/source product (and identify its cofinal Parseval return with coordinate
`P2`); a source-polar-mass estimate alone cannot be the missing terminal law.
-/

noncomputable section

open Real
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2ProductionPhaseTestBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesDirectionDepletedH2Production
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

/-! ## The derivative-weighted test incidence -/

/-- A Hermitian production reading is paid by the explicit three-component `L1` receivers of
both its test occurrence and its transported source occurrence. -/
theorem abs_sourceTestProductionReading_le_test_mul_source
    (test source : ComplexVector) :
    |sourceTestProductionReading test source| ≤
      complexVectorL1 test * complexVectorL1 source := by
  unfold sourceTestProductionReading
  calc
    |(∑ component : Fin 3,
        (starRingEnd ℂ) (test component) * source component).re| ≤
        ‖∑ component : Fin 3,
          (starRingEnd ℂ) (test component) * source component‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ component : Fin 3,
        ‖(starRingEnd ℂ) (test component) * source component‖ :=
      norm_sum_le _ _
    _ = ‖test 0‖ * ‖source 0‖ +
          ‖test 1‖ * ‖source 1‖ +
            ‖test 2‖ * ‖source 2‖ := by
      simp [Fin.sum_univ_succ]
      ring
    _ ≤ complexVectorL1 test * complexVectorL1 source := by
      unfold complexVectorL1
      nlinarith [norm_nonneg (test 0), norm_nonneg (test 1), norm_nonneg (test 2),
        norm_nonneg (source 0), norm_nonneg (source 1), norm_nonneg (source 2),
        mul_nonneg (norm_nonneg (test 0)) (norm_nonneg (source 1)),
        mul_nonneg (norm_nonneg (test 0)) (norm_nonneg (source 2)),
        mul_nonneg (norm_nonneg (test 1)) (norm_nonneg (source 0)),
        mul_nonneg (norm_nonneg (test 1)) (norm_nonneg (source 2)),
        mul_nonneg (norm_nonneg (test 2)) (norm_nonneg (source 0)),
        mul_nonneg (norm_nonneg (test 2)) (norm_nonneg (source 1))]

/-- The complete polar reconstruction becomes an unconditional upper estimate once the actual
test occurrence is retained.  This is the strongest source-split estimate before a PDE-specific
bound on the derivative-weighted test/source product. -/
theorem abs_sourceTestProductionReading_le_test_mul_polar
    (receiver source test : ComplexVector) :
    |sourceTestProductionReading test source| ≤
      complexVectorL1 test *
        (complexVectorL1 (receiverDirectionRemainder receiver source) +
          complexVectorL1
            (receiverAlignedAmplitude receiver source • receiver)) := by
  have hreconstruct := receiverDirectionRemainder_add_aligned receiver source
  calc
    |sourceTestProductionReading test source| ≤
        complexVectorL1 test * complexVectorL1 source :=
      abs_sourceTestProductionReading_le_test_mul_source test source
    _ = complexVectorL1 test *
        complexVectorL1
          (receiverDirectionRemainder receiver source +
            receiverAlignedAmplitude receiver source • receiver) := by
      rw [hreconstruct]
    _ ≤ complexVectorL1 test *
        (complexVectorL1 (receiverDirectionRemainder receiver source) +
          complexVectorL1
            (receiverAlignedAmplitude receiver source • receiver)) :=
      mul_le_mul_of_nonneg_left
        (complexVectorL1_add_le _ _) (complexVectorL1_nonneg test)

/-! ## The actual compact source and finite Fourier aperture -/

/-- The actual compact sharp-source mode inherits the test-aware polar estimate with no new
hypothesis. -/
theorem abs_compactH2ProductionCompleteTestReading_le_test_mul_polar
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (test : ComplexVector) :
    |compactH2ProductionCompleteTestReading
        solution ha hab hbT frequency sourceTime test| ≤
      complexVectorL1 test *
        (complexVectorL1
            (compactH2ProductionPhaseRemainderMode
              solution ha hab hbT q frequency sourceTime) +
          complexVectorL1
            (compactH2ProductionAlignedMode
              solution ha hab hbT q frequency sourceTime)) := by
  unfold compactH2ProductionCompleteTestReading
    compactH2ProductionPhaseRemainderMode compactH2ProductionAlignedMode
    compactH2ProductionAlignedAmplitude compactH2ProductionDirectionReceiver
  exact abs_sourceTestProductionReading_le_test_mul_polar _ _ _

/-- Complete test-weighted phase-plus-aligned population on a finite Fourier aperture. -/
def compactFiniteH2CurlPolarTestMassAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    complexVectorL1
        (compactH2CurlEnergyTestMode solution ha hab hbT frequency sourceTime) *
      (complexVectorL1
          (compactH2ProductionPhaseRemainderMode
            solution ha hab hbT q frequency sourceTime) +
        complexVectorL1
          (compactH2ProductionAlignedMode
            solution ha hab hbT q frequency sourceTime))

theorem compactFiniteH2CurlPolarTestMassAt_nonneg
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) :
    0 ≤ compactFiniteH2CurlPolarTestMassAt
      solution ha hab hbT q modes sourceTime := by
  unfold compactFiniteH2CurlPolarTestMassAt
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    mul_nonneg (complexVectorL1_nonneg _)
      (add_nonneg (complexVectorL1_nonneg _) (complexVectorL1_nonneg _))

/-- Every actual finite-aperture signed curl-energy reading is unconditionally bounded by the
test-aware polar population.  The derivative weight is visible rather than hidden in a constant. -/
theorem abs_compactFiniteH2CurlCompleteAt_le_polarTestMass
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) :
    |compactFiniteH2CurlCompleteAt solution ha hab hbT modes sourceTime| ≤
      compactFiniteH2CurlPolarTestMassAt
        solution ha hab hbT q modes sourceTime := by
  unfold compactFiniteH2CurlCompleteAt compactFiniteH2CurlPolarTestMassAt
  calc
    |∑ frequency ∈ modes,
        compactH2ProductionCompleteTestReading
          solution ha hab hbT frequency sourceTime
            (compactH2CurlEnergyTestMode
              solution ha hab hbT frequency sourceTime)| ≤
        ∑ frequency ∈ modes,
          |compactH2ProductionCompleteTestReading
            solution ha hab hbT frequency sourceTime
              (compactH2CurlEnergyTestMode
                solution ha hab hbT frequency sourceTime)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun frequency _hfrequency ↦
      abs_compactH2ProductionCompleteTestReading_le_test_mul_polar
        solution ha hab hbT q frequency sourceTime
          (compactH2CurlEnergyTestMode
            solution ha hab hbT frequency sourceTime)

/-! ## The literal coordinate P2 receiver -/

/-- The actual signed coordinate `P2` current has an unconditional, noncircular pointwise upper
estimate.  The coefficient is the genuine cube-gradient receiver and the payment is the actual
`H2` storage plus the actual `H3` viscous current.  This theorem does not close the endpoint:
the gradient receiver is precisely the unsummed time/current face which the phase/dyadic route
would have to replace or absorb. -/
theorem openPeriodicSolutionOn_coordinateH2NonlinearProductionCurrent_le_gradient_mul_storage_add_dissipation
    {T nu : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    coordinateH2NonlinearProductionCurrent velocity t ≤
      240 * cubeGradientSup (fun x ↦ velocity x t) *
        (coordinateH2Energy velocity t +
          coordinateH3ViscousDissipation velocity t) := by
  let M : ℝ := cubeGradientSup (fun x ↦ velocity x t)
  have hfirst :=
    openPeriodicSolutionOn_neg_coordinateH1StretchingWork_le solution ht
  have hsecond :=
    openPeriodicSolutionOn_neg_coordinateH2LowerWork_le solution ht
  have hproductionToH3 :
      coordinateH2NonlinearProductionCurrent velocity t ≤
        240 * M * coordinateH3Energy velocity t := by
    unfold coordinateH2NonlinearProductionCurrent
    dsimp only [M] at hfirst hsecond ⊢
    linarith
  have hM : 0 ≤ M := by
    exact cubeGradientSup_nonneg (fun x ↦ velocity x t)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
  have hsplit :=
    openPeriodicSolutionOn_coordinateH3Energy_eq_H2Energy_add_half_H2Dissipation
      solution ht
  have h0 := coordinateH0Dissipation_nonneg velocity t
  have h1 := coordinateH1Dissipation_nonneg velocity t
  have h2 := coordinateH2Dissipation_nonneg velocity t
  have hH3 :
      coordinateH3Energy velocity t ≤
        coordinateH2Energy velocity t +
          coordinateH3ViscousDissipation velocity t := by
    rw [hsplit]
    unfold coordinateH3ViscousDissipation
    nlinarith
  exact hproductionToH3.trans
    (mul_le_mul_of_nonneg_left hH3 (mul_nonneg (by norm_num) hM))

/-! ## Exact obstruction to a source-only production estimate -/

/-- **[counterexample; formal-checked]** There is no uniform scalar bound for all production
tests in terms of only the source's phase and aligned masses.  The source polar faces stay fixed
while the derivative-weighted test is rescaled. -/
theorem no_uniform_sourcePolarMass_bound_for_productionTests :
    ¬ ∃ constant : ℝ,
      ∀ (receiver source test : ComplexVector),
        |sourceTestProductionReading test source| ≤
          constant *
            (complexVectorL1 (receiverDirectionRemainder receiver source) +
              complexVectorL1
                (receiverAlignedAmplitude receiver source • receiver)) := by
  rintro ⟨constant, hbound⟩
  let amplitude : ℝ := |constant| + 1
  let test : ComplexVector :=
    ((amplitude : ℂ) • orthogonalSeparatorOutput)
  have h := hbound orthogonalSeparatorReceiver orthogonalSeparatorOutput test
  have hamplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hreading :
      sourceTestProductionReading test orthogonalSeparatorOutput = amplitude := by
    simp [sourceTestProductionReading, test, amplitude, orthogonalSeparatorOutput]
  have haligned :
      receiverAlignedAmplitude orthogonalSeparatorReceiver orthogonalSeparatorOutput •
          orthogonalSeparatorReceiver = 0 := by
    simp [receiverAlignedAmplitude, orthogonalSeparatorReceiver,
      orthogonalSeparatorOutput, complexDot, dotProduct]
  rw [hreading, abs_of_nonneg hamplitude,
    receiverDirectionRemainder_orthogonalSeparator,
    complexVectorL1_orthogonalSeparatorOutput, haligned] at h
  simp [complexVectorL1] at h
  dsimp [amplitude] at h
  linarith [le_abs_self constant]

section Audit

#print axioms abs_sourceTestProductionReading_le_test_mul_source
#print axioms abs_sourceTestProductionReading_le_test_mul_polar
#print axioms abs_compactH2ProductionCompleteTestReading_le_test_mul_polar
#print axioms abs_compactFiniteH2CurlCompleteAt_le_polarTestMass
#print axioms
  openPeriodicSolutionOn_coordinateH2NonlinearProductionCurrent_le_gradient_mul_storage_add_dissipation
#print axioms no_uniform_sourcePolarMass_bound_for_productionTests

end Audit

end Soma.Holonics.Millennium.NavierStokesH2ProductionPhaseTestBound
