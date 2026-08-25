import ElementaryHolonics.Millennium.NavierStokesFiniteTimeContinuation
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-!
# The constructed spatial coherence closes into the enstrophy receiver

**[proved-derived]** The physical source modulus and the summable dyadic Hodge distance moments
now control the complete spatially integrated vortex-stretching occurrence.  The reciprocal
receiver in the direction reconstruction is not discarded: on the real vorticity locus it cancels
two of the four vorticity powers exactly up to the explicit coordinate `L¹` constant.

The resulting coefficient is finite on every strict-interior time slice.  Its only unreturned
face is terminal-time control of the selected compact-chart vorticity Lipschitz constant; this file
does not infer such control from pointwise smoothness on the open lifespan.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-! ## Cancellation of the reciprocal direction receiver -/

/-- On the real vorticity locus, the inverse quadratic direction receiver cancels two powers of
the coordinate `L¹` population.  The constant `81 = 3⁴` retains the four coordinate-comparison
occurrences used by the current receiver. -/
theorem norm_inverse_complexDot_mul_complexVectorL1_pow_four_le
    (v : Space) :
    ‖(complexDot (complexOfRealSpace v) (complexOfRealSpace v))⁻¹‖ *
        complexVectorL1 (complexOfRealSpace v) ^ 4 ≤
      81 * ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv, complexDot, complexOfRealSpace, complexVectorL1]
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hvnormPos : 0 < ‖v‖ := (norm_pos_iff.mpr hv)
  have hdot :
      complexDot (complexOfRealSpace v) (complexOfRealSpace v) =
        ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [complexDot_complexOfRealSpace]
    simp
  have hl1 := complexVectorL1_complexOfRealSpace_le_three_norm v
  have hl1Nonneg : 0 ≤ complexVectorL1 (complexOfRealSpace v) :=
    complexVectorL1_nonneg _
  rw [hdot, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖v‖)]
  calc
    (‖v‖ ^ 2)⁻¹ * complexVectorL1 (complexOfRealSpace v) ^ 4 ≤
        (‖v‖ ^ 2)⁻¹ * (3 * ‖v‖) ^ 4 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hl1Nonneg hl1 4)
        (inv_nonneg.mpr (sq_nonneg ‖v‖))
    _ = 81 * ‖v‖ ^ 2 := by
      field_simp
      ring

/-! ## The exact coefficient returned to the spatial integral -/

/-- The complete first-distance moment population of the actual dyadic Hodge kernel. -/
def totalDyadicHodgeDistanceMoment : ℝ :=
  ∑' scale : ℕ,
    dyadicHodgeJacobianKernelModulusMoment (torusDistancePowerModulus 1) scale

theorem totalDyadicHodgeDistanceMoment_nonneg :
    0 ≤ totalDyadicHodgeDistanceMoment := by
  exact tsum_nonneg fun scale ↦
    dyadicHodgeJacobianKernelModulusMoment_nonneg
      (torusDistancePowerModulus 1)
      (torusDistancePowerModulus_nonneg 1) scale

/-- The source-specific coefficient remaining after all spatial scales and the complete unit cube
have been composed. -/
def openPeriodicVorticityDirectionEnstrophyCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  (13122 * Real.pi) *
      Real.sqrt (2 * periodicKineticEnergy velocity t.1) +
    729 * (openPeriodicVorticityLipschitzConstant solution t : ℝ) *
      totalDyadicHodgeDistanceMoment

theorem openPeriodicVorticityDirectionEnstrophyCoefficient_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ openPeriodicVorticityDirectionEnstrophyCoefficient solution t := by
  unfold openPeriodicVorticityDirectionEnstrophyCoefficient
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      (Real.sqrt_nonneg _))
    (mul_nonneg
      (mul_nonneg (by norm_num) (NNReal.coe_nonneg _))
      totalDyadicHodgeDistanceMoment_nonneg)

/-- **[proved-derived; formal-checked]** The spatial coherence return is now a genuine pointwise
enstrophy-density law.  No spatial summability premise and no Fourier aperture remain. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_enstrophyDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        ‖torusVorticityEvolution solution t q‖ ^ 2 := by
  let omega : Space := torusVorticityEvolution solution t q
  let omegaComplex : ComplexVector := openPeriodicComplexVorticityAt solution t q
  let lipschitz : ℝ := openPeriodicVorticityLipschitzConstant solution t
  let moment : ℝ := totalDyadicHodgeDistanceMoment
  let base : ℝ :=
    (1458 * Real.pi) * Real.sqrt (2 * periodicKineticEnergy velocity t.1)
  have homegaComplex : omegaComplex = complexOfRealSpace omega := by
    exact openPeriodicComplexVorticityAt_eq_torusComplexification solution t q
  have hbaseNonneg : 0 ≤ base := by
    dsimp [base]
    positivity
  have hlipschitzNonneg : 0 ≤ lipschitz := by
    exact NNReal.coe_nonneg _
  have hmomentNonneg : 0 ≤ moment := by
    exact totalDyadicHodgeDistanceMoment_nonneg
  have hl1 : complexVectorL1 omegaComplex ≤ 3 * ‖omega‖ := by
    rw [homegaComplex]
    exact complexVectorL1_complexOfRealSpace_le_three_norm omega
  have hmass :
      openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
        (9 * complexVectorL1 omegaComplex * lipschitz) * moment := by
    simpa [omegaComplex, lipschitz, moment, totalDyadicHodgeDistanceMoment] using
      openPeriodicFullSpatialCrossCoherenceMass_le_distanceMoments solution t q
  have hinverse :
      ‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
          complexVectorL1 omegaComplex ^ 4 ≤
        81 * ‖omega‖ ^ 2 := by
    rw [homegaComplex]
    exact norm_inverse_complexDot_mul_complexVectorL1_pow_four_le omega
  have hbaseTerm :
      base * complexVectorL1 omegaComplex ^ 2 ≤
        (9 * base) * ‖omega‖ ^ 2 := by
    calc
      base * complexVectorL1 omegaComplex ^ 2 ≤
          base * (3 * ‖omega‖) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (complexVectorL1_nonneg _) hl1 2)
          hbaseNonneg
      _ = (9 * base) * ‖omega‖ ^ 2 := by ring
  have hcrossTerm :
      (‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
          complexVectorL1 omegaComplex *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 omegaComplex ^ 2 ≤
        (729 * lipschitz * moment) * ‖omega‖ ^ 2 := by
    calc
      (‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
          complexVectorL1 omegaComplex *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 omegaComplex ^ 2 ≤
        (‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
          complexVectorL1 omegaComplex *
            ((9 * complexVectorL1 omegaComplex * lipschitz) * moment)) *
          complexVectorL1 omegaComplex ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmass
            (mul_nonneg (norm_nonneg _) (complexVectorL1_nonneg _)))
          (sq_nonneg _)
      _ = (9 * lipschitz * moment) *
          (‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
            complexVectorL1 omegaComplex ^ 4) := by ring
      _ ≤ (9 * lipschitz * moment) * (81 * ‖omega‖ ^ 2) := by
        gcongr
      _ = (729 * lipschitz * moment) * ‖omega‖ ^ 2 := by ring
  have hphysical :=
    abs_openPeriodicPhysicalVortexStretchingAt_le_constructedSpatialCoherence
      solution t q
  change
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      openPeriodicVorticityDirectionEnstrophyCoefficient solution t * ‖omega‖ ^ 2
  calc
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
        base * complexVectorL1 omegaComplex ^ 2 +
          (‖(complexDot omegaComplex omegaComplex)⁻¹‖ *
            complexVectorL1 omegaComplex *
              openPeriodicFullSpatialCrossCoherenceMass solution t q) *
            complexVectorL1 omegaComplex ^ 2 := by
      simpa [base, omegaComplex, mul_assoc] using hphysical
    _ ≤ (9 * base) * ‖omega‖ ^ 2 +
        (729 * lipschitz * moment) * ‖omega‖ ^ 2 :=
      add_le_add hbaseTerm hcrossTerm
    _ = openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        ‖omega‖ ^ 2 := by
      simp only [openPeriodicVorticityDirectionEnstrophyCoefficient,
        base, lipschitz, moment]
      ring

/-! ## Composition with the actual unit-cube enstrophy receiver -/

/-- **[proved-derived; formal-checked]** The constructed source modulus and every dyadic spatial
scale now reach the signed unit-cube vortex-stretching receiver used by the enstrophy identity.
The only coefficient left is independent of the spatial receiver occurrence. -/
theorem openPeriodicVortexStretching_le_enstrophyCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    periodicVortexStretching velocity t.1 ≤
      2 * openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        periodicEnstrophy velocity t.1 := by
  let S : ℝ := (t.1 + T) / 2
  have hSpos : 0 < S := by
    have hTpos : 0 < T := t.2.1.trans t.2.2
    dsimp [S]
    exact div_pos (add_pos t.2.1 hTpos) (by norm_num)
  have hST : S < T := by
    dsimp [S]
    linarith [t.2.2]
  have htS : t.1 < S := by
    dsimp [S]
    linarith [t.2.2]
  let closedSolution : PeriodicSolutionOn S nu initial force velocity pressure :=
    solution.toClosedInterior hSpos hST
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have homega : ContDiff ℝ 2 (fun x ↦ vorticityField velocity x t.1) :=
    periodicSolutionOn_vorticityField_contDiff_two closedSolution t.2.1 htS
  have hstretchingIntegrable : IntegrableOn (fun x ↦
      inner ℝ
        (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
        (vorticityField velocity x t.1)) unitCube :=
    periodicSolutionOn_vortexStretching_integrable closedSolution t.2.1 htS
  have hrightIntegrable : IntegrableOn (fun x ↦
      openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        ‖vorticityField velocity x t.1‖ ^ 2) unitCube :=
    (continuous_const.mul (homega.continuous.norm.pow 2)).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hpoint : ∀ x ∈ unitCube,
      inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
          (vorticityField velocity x t.1) ≤
        openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
          ‖vorticityField velocity x t.1‖ ^ 2 := by
    intro x _hx
    calc
      inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
          (vorticityField velocity x t.1) ≤
        |inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
          (vorticityField velocity x t.1)| := le_abs_self _
      _ = |openPeriodicPhysicalVortexStretchingAt solution t
          (euclideanToSpatialTorus x)| := by
        rw [openPeriodicPhysicalVortexStretchingAt_projection]
      _ ≤ openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
          ‖torusVorticityEvolution solution t (euclideanToSpatialTorus x)‖ ^ 2 :=
        abs_openPeriodicPhysicalVortexStretchingAt_le_enstrophyDensity
          solution t (euclideanToSpatialTorus x)
      _ = openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
          ‖vorticityField velocity x t.1‖ ^ 2 := by
        rw [torusVorticityEvolution_projection]
  calc
    periodicVortexStretching velocity t.1 ≤
        ∫ x in unitCube,
          openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
            ‖vorticityField velocity x t.1‖ ^ 2 := by
      exact setIntegral_mono_on hstretchingIntegrable hrightIntegrable
        hcubeMeasurable hpoint
    _ = openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        ∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 2 * openPeriodicVorticityDirectionEnstrophyCoefficient solution t *
        periodicEnstrophy velocity t.1 := by
      unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul]
      ring

/-- The exact real-time chart of the returned coefficient.  It is zero outside the physical open
lifespan solely to give the terminal integral a total real-domain type. -/
def openPeriodicVorticityDirectionEnstrophyRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo 0 T then
    openPeriodicVorticityDirectionEnstrophyCoefficient solution ⟨s, hs⟩
  else 0

@[simp]
theorem openPeriodicVorticityDirectionEnstrophyRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    openPeriodicVorticityDirectionEnstrophyRate solution s =
      openPeriodicVorticityDirectionEnstrophyCoefficient solution ⟨s, hs⟩ := by
  simp [openPeriodicVorticityDirectionEnstrophyRate, hs]

theorem openPeriodicVorticityDirectionEnstrophyRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    0 ≤ openPeriodicVorticityDirectionEnstrophyRate solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [openPeriodicVorticityDirectionEnstrophyRate_eq solution hs]
    exact openPeriodicVorticityDirectionEnstrophyCoefficient_nonneg solution ⟨s, hs⟩
  · simp [openPeriodicVorticityDirectionEnstrophyRate, hs]

/-- **[proved-derived; formal-checked]** Nonnegative viscosity removes the dissipative face and
the constructed coherence coefficient replaces the former uniform-Jacobian premise in the exact
enstrophy-rate law. -/
theorem openPeriodicEnstrophyRate_le_directionCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (hnu : 0 ≤ nu) (F : ℝ)
    (hforce : periodicCurlForcingWork force velocity t.1 ≤ F) :
    periodicEnstrophyRate nu force velocity t.1 ≤
      2 * openPeriodicVorticityDirectionEnstrophyRate solution t.1 *
          periodicEnstrophy velocity t.1 + F := by
  let S : ℝ := (t.1 + T) / 2
  have hTpos : 0 < T := t.2.1.trans t.2.2
  have hSpos : 0 < S := by
    dsimp [S]
    exact div_pos (add_pos t.2.1 hTpos) (by norm_num)
  have hST : S < T := by
    dsimp [S]
    linarith [t.2.2]
  have htS : t.1 < S := by
    dsimp [S]
    linarith [t.2.2]
  let closedSolution : PeriodicSolutionOn S nu initial force velocity pressure :=
    solution.toClosedInterior hSpos hST
  have hdiss : 0 ≤ nu * periodicVorticityDissipation velocity t.1 :=
    periodicSolutionOn_viscousVorticityDissipation_nonneg
      closedSolution t.2.1 htS hnu
  have hstretch := openPeriodicVortexStretching_le_enstrophyCoefficient solution t
  rw [openPeriodicVorticityDirectionEnstrophyRate_eq solution t.2]
  unfold periodicEnstrophyRate
  linarith

section Audit

#print axioms norm_inverse_complexDot_mul_complexVectorL1_pow_four_le
#print axioms totalDyadicHodgeDistanceMoment_nonneg
#print axioms openPeriodicVorticityDirectionEnstrophyCoefficient_nonneg
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_enstrophyDensity
#print axioms openPeriodicVortexStretching_le_enstrophyCoefficient
#print axioms openPeriodicVorticityDirectionEnstrophyRate_nonneg
#print axioms openPeriodicEnstrophyRate_le_directionCoefficient

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
