import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A canonical vorticity derivative modulus

**[proved-derived]** The source distance law initially selected an arbitrary Lipschitz witness on
each strict-interior slice.  This owner replaces that choice by the norm of the actual spatial
vorticity derivative over the fixed compact radius-three chart.  The derivative population is the
source occurrence; the continuous-map norm is its canonical spatial receiver.

This removes witness-selection ambiguity.  Continuity or integrability as the time coordinate
approaches the open terminal face remains a separate theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-- The actual spatial derivative of vorticity, retained over the complete compact chart used by
the torus-distance lift. -/
def openPeriodicVorticityDerivativeChart
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    C(Metric.closedBall (0 : Space) 3, Space →L[ℝ] Space) :=
  ⟨fun x ↦ fderiv ℝ (fun y ↦ vorticityField velocity y t.1) x.1,
    ((vorticityField_contDiff_one velocity t.1
      ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous_fderiv one_ne_zero).comp
      continuous_subtype_val⟩

/-- The canonical nonnegative coefficient is exactly the compact-chart norm of the derivative
population. -/
def openPeriodicCanonicalVorticityLipschitzConstant
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ≥0 :=
  ‖openPeriodicVorticityDerivativeChart solution t‖₊

/-- Every addressed derivative occurrence is bounded by the canonical compact-chart receiver. -/
theorem nnnorm_fderiv_vorticity_le_canonical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) {x : Space} (hx : x ∈ Metric.closedBall (0 : Space) 3) :
    ‖fderiv ℝ (fun y ↦ vorticityField velocity y t.1) x‖₊ ≤
      openPeriodicCanonicalVorticityLipschitzConstant solution t := by
  change
    ‖(openPeriodicVorticityDerivativeChart solution t) ⟨x, hx⟩‖ ≤
      ‖openPeriodicVorticityDerivativeChart solution t‖
  exact (openPeriodicVorticityDerivativeChart solution t).norm_coe_le_norm ⟨x, hx⟩

/-- The mean-value theorem transports the derivative receiver into the exact Lipschitz carrier on
the convex radius-three chart. -/
theorem openPeriodicCanonicalVorticityLipschitzOn_closedBall
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    LipschitzOnWith (openPeriodicCanonicalVorticityLipschitzConstant solution t)
      (fun x ↦ vorticityField velocity x t.1) (Metric.closedBall 0 3) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x _hx
    exact (vorticityField_contDiff_one velocity t.1
      ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le
        (WithTop.coe_le_coe.mpr le_top))).differentiable (by norm_num) x
  · intro x hx
    exact nnnorm_fderiv_vorticity_le_canonical solution t hx
  · exact convex_closedBall 0 3

/-! ## Canonical source and scale carriers -/

/-- The physical cross difference obeys the same exact torus-distance law with the canonical
derivative norm in place of the former choice-selected witness. -/
theorem openPeriodic_receiverCrossDifference_le_canonicalDistance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q y : SpatialTorus) :
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)) *
        dist y 0 := by
  exact openPeriodic_receiverCrossDifference_le_distance_of_lipschitzOn
    solution t (openPeriodicCanonicalVorticityLipschitzConstant solution t)
      (openPeriodicCanonicalVorticityLipschitzOn_closedBall solution t) q y

/-- The canonical physical source law packaged in the distance-modulus interface. -/
def openPeriodicCanonicalVorticityDistanceCrossModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    OpenPeriodicSpatialCrossModulus solution t q :=
  openPeriodicTorusDistancePowerCrossModulus solution t q
    (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
      (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)) 1
    (mul_nonneg
      (mul_nonneg (by norm_num) (complexVectorL1_nonneg _))
      (NNReal.coe_nonneg _))
    (by
      intro y
      simpa only [pow_one] using
        openPeriodic_receiverCrossDifference_le_canonicalDistance solution t q y)

/-- The infinite-depth spatial carrier no longer depends on any selected Lipschitz witness. -/
theorem openPeriodicCanonicalDyadicSpatialCrossCoherenceSummable_inhabited
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q := by
  exact openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
    solution t q (openPeriodicCanonicalVorticityDistanceCrossModulus solution t q)
      summableDyadicHodgeJacobianKernelDistanceMoments_inhabited

/-- The complete cross-coherence mass is reconstructed through the canonical derivative norm. -/
theorem openPeriodicFullSpatialCrossCoherenceMass_le_canonicalDistanceMoments
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
      (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)) *
        ∑' scale : ℕ,
          dyadicHodgeJacobianKernelModulusMoment
            (torusDistancePowerModulus 1) scale := by
  exact openPeriodicFullSpatialCrossCoherenceMass_le_modulusMoments
    solution t q (openPeriodicCanonicalVorticityDistanceCrossModulus solution t q)
      summableDyadicHodgeJacobianKernelDistanceMoments_inhabited

/-! ## Canonical enstrophy-density return -/

/-- The spatially composed coefficient with no choice-selected Lipschitz witness. -/
def openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  (13122 * Real.pi) *
      Real.sqrt (2 * periodicKineticEnergy velocity t.1) +
    729 * (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
      totalDyadicHodgeDistanceMoment

theorem openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t := by
  unfold openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      (Real.sqrt_nonneg _))
    (mul_nonneg
      (mul_nonneg (by norm_num) (NNReal.coe_nonneg _))
      totalDyadicHodgeDistanceMoment_nonneg)

/-- **[proved-derived; formal-checked]** The canonical derivative chart controls the literal
physical stretching occurrence through vorticity square, with every spatial scale composed. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalEnstrophyDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        ‖torusVorticityEvolution solution t q‖ ^ 2 := by
  let omega : Space := torusVorticityEvolution solution t q
  let omegaComplex : ComplexVector := openPeriodicComplexVorticityAt solution t q
  let lipschitz : ℝ := openPeriodicCanonicalVorticityLipschitzConstant solution t
  let moment : ℝ := totalDyadicHodgeDistanceMoment
  let base : ℝ :=
    (1458 * Real.pi) * Real.sqrt (2 * periodicKineticEnergy velocity t.1)
  have homegaComplex : omegaComplex = complexOfRealSpace omega := by
    exact openPeriodicComplexVorticityAt_eq_torusComplexification solution t q
  have hbaseNonneg : 0 ≤ base := by
    dsimp [base]
    positivity
  have hlipschitzNonneg : 0 ≤ lipschitz := NNReal.coe_nonneg _
  have hmomentNonneg : 0 ≤ moment := totalDyadicHodgeDistanceMoment_nonneg
  have hl1 : complexVectorL1 omegaComplex ≤ 3 * ‖omega‖ := by
    rw [homegaComplex]
    exact complexVectorL1_complexOfRealSpace_le_three_norm omega
  have hmass :
      openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
        (9 * complexVectorL1 omegaComplex * lipschitz) * moment := by
    simpa [omegaComplex, lipschitz, moment, totalDyadicHodgeDistanceMoment] using
      openPeriodicFullSpatialCrossCoherenceMass_le_canonicalDistanceMoments solution t q
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
    abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence_kineticEnergy
      solution t q
        (openPeriodicCanonicalDyadicSpatialCrossCoherenceSummable_inhabited solution t q)
  change
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        ‖omega‖ ^ 2
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
    _ = openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        ‖omega‖ ^ 2 := by
      simp only [openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient,
        base, lipschitz, moment]
      ring

/-- The canonical pointwise law integrated over the actual periodic unit cube. -/
theorem openPeriodicVortexStretching_le_canonicalEnstrophyCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    periodicVortexStretching velocity t.1 ≤
      2 * openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        periodicEnstrophy velocity t.1 := by
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
      openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        ‖vorticityField velocity x t.1‖ ^ 2) unitCube :=
    (continuous_const.mul (homega.continuous.norm.pow 2)).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hpoint : ∀ x ∈ unitCube,
      inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t.1) x (vorticityField velocity x t.1))
          (vorticityField velocity x t.1) ≤
        openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
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
      _ ≤ openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
          ‖torusVorticityEvolution solution t (euclideanToSpatialTorus x)‖ ^ 2 :=
        abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalEnstrophyDensity
          solution t (euclideanToSpatialTorus x)
      _ = openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
          ‖vorticityField velocity x t.1‖ ^ 2 := by
        rw [torusVorticityEvolution_projection]
  calc
    periodicVortexStretching velocity t.1 ≤
        ∫ x in unitCube,
          openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
            ‖vorticityField velocity x t.1‖ ^ 2 := by
      exact setIntegral_mono_on hstretchingIntegrable hrightIntegrable
        hcubeMeasurable hpoint
    _ = openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        ∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 2 * openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution t *
        periodicEnstrophy velocity t.1 := by
      unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul]
      ring

/-- Totalized real-time presentation of the canonical coefficient. -/
def openPeriodicCanonicalVorticityDirectionEnstrophyRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo 0 T then
    openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution ⟨s, hs⟩
  else 0

@[simp]
theorem openPeriodicCanonicalVorticityDirectionEnstrophyRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    openPeriodicCanonicalVorticityDirectionEnstrophyRate solution s =
      openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution ⟨s, hs⟩ := by
  simp [openPeriodicCanonicalVorticityDirectionEnstrophyRate, hs]

theorem openPeriodicCanonicalVorticityDirectionEnstrophyRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    0 ≤ openPeriodicCanonicalVorticityDirectionEnstrophyRate solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [openPeriodicCanonicalVorticityDirectionEnstrophyRate_eq solution hs]
    exact openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_nonneg solution ⟨s, hs⟩
  · simp [openPeriodicCanonicalVorticityDirectionEnstrophyRate, hs]

/-- Nonnegative viscosity turns the canonical spatial return into the exact enstrophy-rate law. -/
theorem openPeriodicEnstrophyRate_le_canonicalDirectionCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (hnu : 0 ≤ nu) (F : ℝ)
    (hforce : periodicCurlForcingWork force velocity t.1 ≤ F) :
    periodicEnstrophyRate nu force velocity t.1 ≤
      2 * openPeriodicCanonicalVorticityDirectionEnstrophyRate solution t.1 *
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
  have hstretch := openPeriodicVortexStretching_le_canonicalEnstrophyCoefficient solution t
  rw [openPeriodicCanonicalVorticityDirectionEnstrophyRate_eq solution t.2]
  unfold periodicEnstrophyRate
  linarith

section Audit

#print axioms nnnorm_fderiv_vorticity_le_canonical
#print axioms openPeriodicCanonicalVorticityLipschitzOn_closedBall
#print axioms openPeriodic_receiverCrossDifference_le_canonicalDistance
#print axioms openPeriodicCanonicalDyadicSpatialCrossCoherenceSummable_inhabited
#print axioms openPeriodicFullSpatialCrossCoherenceMass_le_canonicalDistanceMoments
#print axioms openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_nonneg
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalEnstrophyDensity
#print axioms openPeriodicVortexStretching_le_canonicalEnstrophyCoefficient
#print axioms openPeriodicCanonicalVorticityDirectionEnstrophyRate_nonneg
#print axioms openPeriodicEnstrophyRate_le_canonicalDirectionCoefficient

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
