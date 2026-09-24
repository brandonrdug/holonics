import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ComparableQuantitativeBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2RotatedMajorantCofinalBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion

/-!
# Complete physical H2 current under the cofinal spatial majorant

**[proved-derived; formal-checked]** The four exact dyadic sectors of every finite common
three-pin cube are paid by radius-independent receivers: the primary unique-low service, the two
separately oriented rotated services, and the complete comparable-sector kernel.  Cofinal cube
exhaustion then returns an unconditional bound on the literal coordinate `H2` nonlinear
production current.

This is the complete conclusion of the current pointwise absolute-value route.  Its unique-low
services contain a cubic native-`H3` face, while the comparable kernel is retained in its complete
summable form.  Consequently this owner asserts no time integrability, viscous absorption,
continuation, or terminal Navier--Stokes control.
-/

noncomputable section

open Filter Set Topology

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalAbsoluteMajorant

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH2LowVelocityGradeKernel
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableResidueBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ComparableQuantitativeBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2PrimaryMajorantCofinalBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2RotatedMajorantCofinalBound
open Soma.Holonics.Millennium.NavierStokesPhysicalH2UniqueLowRotationPopulation
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.Turn

/-- Radius-independent payment for the primary unique-low orientation. -/
def physicalH2PrimaryCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  (18 * primitiveTorusStokesScale * calibration.fullTurn) *
    ((physicalH2PrimaryLowGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
      (calibratedHighVelocityGradeService *
        ‖openVelocityWeightedH3State solution t‖ ^ 2))

/-- Common radius-independent payment for either rotated unique-low orientation. -/
def physicalH2RotatedCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  (calibration.fullTurn * 3) *
    ((rotatedLowVelocityGradeFactor solution t 0 +
        calibratedLowVelocityGradeService *
          (3 * ‖openVelocityWeightedH3State solution t‖)) *
      (18 * rotatedHighBandH3Calibration *
        ‖openVelocityWeightedH3State solution t‖ ^ 2))

/-- The full absolute cofinal receiver: primary, two oriented rotated populations, and the
complete comparable-sector kernel. -/
def physicalH2AbsoluteCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  physicalH2PrimaryCofinalMajorant calibration solution t +
    physicalH2RotatedCofinalMajorant calibration solution t +
    physicalH2RotatedCofinalMajorant calibration solution t +
    physicalH2ComparableCompleteKernel solution t

/-- Every common three-pin cube is paid by the same complete spatial majorant. -/
theorem norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_cofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ ≤
      physicalH2AbsoluteCofinalMajorant calibration solution t := by
  have hpartition :=
    norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
      calibration hcircle solution t radius
  have hprimary :=
    finiteAdvectingLowPrimaryGradeRatioPopulation_le_cofinalUniform
      calibration hcircle solution t radius
  have hsecond :=
    finiteOpenAdvectingLowSecondGradeRatioPopulation_le_cofinalUniform
      calibration solution t radius
  have hthird :=
    finiteOpenAdvectingLowThirdGradeRatioPopulation_le_cofinalUniform
      calibration solution t radius
  have hcomparable :=
    norm_finiteOpenPhysicalH2ComparableCurrent_le_completeKernel
      solution t radius
  unfold physicalH2AbsoluteCofinalMajorant
    physicalH2PrimaryCofinalMajorant physicalH2RotatedCofinalMajorant
  linarith

/-- The cofinal finite-cube bound passes to the literal complete physical velocity current.  The
factor `1/2` is the exact exchanged-current receiver orientation, not a relaxed constant. -/
theorem abs_completePhysicalH2VelocityCurrent_le_half_cofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    |completePhysicalH2VelocityCurrent solution t| ≤
      (1 / 2 : ℝ) * physicalH2AbsoluteCofinalMajorant calibration solution t := by
  have hlimit :=
    tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t
  have habs : Tendsto
      (fun radius : ℕ ↦
        |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re|)
      atTop (nhds |completePhysicalH2VelocityCurrent solution t|) :=
    continuous_abs.tendsto _ |>.comp hlimit
  apply le_of_tendsto habs
  exact Filter.Eventually.of_forall fun radius ↦ by
    calc
      |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re| =
          (1 / 2 : ℝ) *
            |(finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re| := by
        rw [abs_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) *
          ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ :=
        mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm
            (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius))
          (by norm_num)
      _ ≤ (1 / 2 : ℝ) * physicalH2AbsoluteCofinalMajorant calibration solution t :=
        mul_le_mul_of_nonneg_left
          (norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_cofinalMajorant
            calibration hcircle solution t radius)
          (by norm_num)

/-- The same actual cofinal majorant lands directly in the coordinate nonlinear production
receiver used by the exact `H2`--`H3` balance. -/
theorem abs_coordinateH2NonlinearProductionCurrent_le_half_cofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    |coordinateH2NonlinearProductionCurrent velocity t.1| ≤
      (1 / 2 : ℝ) * physicalH2AbsoluteCofinalMajorant calibration solution t := by
  rw [← completePhysicalH2VelocityCurrent_eq_coordinateH2NonlinearProductionCurrent
    solution t]
  exact abs_completePhysicalH2VelocityCurrent_le_half_cofinalMajorant
    calibration hcircle solution t

/-! ## Fully quantitative cubic endpoint -/

/-- The comparable-sector complete service after every maximum grade is paid in the native
velocity `H3` chart. -/
def physicalH2ComparableVelocityH3CofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  (calibratedComparableVelocityBoundaryService calibration +
      ∑' level : ℕ, calibratedComparableVelocityGradeKernel calibration level) *
    ‖openVelocityWeightedH3State solution t‖ ^ 3

/-- The fully quantitative radius-independent spatial endpoint.  Every sector is now expressed
in the native velocity chart; its highest-order dependence remains cubic. -/
def physicalH2QuantitativeAbsoluteCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  physicalH2PrimaryCofinalMajorant calibration solution t +
    physicalH2RotatedCofinalMajorant calibration solution t +
    physicalH2RotatedCofinalMajorant calibration solution t +
    physicalH2ComparableVelocityH3CofinalMajorant calibration solution t

/-- Every common cube is controlled by the completely quantitative native-velocity endpoint. -/
theorem norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_quantitativeCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ ≤
      physicalH2QuantitativeAbsoluteCofinalMajorant calibration solution t := by
  have hpartition :=
    norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_threeGradeRatioPopulations_add_comparable
      calibration hcircle solution t radius
  have hprimary :=
    finiteAdvectingLowPrimaryGradeRatioPopulation_le_cofinalUniform
      calibration hcircle solution t radius
  have hsecond :=
    finiteOpenAdvectingLowSecondGradeRatioPopulation_le_cofinalUniform
      calibration solution t radius
  have hthird :=
    finiteOpenAdvectingLowThirdGradeRatioPopulation_le_cofinalUniform
      calibration solution t radius
  have hcomparable :=
    norm_finiteOpenPhysicalH2ComparableCurrent_le_completeVelocityH3Service
      calibration hcircle solution t radius
  unfold physicalH2QuantitativeAbsoluteCofinalMajorant
    physicalH2ComparableVelocityH3CofinalMajorant
    physicalH2PrimaryCofinalMajorant physicalH2RotatedCofinalMajorant
  linarith

/-- Cofinal exhaustion returns the fully quantitative native-velocity bound on the complete
physical current. -/
theorem abs_completePhysicalH2VelocityCurrent_le_half_quantitativeCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    |completePhysicalH2VelocityCurrent solution t| ≤
      (1 / 2 : ℝ) *
        physicalH2QuantitativeAbsoluteCofinalMajorant calibration solution t := by
  have hlimit :=
    tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t
  have habs : Tendsto
      (fun radius : ℕ ↦
        |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re|)
      atTop (nhds |completePhysicalH2VelocityCurrent solution t|) :=
    continuous_abs.tendsto _ |>.comp hlimit
  apply le_of_tendsto habs
  exact Filter.Eventually.of_forall fun radius ↦ by
    calc
      |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re| =
          (1 / 2 : ℝ) *
            |(finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re| := by
        rw [abs_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) *
          ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ :=
        mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm
            (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius))
          (by norm_num)
      _ ≤ (1 / 2 : ℝ) *
          physicalH2QuantitativeAbsoluteCofinalMajorant calibration solution t :=
        mul_le_mul_of_nonneg_left
          (norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_quantitativeCofinalMajorant
            calibration hcircle solution t radius)
          (by norm_num)

/-- The quantitative cofinal endpoint is an actual pointwise estimate for the coordinate
nonlinear production receiver.  It remains a static cubic estimate. -/
theorem abs_coordinateH2NonlinearProductionCurrent_le_half_quantitativeCofinalMajorant
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    |coordinateH2NonlinearProductionCurrent velocity t.1| ≤
      (1 / 2 : ℝ) *
        physicalH2QuantitativeAbsoluteCofinalMajorant calibration solution t := by
  rw [← completePhysicalH2VelocityCurrent_eq_coordinateH2NonlinearProductionCurrent
    solution t]
  exact abs_completePhysicalH2VelocityCurrent_le_half_quantitativeCofinalMajorant
    calibration hcircle solution t

section Audit

#print axioms norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_cofinalMajorant
#print axioms abs_completePhysicalH2VelocityCurrent_le_half_cofinalMajorant
#print axioms abs_coordinateH2NonlinearProductionCurrent_le_half_cofinalMajorant
#print axioms norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_quantitativeCofinalMajorant
#print axioms abs_completePhysicalH2VelocityCurrent_le_half_quantitativeCofinalMajorant
#print axioms abs_coordinateH2NonlinearProductionCurrent_le_half_quantitativeCofinalMajorant

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalAbsoluteMajorant
