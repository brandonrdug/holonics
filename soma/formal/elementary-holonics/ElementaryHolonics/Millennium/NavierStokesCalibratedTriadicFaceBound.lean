import ElementaryHolonics.Millennium.NavierStokesH2TriadShellLeverBound

/-!
# Intrinsic full-turn calibration of one Fourier triadic face

**[proved-derived; formal-checked]**  The standing Fourier advection coefficient is decoded from
an addressed arc/radial turn carrier before any numerical circle coordinate is selected.  The
calibrated interaction carries `fullTurn * I` as its derivative current.  Nonnegativity of that
current follows from the nonnegative integrated arc population and the positive radial scale.

The pointwise trilinear estimate retains the transported frequency and the three ordered mode
occurrences.  A Euclidean-circle witness separately identifies the calibrated face with the
standing torus Fourier face.  There is no shell population, time integration, terminal estimate,
or continuation claim in this owner.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound

open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## The intrinsic derivative-current carrier -/

/-- The full-turn receiver is nonnegative because its numerator is the integrated nonnegative
arc population and its denominator is the positive radial scale. -/
theorem fullTurn_nonneg_from_arcRadial
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) :
    0 ≤ calibration.fullTurn := by
  rw [TurnCalibration.fullTurn]
  exact div_nonneg calibration.partition.integratedLength_nonneg
    calibration.radialScale_pos.le

/-- One advective Fourier interaction before selecting a numerical circle chart.  The first
frequency remains in the address even though the derivative current acts on the transported
frequency. -/
def calibratedComplexAdvectiveInteraction
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (_advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode : ComplexVector) : ComplexVector :=
  (((calibration.fullTurn : ℂ) * Complex.I) *
      complexDot (complexFrequencyVector transportedFrequency) advectingMode) •
    transportedMode

/-- The ordered bilinear dot receiver of the calibrated advective current with its receiving
mode. -/
def calibratedTriadicEnergyFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  complexDot
    (calibratedComplexAdvectiveInteraction calibration advectingFrequency
      transportedFrequency advectingMode transportedMode)
    receiverMode

/-! ## Euclidean-circle decoding -/

/-- A Euclidean-circle witness decodes the intrinsic derivative current to the standing Fourier
interaction.  The transcendental coordinate enters only through that explicit witness. -/
theorem calibratedComplexAdvectiveInteraction_eq_complexAdvectiveInteraction
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode : ComplexVector) :
    calibratedComplexAdvectiveInteraction calibration advectingFrequency
        transportedFrequency advectingMode transportedMode =
      complexAdvectiveInteraction advectingFrequency transportedFrequency
        advectingMode transportedMode := by
  unfold calibratedComplexAdvectiveInteraction complexAdvectiveInteraction
  rw [calibration.fullTurn_eq_two_pi_of_isEuclideanCircle hcircle]
  norm_num

/-- The same Euclidean witness decodes the complete calibrated triadic receiver face. -/
theorem calibratedTriadicEnergyFace_eq_triadicEnergyFace
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    calibratedTriadicEnergyFace calibration advectingFrequency transportedFrequency
        advectingMode transportedMode receiverMode =
      triadicEnergyFace advectingFrequency transportedFrequency
        advectingMode transportedMode receiverMode := by
  unfold calibratedTriadicEnergyFace triadicEnergyFace
  rw [calibratedComplexAdvectiveInteraction_eq_complexAdvectiveInteraction
    calibration hcircle]

/-! ## Ordered pointwise L1 transport -/

/-- The calibrated advective current is bounded by its intrinsic full-turn length, transported
frequency length, and the two ordered mode lengths. -/
theorem complexVectorL1_calibratedComplexAdvectiveInteraction_le
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode : ComplexVector) :
    complexVectorL1
        (calibratedComplexAdvectiveInteraction calibration advectingFrequency
          transportedFrequency advectingMode transportedMode) ≤
      calibration.fullTurn * frequencyL1 transportedFrequency *
        complexVectorL1 advectingMode * complexVectorL1 transportedMode := by
  have hturn : 0 ≤ calibration.fullTurn :=
    fullTurn_nonneg_from_arcRadial calibration
  have hdot := norm_complexDot_le_l1_mul_l1
    (complexFrequencyVector transportedFrequency) advectingMode
  rw [complexVectorL1_complexFrequencyVector] at hdot
  unfold calibratedComplexAdvectiveInteraction
  rw [complexVectorL1_smul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hturn, Complex.norm_I]
  calc
    calibration.fullTurn * 1 *
          ‖complexDot (complexFrequencyVector transportedFrequency) advectingMode‖ *
        complexVectorL1 transportedMode ≤
      calibration.fullTurn * 1 *
          (frequencyL1 transportedFrequency * complexVectorL1 advectingMode) *
        complexVectorL1 transportedMode := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdot
          (mul_nonneg hturn (by norm_num)))
        (complexVectorL1_nonneg transportedMode)
    _ = calibration.fullTurn * frequencyL1 transportedFrequency *
        complexVectorL1 advectingMode * complexVectorL1 transportedMode := by ring

/-- **Intrinsic pointwise trilinear L1 estimate.**  The theorem retains, in order, the full-turn
carrier, transported derivative frequency, advecting mode, transported mode, and receiving mode.
-/
theorem norm_calibratedTriadicEnergyFace_le
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    ‖calibratedTriadicEnergyFace calibration advectingFrequency transportedFrequency
        advectingMode transportedMode receiverMode‖ ≤
      calibration.fullTurn * frequencyL1 transportedFrequency *
        complexVectorL1 advectingMode * complexVectorL1 transportedMode *
          complexVectorL1 receiverMode := by
  unfold calibratedTriadicEnergyFace
  calc
    ‖complexDot
        (calibratedComplexAdvectiveInteraction calibration advectingFrequency
          transportedFrequency advectingMode transportedMode)
        receiverMode‖ ≤
      complexVectorL1
          (calibratedComplexAdvectiveInteraction calibration advectingFrequency
            transportedFrequency advectingMode transportedMode) *
        complexVectorL1 receiverMode :=
      norm_complexDot_le_l1_mul_l1 _ _
    _ ≤
      (calibration.fullTurn * frequencyL1 transportedFrequency *
          complexVectorL1 advectingMode * complexVectorL1 transportedMode) *
        complexVectorL1 receiverMode :=
      mul_le_mul_of_nonneg_right
        (complexVectorL1_calibratedComplexAdvectiveInteraction_le calibration
          advectingFrequency transportedFrequency advectingMode transportedMode)
        (complexVectorL1_nonneg receiverMode)
    _ = calibration.fullTurn * frequencyL1 transportedFrequency *
        complexVectorL1 advectingMode * complexVectorL1 transportedMode *
          complexVectorL1 receiverMode := by ring

/-- The standing Fourier face inherits the intrinsic pointwise bound only through an explicit
Euclidean-circle decoding witness. -/
theorem norm_triadicEnergyFace_le_of_calibration
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle)
    (advectingFrequency transportedFrequency : SpatialFrequency)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    ‖triadicEnergyFace advectingFrequency transportedFrequency
        advectingMode transportedMode receiverMode‖ ≤
      calibration.fullTurn * frequencyL1 transportedFrequency *
        complexVectorL1 advectingMode * complexVectorL1 transportedMode *
          complexVectorL1 receiverMode := by
  rw [← calibratedTriadicEnergyFace_eq_triadicEnergyFace calibration hcircle]
  exact norm_calibratedTriadicEnergyFace_le calibration advectingFrequency
    transportedFrequency advectingMode transportedMode receiverMode

#print axioms fullTurn_nonneg_from_arcRadial
#print axioms calibratedComplexAdvectiveInteraction_eq_complexAdvectiveInteraction
#print axioms calibratedTriadicEnergyFace_eq_triadicEnergyFace
#print axioms complexVectorL1_calibratedComplexAdvectiveInteraction_le
#print axioms norm_calibratedTriadicEnergyFace_le
#print axioms norm_triadicEnergyFace_le_of_calibration

end Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
