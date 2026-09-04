import ElementaryHolonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
import ElementaryHolonics.Millennium.NavierStokesH2TriadShellLeverBound

/-!
# The completed physical H2 curl multiplier swing

**[proved-derived; formal-checked]**  The physical/Fourier bridge identifies the literal
derivative-weighted curl work with the two homogeneous multiplier orders
`lambda + lambda^2 = lambda * (1 + lambda)`.  In the vorticity chart, the earlier
`h2CurlEnergyMultiplier` correctly carries the inhomogeneous test factor `1 + lambda` on curl
modes.  Its exchanged transfer is therefore the correctly typed vorticity-test-factor swing,
while the velocity-chart physical work additionally retains the leading curl--curl Stokes factor.

This owner retains both caused factors.  On an exchanged divergence-free triad, the completed
multiplier difference factors exactly as

`(lambda(q) - lambda(r)) * (1 + lambda(q) + lambda(r))`.

The first factor is the already-founded pantographic lever through the advecting pin.  The second
factor is the additional physical curl scale and is never discarded in the cube or dyadic
receivers below.  Equal-radius exchanged pins remain in the exact null fibre.

These are single-triad identities and estimates before an infinite convolution or absolute
coefficient population is formed.  They do not establish a Navier--Stokes continuation theorem.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.Turn

/-! ## The two-factor physical multiplier -/

/-- The completed physical `H2` curl-energy multiplier in an intrinsic turn calibration.
The first factor is supplied by the curl--curl Hodge receiver and the second by the inhomogeneous
`H2` test. -/
def calibratedPhysicalH2CurlEnergyMultiplier {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (frequency : SpatialFrequency) : ℂ :=
  ((calibratedTorusStokesEigenvalue calibration frequency *
      (1 + calibratedTorusStokesEigenvalue calibration frequency) : ℝ) : ℂ)

/-- The completed physical `H2` curl-energy multiplier in the standing torus chart. -/
def physicalH2CurlEnergyMultiplier (frequency : SpatialFrequency) : ℂ :=
  ((torusStokesEigenvalue frequency *
      (1 + torusStokesEigenvalue frequency) : ℝ) : ℂ)

/-- The completed multiplier is exactly the two homogeneous orders returned by the physical
Parseval bridge. -/
theorem physicalH2CurlEnergyMultiplier_eq_orderOne_add_orderTwo
    (frequency : SpatialFrequency) :
    physicalH2CurlEnergyMultiplier frequency =
      ((torusStokesEigenvalue frequency +
        torusStokesEigenvalue frequency ^ 2 : ℝ) : ℂ) := by
  unfold physicalH2CurlEnergyMultiplier
  push_cast
  ring

/-- Precise classification of the predecessor: `h2CurlEnergyMultiplier` is the test factor.
The physical curl receiver supplies the distinct leading Stokes factor. -/
theorem physicalH2CurlEnergyMultiplier_eq_stokes_mul_testFactor
    (frequency : SpatialFrequency) :
    physicalH2CurlEnergyMultiplier frequency =
      (torusStokesEigenvalue frequency : ℂ) * h2CurlEnergyMultiplier frequency := by
  unfold physicalH2CurlEnergyMultiplier h2CurlEnergyMultiplier
  push_cast
  ring

/-- In the velocity chart, the homogeneous physical mode work is exactly the real receiver of
the completed two-factor multiplier.  This is the direct type-level distinction from the
vorticity-chart `1 + lambda` test. -/
theorem homogeneousCoordinateH2ModeWork_eq_completedPhysicalMultiplier
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector) :
    homogeneousCoordinateH2ModeWork frequency velocityMode sourceMode =
      -(physicalH2CurlEnergyMultiplier frequency).re *
        sourceTestProductionReading velocityMode sourceMode := by
  unfold homogeneousCoordinateH2ModeWork physicalH2CurlEnergyMultiplier
  simp
  ring

/-- The standing physical multiplier is measured entirely through the primitive lattice
character scale and the integer-frequency square. -/
theorem physicalH2CurlEnergyMultiplier_eq_primitiveScale
    (frequency : SpatialFrequency) :
    physicalH2CurlEnergyMultiplier frequency =
      ((primitiveTorusStokesScale * frequencySquared frequency *
        (1 + primitiveTorusStokesScale * frequencySquared frequency) : ℝ) : ℂ) := by
  rw [physicalH2CurlEnergyMultiplier,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]

/-- A Euclidean-circle witness identifies the calibrated completed multiplier with the standing
torus multiplier. -/
theorem calibratedPhysicalH2CurlEnergyMultiplier_eq_physicalH2CurlEnergyMultiplier
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle) (frequency : SpatialFrequency) :
    calibratedPhysicalH2CurlEnergyMultiplier calibration frequency =
      physicalH2CurlEnergyMultiplier frequency := by
  unfold calibratedPhysicalH2CurlEnergyMultiplier physicalH2CurlEnergyMultiplier
  rw [calibratedTorusStokesEigenvalue_eq_torusStokesEigenvalue
    calibration hcircle frequency]

/-! ## Completed exchanged swing -/

/-- Completed physical `H2` curl transfer before a norm or coefficient-mass receiver. -/
def calibratedPhysicalH2ExchangedTriadTransfer {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer
    (calibratedPhysicalH2CurlEnergyMultiplier calibration) triad
      advectingMode transportedMode receiverMode

/-- Completed physical `H2` curl transfer in the standing torus chart. -/
def physicalH2ExchangedTriadTransfer
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer physicalH2CurlEnergyMultiplier triad
    advectingMode transportedMode receiverMode

/-- The intrinsic completed physical swing has the exact polynomial difference factorization. -/
theorem calibratedPhysicalH2ExchangedTriadTransfer_eq_factorized
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    calibratedPhysicalH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode =
      (((calibratedTorusStokesEigenvalue calibration triad.transported -
          calibratedTorusStokesEigenvalue calibration triad.receiver) *
        (1 + calibratedTorusStokesEigenvalue calibration triad.transported +
          calibratedTorusStokesEigenvalue calibration triad.receiver) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [calibratedPhysicalH2ExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence]
  unfold calibratedPhysicalH2CurlEnergyMultiplier
  push_cast
  ring

/-- **Completed physical clocked pantographic swing.**  The literal standing-torus multiplier
`lambda + lambda^2` crosses an exchanged divergence-free triad through the exact factor
`(lambda(q)-lambda(r)) * (1+lambda(q)+lambda(r))`. -/
theorem physicalH2ExchangedTriadTransfer_eq_factorized
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      (((torusStokesEigenvalue triad.transported -
          torusStokesEigenvalue triad.receiver) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [physicalH2ExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence]
  unfold physicalH2CurlEnergyMultiplier
  push_cast
  ring

/-- The earlier exchanged transfer is exactly the test-factor swing.  The completed physical
swing retains the additional symmetric curl scale `1 + lambda(q) + lambda(r)`. -/
theorem physicalH2ExchangedTriadTransfer_eq_symmetricCurlScale_mul_testFactorSwing
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      ((1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver : ℝ) : ℂ) *
        h2ExchangedTriadTransfer triad
          advectingMode transportedMode receiverMode := by
  rw [physicalH2ExchangedTriadTransfer_eq_factorized triad
      advectingMode transportedMode receiverMode hdivergence,
    h2ExchangedTriadTransfer_eq_stokesDifference_mul triad
      advectingMode transportedMode receiverMode hdivergence]
  push_cast
  ring

/-! ## Intrinsic and primitive-scale lever presentations -/

/-- Intrinsic completed swing through the advecting-pin lever and its additional physical curl
scale. -/
theorem calibratedPhysicalH2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    calibratedPhysicalH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode =
      ((calibratedStokesScale calibration *
          (frequencyPairing triad.advecting triad.receiver -
            frequencyPairing triad.advecting triad.transported) *
          (1 + calibratedStokesScale calibration *
            (frequencySquared triad.transported +
              frequencySquared triad.receiver)) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [calibratedPhysicalH2ExchangedTriadTransfer_eq_factorized calibration triad
      advectingMode transportedMode receiverMode hdivergence,
    calibratedTorusStokesEigenvalue_transported_sub_receiver]
  unfold calibratedTorusStokesEigenvalue
  push_cast
  ring

/-- Actual completed swing through the primitive-character Stokes scale. -/
theorem physicalH2ExchangedTriadTransfer_eq_primitiveScale_advectingPairingSwing_mul
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      ((primitiveTorusStokesScale *
          (frequencyPairing triad.advecting triad.receiver -
            frequencyPairing triad.advecting triad.transported) *
          (1 + primitiveTorusStokesScale *
            (frequencySquared triad.transported +
              frequencySquared triad.receiver)) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [physicalH2ExchangedTriadTransfer_eq_factorized triad
      advectingMode transportedMode receiverMode hdivergence,
    torusStokesEigenvalue_transported_sub_receiver,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
  push_cast
  ring

/-- Equal-radius exchanged pins remain in the null fibre of the completed physical swing. -/
theorem physicalH2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [physicalH2ExchangedTriadTransfer_eq_factorized triad
      advectingMode transportedMode receiverMode hdivergence]
  have heigen :
      torusStokesEigenvalue triad.transported =
        torusStokesEigenvalue triad.receiver := by
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
      torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared, hradius]
  rw [heigen, sub_self]
  simp

/-! ## Honest scale-local bounds retaining the extra curl scale -/

/-- A coordinate-cube aperture bounds the squared frequency receiver by three coordinate
squares. -/
theorem frequencySquared_le_three_mul_cubeRadius_sq
    {radius : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) :
    frequencySquared frequency ≤ 3 * (radius : ℝ) ^ 2 := by
  have hcoordinate : ∀ coordinate : Fin 3,
      (frequency coordinate : ℝ) ^ 2 ≤ (radius : ℝ) ^ 2 := by
    intro coordinate
    have habs :=
      abs_frequency_coordinate_le_radius_of_mem_frequencyCube hfrequency coordinate
    have hsquare := (sq_le_sq₀ (abs_nonneg (frequency coordinate : ℝ))
      (Nat.cast_nonneg radius)).2 habs
    simpa only [sq_abs] using hsquare
  rw [show frequencySquared frequency =
      (frequency 0 : ℝ) ^ 2 + (frequency 1 : ℝ) ^ 2 +
        (frequency 2 : ℝ) ^ 2 by
    simp [frequencySquared, Fin.sum_univ_succ, add_assoc]]
  linarith [hcoordinate 0, hcoordinate 1, hcoordinate 2]

/-- The primitive-character Stokes eigenvalue on a frequency cube has its explicit quadratic
aperture scale. -/
theorem torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq
    {radius : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) :
    torusStokesEigenvalue frequency ≤
      primitiveTorusStokesScale * (3 * (radius : ℝ) ^ 2) := by
  rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
  exact mul_le_mul_of_nonneg_left
    (frequencySquared_le_three_mul_cubeRadius_sq hfrequency)
    primitiveTorusStokesScale_pos.le

/-- Both high exchanged pins contribute to the additional symmetric curl scale. -/
theorem symmetricCurlScale_le_primitiveScale_six_mul_cubeRadius_sq
    (triad : AddressedClosedFourierTriad) (highRadius : ℕ)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    1 + torusStokesEigenvalue triad.transported +
        torusStokesEigenvalue triad.receiver ≤
      1 + primitiveTorusStokesScale * (6 * (highRadius : ℝ) ^ 2) := by
  have htransportedBound :=
    torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq htransported
  have hreceiverBound :=
    torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq hreceiver
  nlinarith [primitiveTorusStokesScale_pos]

/-- Cube-local norm bound for the completed physical swing.  The earlier low-times-high lever is
multiplied by the additional symmetric curl scale; that factor is not hidden in a constant. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  rw [physicalH2ExchangedTriadTransfer_eq_factorized triad
      advectingMode transportedMode receiverMode hdivergence,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hscale :
      0 ≤ 1 + torusStokesEigenvalue triad.transported +
        torusStokesEigenvalue triad.receiver := by
    linarith [torusStokesEigenvalue_nonneg triad.transported,
      torusStokesEigenvalue_nonneg triad.receiver]
  rw [abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (abs_torusStokesEigenvalue_difference_le_six_mul_cubeRadii
        triad lowRadius highRadius hadvecting htransported hreceiver)
      hscale)
    (norm_nonneg _)

/-- Fully aperture-bounded cube form.  The additional `highRadius^2` factor is the leading
curl--curl Stokes occurrence; the completed physical swing therefore retains one more high-scale
quadratic factor than the vorticity-test-factor swing. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_explicit_cubeScale
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) *
        (1 + primitiveTorusStokesScale * (6 * (highRadius : ℝ) ^ 2))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  have hfirst := norm_physicalH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    triad lowRadius highRadius advectingMode transportedMode receiverMode hdivergence
      hadvecting htransported hreceiver
  have hcurl := symmetricCurlScale_le_primitiveScale_six_mul_cubeRadius_sq
    triad highRadius htransported hreceiver
  have hleverNonneg :
      0 ≤ primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) := by
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg lowRadius))
        (Nat.cast_nonneg highRadius))
  have hfaceNonneg :
      0 ≤ ‖triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode‖ := norm_nonneg _
  calc
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := hfirst
    _ ≤ (primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) *
        (1 + primitiveTorusStokesScale * (6 * (highRadius : ℝ) ^ 2))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcurl hleverNonneg) hfaceNonneg

/-- Dyadic high--high--low specialization.  The retained scale is low times high, multiplied by
the additional physical curl scale of the exchanged high pins. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_of_highHighLowDyadic
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  exact norm_physicalH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    triad (dyadicRadius (lowLevel + 1)) (dyadicRadius (highLevel + 1))
    advectingMode transportedMode receiverMode hdivergence
    ((mem_dyadicFrequencyShell_iff lowLevel triad.advecting).mp hadvecting).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.transported).mp htransported).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.receiver).mp hreceiver).1

/-- The dyadic bound exposes the genuine separated ratio but retains the additional high curl
scale.  Thus the physical multiplier is a ratio times a high fourth-order scale asymptotically,
not merely the ratio times the high square of the test-factor swing. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_ratio_mul_high_sq_mul_curlScale
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicLowHighLengthRatio lowLevel highLevel *
          (dyadicRadius (highLevel + 1) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  calc
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ :=
      norm_physicalH2ExchangedTriadTransfer_le_of_highHighLowDyadic triad
        lowLevel highLevel advectingMode transportedMode receiverMode hdivergence
        hseparated hadvecting htransported hreceiver
    _ = (primitiveTorusStokesScale *
        (6 * dyadicLowHighLengthRatio lowLevel highLevel *
          (dyadicRadius (highLevel + 1) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
      rw [show 6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ) =
        6 * ((dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) by ring,
        dyadic_low_mul_high_eq_ratio_mul_high_sq]
      ring

section Audit

#print axioms physicalH2CurlEnergyMultiplier_eq_orderOne_add_orderTwo
#print axioms physicalH2CurlEnergyMultiplier_eq_stokes_mul_testFactor
#print axioms homogeneousCoordinateH2ModeWork_eq_completedPhysicalMultiplier
#print axioms physicalH2CurlEnergyMultiplier_eq_primitiveScale
#print axioms calibratedPhysicalH2CurlEnergyMultiplier_eq_physicalH2CurlEnergyMultiplier
#print axioms calibratedPhysicalH2ExchangedTriadTransfer_eq_factorized
#print axioms physicalH2ExchangedTriadTransfer_eq_factorized
#print axioms physicalH2ExchangedTriadTransfer_eq_symmetricCurlScale_mul_testFactorSwing
#print axioms calibratedPhysicalH2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
#print axioms physicalH2ExchangedTriadTransfer_eq_primitiveScale_advectingPairingSwing_mul
#print axioms physicalH2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
#print axioms frequencySquared_le_three_mul_cubeRadius_sq
#print axioms torusStokesEigenvalue_le_primitiveScale_three_mul_cubeRadius_sq
#print axioms symmetricCurlScale_le_primitiveScale_six_mul_cubeRadius_sq
#print axioms norm_physicalH2ExchangedTriadTransfer_le_six_mul_cubeRadii
#print axioms norm_physicalH2ExchangedTriadTransfer_le_explicit_cubeScale
#print axioms norm_physicalH2ExchangedTriadTransfer_le_of_highHighLowDyadic
#print axioms norm_physicalH2ExchangedTriadTransfer_le_ratio_mul_high_sq_mul_curlScale

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
