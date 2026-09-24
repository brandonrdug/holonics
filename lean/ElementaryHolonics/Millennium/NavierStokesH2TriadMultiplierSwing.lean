import ElementaryHolonics.Millennium.NavierStokesFiniteFourierHeat
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
import ElementaryHolonics.Millennium.Turn

/-!
# The H2 Fourier multiplier as an exchanged-triad swing

**[proved-derived; formal-checked]**  The inhomogeneous H2 curl-energy test carries the multiplier
`1 + lambda(k)`.  On an exchanged divergence-free Fourier triad the common storage occurrence `1`
cannot contribute: skew cancellation leaves only the difference of the two Stokes eigenvalue
coordinates.  This is the exact local pantographic swing of the H2 multiplier.

The Stokes scale is first constructed from an addressed full-turn calibration.  A Euclidean-circle
witness later identifies that intrinsic scale with the standing unit-torus eigenvalue; no
transcendental coordinate is postulated in the new multiplier definition.  The quadratic
frequency difference additionally factors through the advecting pin and the difference between
the transported and receiver pins.  Thus a same-radius exchanged pair carries zero H2 transfer,
while every surviving transfer retains the precise commutator lever arm.

This finite triad identity preserves cancellation before absolute mass.  It does not sum the
infinite convolution or bound the terminal production current.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.Turn

/-! ## Intrinsic turn-calibrated Stokes coordinates -/

/-- The squared full-turn line is the dimensional scale converting an integer character length
into the unit-torus Stokes eigenvalue chart. -/
def calibratedStokesScale {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) : ℝ :=
  calibration.fullTurn ^ 2

/-- Stokes eigenvalue before a particular numerical circle chart is chosen. -/
def calibratedTorusStokesEigenvalue {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (frequency : SpatialFrequency) : ℝ :=
  calibratedStokesScale calibration * frequencySquared frequency

/-- The inhomogeneous H2 curl-energy multiplier in the intrinsic turn chart. -/
def calibratedH2CurlEnergyMultiplier {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (frequency : SpatialFrequency) : ℂ :=
  ((1 + calibratedTorusStokesEigenvalue calibration frequency : ℝ) : ℂ)

/-- A Euclidean-circle calibration recovers the standing unit-torus Stokes chart.  The circle
coordinate enters only through the declared calibration theorem. -/
theorem calibratedTorusStokesEigenvalue_eq_torusStokesEigenvalue
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (hcircle : calibration.IsEuclideanCircle) (frequency : SpatialFrequency) :
    calibratedTorusStokesEigenvalue calibration frequency =
      torusStokesEigenvalue frequency := by
  rw [calibratedTorusStokesEigenvalue, calibratedStokesScale,
    calibration.fullTurn_eq_two_pi_of_isEuclideanCircle hcircle]
  rfl

/-! ## The standing torus scale recovered from a primitive character -/

/-- The first primitive lattice character.  Its identity is incidence data, not a numerical
transcendental calibration. -/
def firstPrimitiveSpatialFrequency : SpatialFrequency := fun coordinate ↦
  if coordinate = 0 then 1 else 0

@[simp]
theorem frequencySquared_firstPrimitiveSpatialFrequency :
    frequencySquared firstPrimitiveSpatialFrequency = 1 := by
  simp [firstPrimitiveSpatialFrequency, frequencySquared]

theorem firstPrimitiveSpatialFrequency_ne_zero :
    firstPrimitiveSpatialFrequency ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (0 : Fin 3)
  simp [firstPrimitiveSpatialFrequency] at hcoordinate

/-- The standing torus Stokes scale measured by its action on one primitive character.  This is a
constraint identity internal to the already-founded torus operator. -/
def primitiveTorusStokesScale : ℝ :=
  torusStokesEigenvalue firstPrimitiveSpatialFrequency

theorem primitiveTorusStokesScale_pos : 0 < primitiveTorusStokesScale := by
  exact torusStokesEigenvalue_pos firstPrimitiveSpatialFrequency_ne_zero

/-- Every standing torus eigenvalue is the primitive-character scale times the integer-frequency
square.  No external numerical coordinate appears in the theorem surface. -/
theorem torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared
    (frequency : SpatialFrequency) :
    torusStokesEigenvalue frequency =
      primitiveTorusStokesScale * frequencySquared frequency := by
  unfold primitiveTorusStokesScale torusStokesEigenvalue
  rw [frequencySquared_firstPrimitiveSpatialFrequency]
  ring

/-- Actual inhomogeneous H2 multiplier in the standing torus chart. -/
def h2CurlEnergyMultiplier (frequency : SpatialFrequency) : ℂ :=
  ((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)

/-! ## The exact quadratic lever arm of a closed triad -/

/-- Bilinear real pairing of two integer frequency pins before a norm receiver is taken. -/
def frequencyPairing (left right : SpatialFrequency) : ℝ :=
  ∑ coordinate : Fin 3, (left coordinate : ℝ) * (right coordinate : ℝ)

/-- Closing the frequency triangle factors the difference of its two squared-radius coordinates
through the advecting pin. -/
theorem frequencySquared_transported_sub_receiver_eq_advecting_pairing_swing
    (triad : AddressedClosedFourierTriad) :
    frequencySquared triad.transported - frequencySquared triad.receiver =
      frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported := by
  have hcoordinate : ∀ coordinate : Fin 3,
      (triad.transported coordinate : ℝ) ^ 2 -
          (triad.receiver coordinate : ℝ) ^ 2 =
        (triad.advecting coordinate : ℝ) * (triad.receiver coordinate : ℝ) -
          (triad.advecting coordinate : ℝ) *
            (triad.transported coordinate : ℝ) := by
    intro coordinate
    have hclosed := congrFun triad.closed coordinate
    have hclosedReal :
        (triad.advecting coordinate : ℝ) +
            (triad.transported coordinate : ℝ) +
              (triad.receiver coordinate : ℝ) = 0 := by
      exact_mod_cast hclosed
    calc
      (triad.transported coordinate : ℝ) ^ 2 -
          (triad.receiver coordinate : ℝ) ^ 2 =
        ((triad.transported coordinate : ℝ) -
            (triad.receiver coordinate : ℝ)) *
          ((triad.transported coordinate : ℝ) +
            (triad.receiver coordinate : ℝ)) := by ring
      _ = ((triad.transported coordinate : ℝ) -
            (triad.receiver coordinate : ℝ)) *
          (-(triad.advecting coordinate : ℝ)) := by
        congr 1
        linarith
      _ = (triad.advecting coordinate : ℝ) *
            (triad.receiver coordinate : ℝ) -
          (triad.advecting coordinate : ℝ) *
            (triad.transported coordinate : ℝ) := by ring
  calc
    frequencySquared triad.transported - frequencySquared triad.receiver =
        ∑ coordinate : Fin 3,
          ((triad.transported coordinate : ℝ) ^ 2 -
            (triad.receiver coordinate : ℝ) ^ 2) := by
      simp [frequencySquared, Finset.sum_sub_distrib]
    _ = ∑ coordinate : Fin 3,
        ((triad.advecting coordinate : ℝ) * (triad.receiver coordinate : ℝ) -
          (triad.advecting coordinate : ℝ) *
            (triad.transported coordinate : ℝ)) := by
      exact Finset.sum_congr rfl fun coordinate _hcoordinate ↦ hcoordinate coordinate
    _ = frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported := by
      simp [frequencyPairing, Finset.sum_sub_distrib]

/-- The intrinsic Stokes-coordinate difference is the same advecting-pin swing multiplied by the
full-turn scale. -/
theorem calibratedTorusStokesEigenvalue_transported_sub_receiver
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) :
    calibratedTorusStokesEigenvalue calibration triad.transported -
        calibratedTorusStokesEigenvalue calibration triad.receiver =
      calibratedStokesScale calibration *
        (frequencyPairing triad.advecting triad.receiver -
          frequencyPairing triad.advecting triad.transported) := by
  rw [calibratedTorusStokesEigenvalue, calibratedTorusStokesEigenvalue,
    ← mul_sub, frequencySquared_transported_sub_receiver_eq_advecting_pairing_swing]

/-- The standing torus Stokes difference has the same exact primitive-scale factorization. -/
theorem torusStokesEigenvalue_transported_sub_receiver
    (triad : AddressedClosedFourierTriad) :
    torusStokesEigenvalue triad.transported -
        torusStokesEigenvalue triad.receiver =
      primitiveTorusStokesScale *
        (frequencyPairing triad.advecting triad.receiver -
          frequencyPairing triad.advecting triad.transported) := by
  rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    ← mul_sub, frequencySquared_transported_sub_receiver_eq_advecting_pairing_swing]

/-! ## H2 exchanged transport is exactly the multiplier swing -/

/-- The complete exchanged H2 transfer before a norm or absolute-mass receiver. -/
def calibratedH2ExchangedTriadTransfer {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer
    (calibratedH2CurlEnergyMultiplier calibration) triad
      advectingMode transportedMode receiverMode

/-- The actual exchanged H2 transfer in the standing torus chart. -/
def h2ExchangedTriadTransfer
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer h2CurlEnergyMultiplier triad
    advectingMode transportedMode receiverMode

/-- **Exact clocked pantographic swing.**  Divergence freedom cancels the common storage weight;
the exchanged H2 transfer is precisely the Stokes-coordinate difference times the oriented
triadic face. -/
theorem calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode =
      ((calibratedTorusStokesEigenvalue calibration triad.transported -
          calibratedTorusStokesEigenvalue calibration triad.receiver : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [calibratedH2ExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence]
  unfold calibratedH2CurlEnergyMultiplier
  push_cast
  ring

/-- Actual standing-torus form of the exact H2 multiplier swing. -/
theorem h2ExchangedTriadTransfer_eq_stokesDifference_mul
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      ((torusStokesEigenvalue triad.transported -
          torusStokesEigenvalue triad.receiver : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [h2ExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence]
  unfold h2CurlEnergyMultiplier
  push_cast
  ring

/-- Fully factored form: the only surviving H2 transfer is the full-turn scale, the advecting-pin
pairing swing, and the oriented triadic face. -/
theorem calibratedH2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode =
      ((calibratedStokesScale calibration *
          (frequencyPairing triad.advecting triad.receiver -
            frequencyPairing triad.advecting triad.transported) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
    calibration triad advectingMode transportedMode receiverMode hdivergence,
    calibratedTorusStokesEigenvalue_transported_sub_receiver]

/-- Fully factored actual form through the primitive-character scale and advecting-pin lever. -/
theorem h2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      ((primitiveTorusStokesScale *
          (frequencyPairing triad.advecting triad.receiver -
            frequencyPairing triad.advecting triad.transported) : ℝ) : ℂ) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul
    triad advectingMode transportedMode receiverMode hdivergence,
    torusStokesEigenvalue_transported_sub_receiver]

/-- Equal-radius transported and receiving pins carry no exchanged H2 transfer. -/
theorem calibratedH2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
    calibration triad advectingMode transportedMode receiverMode hdivergence]
  have heigen :
      calibratedTorusStokesEigenvalue calibration triad.transported =
        calibratedTorusStokesEigenvalue calibration triad.receiver := by
    unfold calibratedTorusStokesEigenvalue
    rw [hradius]
  rw [heigen, sub_self]
  simp

/-- Equal-radius exchanged pins also return zero in the actual standing torus chart. -/
theorem h2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul
    triad advectingMode transportedMode receiverMode hdivergence]
  have heigen :
      torusStokesEigenvalue triad.transported =
        torusStokesEigenvalue triad.receiver := by
    rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
      torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared, hradius]
  rw [heigen, sub_self]
  simp

section Audit

#print axioms calibratedTorusStokesEigenvalue_eq_torusStokesEigenvalue
#print axioms frequencySquared_firstPrimitiveSpatialFrequency
#print axioms firstPrimitiveSpatialFrequency_ne_zero
#print axioms primitiveTorusStokesScale_pos
#print axioms torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared
#print axioms frequencySquared_transported_sub_receiver_eq_advecting_pairing_swing
#print axioms calibratedTorusStokesEigenvalue_transported_sub_receiver
#print axioms torusStokesEigenvalue_transported_sub_receiver
#print axioms calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
#print axioms h2ExchangedTriadTransfer_eq_stokesDifference_mul
#print axioms calibratedH2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
#print axioms h2ExchangedTriadTransfer_eq_advectingPairingSwing_mul
#print axioms calibratedH2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared
#print axioms h2ExchangedTriadTransfer_eq_zero_of_equal_frequencySquared

end Audit

end Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
