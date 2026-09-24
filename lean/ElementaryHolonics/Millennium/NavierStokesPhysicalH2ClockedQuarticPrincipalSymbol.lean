import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
import ElementaryHolonics.Millennium.NavierStokesWeightedReality

/-!
# Principal symbol of one clocked physical-H2 quartic occurrence

**[proved-derived; formal-checked]** This owner separates the homogeneous degree-four part of
the completed exchanged `H2` multiplier from its degree-two remainder before a norm, real-part,
or absolute-mass receiver is applied.  It then retains the two differentiated frequency pins,
the degree-zero Leray passage, the reciprocal degree-two clock, the selected outer insertion leg,
and the complete inner joining fibre.

The exact dilation laws below show that the clocked principal occurrence has net degree four:
the exchanged multiplier contributes four degrees, the outer and inner advective vertices
contribute one each, and the reciprocal three-pin clock removes two.  An explicit integer-frequency
family satisfies every Fourier divergence constraint and the Leray restriction while returning a
nonzero value proportional to the fourth power of the dilation.  Thus exchange, cyclic rotation,
reality, and incompressibility do not force the individual principal occurrence to lose a degree.

This is a local multiplier statement.  It proves neither an estimate after summation nor terminal
control, continuation, or existence for Navier--Stokes.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ReciprocalClockRenormalization
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedReality

/-! ## Exact integer-frequency dilation -/

/-- Integer dilation of one spatial character. -/
def dilateFrequency (scale : ℤ) (frequency : SpatialFrequency) : SpatialFrequency :=
  fun component ↦ scale * frequency component

/-- Dilation retains the two ordered outer pins rather than only their endpoint. -/
def dilateCompleteTransportAddress
    (scale : ℤ) (address : CompleteTransportAddress) : CompleteTransportAddress :=
  (dilateFrequency scale address.1, dilateFrequency scale address.2)

@[simp]
theorem dilateFrequency_apply
    (scale : ℤ) (frequency : SpatialFrequency) (component : Fin 3) :
    dilateFrequency scale frequency component = scale * frequency component := rfl

@[simp]
theorem dilateFrequency_zero (scale : ℤ) :
    dilateFrequency scale 0 = 0 := by
  ext component
  simp [dilateFrequency]

@[simp]
theorem dilateFrequency_add
    (scale : ℤ) (left right : SpatialFrequency) :
    dilateFrequency scale (left + right) =
      dilateFrequency scale left + dilateFrequency scale right := by
  ext component
  simp [dilateFrequency]
  ring

@[simp]
theorem dilateFrequency_neg (scale : ℤ) (frequency : SpatialFrequency) :
    dilateFrequency scale (-frequency) = -dilateFrequency scale frequency := by
  ext component
  simp [dilateFrequency]

theorem dilateFrequency_ne_zero
    {scale : ℤ} (hscale : scale ≠ 0)
    {frequency : SpatialFrequency} (hfrequency : frequency ≠ 0) :
    dilateFrequency scale frequency ≠ 0 := by
  intro hzero
  obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hfrequency
  have hproduct : scale * frequency component = 0 := by
    simpa [dilateFrequency] using congrFun hzero component
  exact hcomponent ((mul_eq_zero.mp hproduct).resolve_left hscale)

theorem dilateCompleteTransportAddress_ne_zero
    {scale : ℤ} (hscale : scale ≠ 0)
    {address : CompleteTransportAddress} (haddress : address ≠ (0, 0)) :
    dilateCompleteTransportAddress scale address ≠ (0, 0) := by
  intro hzero
  apply haddress
  apply Prod.ext
  · by_contra hfirst
    exact dilateFrequency_ne_zero hscale hfirst (congrArg Prod.fst hzero)
  · by_contra hsecond
    exact dilateFrequency_ne_zero hscale hsecond (congrArg Prod.snd hzero)

@[simp]
theorem completeTransportReceiver_dilate
    (scale : ℤ) (address : CompleteTransportAddress) :
    completeTransportReceiver (dilateCompleteTransportAddress scale address) =
      dilateFrequency scale (completeTransportReceiver address) := by
  ext component
  simp [completeTransportReceiver, dilateCompleteTransportAddress, dilateFrequency]
  ring

@[simp]
theorem physicalH2InsertionFrequency_dilate
    (scale : ℤ) (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg) :
    physicalH2InsertionFrequency (dilateCompleteTransportAddress scale address) leg =
      dilateFrequency scale (physicalH2InsertionFrequency address leg) := by
  cases leg with
  | advecting => rfl
  | transported => rfl
  | receiver => exact completeTransportReceiver_dilate scale address

@[simp]
theorem transportedFrequencyAt_dilate
    (scale : ℤ) (output alpha : SpatialFrequency) :
    transportedFrequencyAt (dilateFrequency scale output) (dilateFrequency scale alpha) =
      dilateFrequency scale (transportedFrequencyAt output alpha) := by
  unfold transportedFrequencyAt
  ext component
  simp [dilateFrequency]
  ring

@[simp]
theorem frequencySquared_dilate
    (scale : ℤ) (frequency : SpatialFrequency) :
    frequencySquared (dilateFrequency scale frequency) =
      (scale : ℝ) ^ 2 * frequencySquared frequency := by
  simp [frequencySquared, dilateFrequency, Fin.sum_univ_succ]
  ring

/-! ## The completed multiplier split -/

/-- The homogeneous degree-four polynomial in the transported and receiver squares. -/
def physicalH2QuarticPrincipalExchangeSwing
    (address : CompleteTransportAddress) : ℝ :=
  (frequencySquared address.2 -
      frequencySquared (completeTransportReceiver address)) *
    (frequencySquared address.2 +
      frequencySquared (completeTransportReceiver address))

/-- The surviving homogeneous degree-two part of the completed exchanged multiplier. -/
def physicalH2QuadraticExchangeSwing
    (address : CompleteTransportAddress) : ℝ :=
  primitiveTorusStokesScale *
    (frequencySquared address.2 -
      frequencySquared (completeTransportReceiver address))

/-- The actual degree-four coefficient in the standing primitive-character Stokes chart. -/
def physicalH2QuarticPrincipalExchangeMultiplier
    (address : CompleteTransportAddress) : ℂ :=
  ((primitiveTorusStokesScale ^ 2 *
      physicalH2QuarticPrincipalExchangeSwing address : ℝ) : ℂ)

/-- The completed inhomogeneous outer coefficient is exactly its degree-two remainder plus the
degree-four principal coefficient. -/
theorem physicalH2ExchangedTriadMultiplier_eq_quadratic_add_quartic
    (address : CompleteTransportAddress) :
    physicalH2ExchangedTriadMultiplier address =
      (physicalH2QuadraticExchangeSwing address : ℂ) +
        physicalH2QuarticPrincipalExchangeMultiplier address := by
  unfold physicalH2ExchangedTriadMultiplier physicalH2QuadraticExchangeSwing
    physicalH2QuarticPrincipalExchangeMultiplier
    physicalH2QuarticPrincipalExchangeSwing
  rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
  push_cast
  ring

/-- The principal outer coefficient has exact integer-frequency degree four. -/
theorem physicalH2QuarticPrincipalExchangeSwing_dilate
    (scale : ℤ) (address : CompleteTransportAddress) :
    physicalH2QuarticPrincipalExchangeSwing
        (dilateCompleteTransportAddress scale address) =
      (scale : ℝ) ^ 4 * physicalH2QuarticPrincipalExchangeSwing address := by
  unfold physicalH2QuarticPrincipalExchangeSwing
  rw [completeTransportReceiver_dilate]
  simp only [dilateCompleteTransportAddress, frequencySquared_dilate]
  ring

/-- Exchange reverses the principal swing; it does not annihilate it. -/
@[simp]
theorem physicalH2QuarticPrincipalExchangeSwing_exchange
    (address : CompleteTransportAddress) :
    physicalH2QuarticPrincipalExchangeSwing (completeTransportExchange address) =
      -physicalH2QuarticPrincipalExchangeSwing address := by
  simp [physicalH2QuarticPrincipalExchangeSwing]
  ring

/-- Reality reflection preserves the real principal swing. -/
@[simp]
theorem physicalH2QuarticPrincipalExchangeSwing_reality
    (address : CompleteTransportAddress) :
    physicalH2QuarticPrincipalExchangeSwing (physicalH2RealityAddress address) =
      physicalH2QuarticPrincipalExchangeSwing address := by
  unfold physicalH2QuarticPrincipalExchangeSwing
  rw [completeTransportReceiver_realityAddress]
  simp [physicalH2RealityAddress, frequencySquared_neg]

/-- The same principal swing on an arbitrary addressed closed triad. -/
def closedTriadQuarticPrincipalSwing (triad : AddressedClosedFourierTriad) : ℝ :=
  (frequencySquared triad.transported - frequencySquared triad.receiver) *
    (frequencySquared triad.transported + frequencySquared triad.receiver)

/-- Three cyclic roles telescope only at the scalar multiplier face.  Their differentiated
amplitude/Leray fibres remain distinct and are not identified by this equality. -/
theorem closedTriadQuarticPrincipalSwing_cyclic_sum_eq_zero
    (triad : AddressedClosedFourierTriad) :
    closedTriadQuarticPrincipalSwing triad +
        closedTriadQuarticPrincipalSwing triad.rotate +
        closedTriadQuarticPrincipalSwing triad.rotate.rotate = 0 := by
  simp [closedTriadQuarticPrincipalSwing]
  ring

theorem closedTriadQuarticPrincipalSwing_completeTransportTriad
    (address : CompleteTransportAddress) :
    closedTriadQuarticPrincipalSwing (completeTransportTriad address) =
      physicalH2QuarticPrincipalExchangeSwing address := rfl

/-! ## One principal occurrence before norms -/

/-- The selected outer insertion face before either homogeneous multiplier component is applied. -/
def physicalH2BareInsertionLegFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) :
    PhysicalH2InsertionLeg → ComplexVector → ℂ
  | .advecting, inserted =>
      triadicEnergyFace address.1 address.2 inserted
        (velocityMode address.2)
        (velocityMode (completeTransportReceiver address))
  | .transported, inserted =>
      triadicEnergyFace address.1 address.2
        (velocityMode address.1) inserted
        (velocityMode (completeTransportReceiver address))
  | .receiver, inserted =>
      triadicEnergyFace address.1 address.2
        (velocityMode address.1) (velocityMode address.2) inserted

@[simp]
theorem physicalH2VelocityExchangedInsertionLegFace_eq_multiplier_mul_bare
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (inserted : ComplexVector) :
    physicalH2VelocityExchangedInsertionLegFace velocityMode address leg inserted =
      physicalH2ExchangedTriadMultiplier address *
        physicalH2BareInsertionLegFace velocityMode address leg inserted := by
  cases leg <;> rfl

/-- One literal term of the already-admitted finite pullback, before any of its three sums. -/
def clockedPhysicalH2QuarticOccurrenceFace
    (nu : ℝ) (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (innerAlpha : SpatialFrequency) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    physicalH2VelocityExchangedInsertionLegFace velocityMode address leg
      (finitePhysicalH2ProjectedSourceAtom velocityMode
        (physicalH2InsertionFrequency address leg) innerAlpha)

/-- Its degree-two remainder, with the same clock, derivative vertices, Leray passage, amplitudes,
and reconstruction fibre. -/
def clockedPhysicalH2QuadraticOccurrenceFace
    (nu : ℝ) (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (innerAlpha : SpatialFrequency) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    (physicalH2QuadraticExchangeSwing address : ℂ) *
      physicalH2BareInsertionLegFace velocityMode address leg
        (finitePhysicalH2ProjectedSourceAtom velocityMode
          (physicalH2InsertionFrequency address leg) innerAlpha)

/-- Its exact degree-four principal component in the standing physical chart. -/
def clockedPhysicalH2QuarticPrincipalOccurrenceFace
    (nu : ℝ) (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (innerAlpha : SpatialFrequency) : ℂ :=
  physicalH2TriadReciprocalClock nu address *
    physicalH2QuarticPrincipalExchangeMultiplier address *
      physicalH2BareInsertionLegFace velocityMode address leg
        (finitePhysicalH2ProjectedSourceAtom velocityMode
          (physicalH2InsertionFrequency address leg) innerAlpha)

/-- **Exact occurrence-level principal split.**  This holds for each of the three insertion legs
and every retained inner address before any summation or norm. -/
theorem clockedPhysicalH2QuarticOccurrenceFace_eq_quadratic_add_principal
    (nu : ℝ) (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (innerAlpha : SpatialFrequency) :
    clockedPhysicalH2QuarticOccurrenceFace nu velocityMode address leg innerAlpha =
      clockedPhysicalH2QuadraticOccurrenceFace
          nu velocityMode address leg innerAlpha +
        clockedPhysicalH2QuarticPrincipalOccurrenceFace
          nu velocityMode address leg innerAlpha := by
  unfold clockedPhysicalH2QuarticOccurrenceFace
    clockedPhysicalH2QuadraticOccurrenceFace
    clockedPhysicalH2QuarticPrincipalOccurrenceFace
  rw [physicalH2VelocityExchangedInsertionLegFace_eq_multiplier_mul_bare,
    physicalH2ExchangedTriadMultiplier_eq_quadratic_add_quartic]
  ring

/-- The derivative factor of an advective interaction with the universal torus calibration
removed. -/
def normalizedAdvectiveInteraction
    (derivativeFrequency : SpatialFrequency)
    (advectingMode transportedMode : ComplexVector) : ComplexVector :=
  (complexDot (complexFrequencyVector derivativeFrequency) advectingMode) •
    transportedMode

/-- The normalized inner principal source at one retained oriented convolution address. -/
def normalizedPrincipalProjectedSourceAtom
    (output alpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector) : ComplexVector :=
  -lerayProjectMode output
    (normalizedAdvectiveInteraction (transportedFrequencyAt output alpha)
      innerAdvectingMode innerTransportedMode)

/-- The outer normalized insertion face.  Its three constructors retain all three product-rule
occurrences. -/
def normalizedPrincipalOuterInsertionFace
    (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) : ℂ :=
  match leg with
  | .advecting =>
      complexDot
        (normalizedAdvectiveInteraction address.2 inserted outerTransportedMode)
        outerReceiverMode
  | .transported =>
      complexDot
        (normalizedAdvectiveInteraction address.2 outerAdvectingMode inserted)
        outerReceiverMode
  | .receiver =>
      complexDot
        (normalizedAdvectiveInteraction address.2 outerAdvectingMode outerTransportedMode)
        inserted

/-- The clock denominator stripped of viscosity and the universal primitive-character scale. -/
def normalizedPhysicalH2TriadClockSquare
    (address : CompleteTransportAddress) : ℝ :=
  frequencySquared address.1 + frequencySquared address.2 +
    frequencySquared (completeTransportReceiver address)

/-- One exact normalized principal-symbol occurrence.  The zero-clock address remains in the
population and is assigned zero. -/
def normalizedClockedPhysicalH2QuarticPrincipalSymbol
    (address : CompleteTransportAddress) (leg : PhysicalH2InsertionLeg)
    (innerAlpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) : ℂ :=
  if address = (0, 0) then 0
  else
    ((physicalH2QuarticPrincipalExchangeSwing address /
      normalizedPhysicalH2TriadClockSquare address : ℝ) : ℂ) *
      normalizedPrincipalOuterInsertionFace address leg
        (normalizedPrincipalProjectedSourceAtom
          (physicalH2InsertionFrequency address leg) innerAlpha
          innerAdvectingMode innerTransportedMode)
        outerAdvectingMode outerTransportedMode outerReceiverMode

/-- Leray projection makes every retained inner source transverse to its selected outer pin. -/
theorem complexDot_normalizedPrincipalProjectedSourceAtom_eq_zero
    (output alpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector) :
    complexDot (complexFrequencyVector output)
        (normalizedPrincipalProjectedSourceAtom output alpha
          innerAdvectingMode innerTransportedMode) = 0 := by
  unfold normalizedPrincipalProjectedSourceAtom
  rw [complexDot, dotProduct_neg]
  change
    -complexDot (complexFrequencyVector output)
        (lerayProjectMode output
          (normalizedAdvectiveInteraction (transportedFrequencyAt output alpha)
            innerAdvectingMode innerTransportedMode)) = 0
  rw [complexDot_lerayProjectMode_eq_zero]
  simp

/-- A raw inner current parallel to its output lies in the exact Leray radical. -/
theorem normalizedPrincipalProjectedSourceAtom_eq_zero_of_parallel
    (output alpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector)
    (scale : ℂ)
    (hparallel :
      normalizedAdvectiveInteraction (transportedFrequencyAt output alpha)
          innerAdvectingMode innerTransportedMode =
        scale • complexFrequencyVector output) :
    normalizedPrincipalProjectedSourceAtom output alpha
        innerAdvectingMode innerTransportedMode = 0 := by
  unfold normalizedPrincipalProjectedSourceAtom
  rw [hparallel, lerayProjectMode_smul_complexFrequencyVector_eq_zero]
  simp

/-! ## Homogeneity through both vertices and the clock -/

@[simp]
theorem complexFrequencyVector_dilate
    (scale : ℤ) (frequency : SpatialFrequency) :
    complexFrequencyVector (dilateFrequency scale frequency) =
      (scale : ℂ) • complexFrequencyVector frequency := by
  ext component
  simp [complexFrequencyVector, dilateFrequency]

theorem complexDot_complexFrequencyVector_dilate
    (scale : ℤ) (frequency : SpatialFrequency) (mode : ComplexVector) :
    complexDot (complexFrequencyVector (dilateFrequency scale frequency)) mode =
      (scale : ℂ) * complexDot (complexFrequencyVector frequency) mode := by
  rw [complexFrequencyVector_dilate]
  simp [complexDot, smul_dotProduct]

theorem normalizedAdvectiveInteraction_dilate
    (scale : ℤ) (derivativeFrequency : SpatialFrequency)
    (advectingMode transportedMode : ComplexVector) :
    normalizedAdvectiveInteraction (dilateFrequency scale derivativeFrequency)
        advectingMode transportedMode =
      (scale : ℂ) • normalizedAdvectiveInteraction derivativeFrequency
        advectingMode transportedMode := by
  unfold normalizedAdvectiveInteraction
  rw [complexDot_complexFrequencyVector_dilate]
  simp [smul_smul]

theorem lerayProjectMode_dilate
    {scale : ℤ} (hscale : scale ≠ 0)
    (frequency : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectMode (dilateFrequency scale frequency) mode =
      lerayProjectMode frequency mode := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    simp
  · have hdilated : dilateFrequency scale frequency ≠ 0 :=
      dilateFrequency_ne_zero hscale hfrequency
    have hscaleComplex : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
    have hfrequencyReal : frequencySquared frequency ≠ 0 :=
      (frequencySquared_pos hfrequency).ne'
    have hfrequencyComplex : (frequencySquared frequency : ℂ) ≠ 0 := by
      exact_mod_cast hfrequencyReal
    have hdot := complexDot_complexFrequencyVector_dilate scale frequency mode
    rw [lerayProjectMode, if_neg hdilated, lerayProjectMode, if_neg hfrequency,
      hdot, frequencySquared_dilate, complexFrequencyVector_dilate]
    ext component
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp

theorem normalizedPrincipalProjectedSourceAtom_dilate
    {scale : ℤ} (hscale : scale ≠ 0)
    (output alpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector) :
    normalizedPrincipalProjectedSourceAtom
        (dilateFrequency scale output) (dilateFrequency scale alpha)
        innerAdvectingMode innerTransportedMode =
      (scale : ℂ) • normalizedPrincipalProjectedSourceAtom output alpha
        innerAdvectingMode innerTransportedMode := by
  unfold normalizedPrincipalProjectedSourceAtom
  rw [transportedFrequencyAt_dilate, normalizedAdvectiveInteraction_dilate,
    lerayProjectMode_dilate hscale]
  change
    -(lerayProjectModeLinearMap output)
        ((scale : ℂ) • normalizedAdvectiveInteraction
          (transportedFrequencyAt output alpha)
          innerAdvectingMode innerTransportedMode) = _
  rw [map_smul]
  change
    -((scale : ℂ) • lerayProjectMode output
      (normalizedAdvectiveInteraction (transportedFrequencyAt output alpha)
        innerAdvectingMode innerTransportedMode)) =
      (scale : ℂ) •
        (-lerayProjectMode output
          (normalizedAdvectiveInteraction (transportedFrequencyAt output alpha)
            innerAdvectingMode innerTransportedMode))
  ext component
  simp

theorem normalizedPrincipalOuterInsertionFace_dilate
    (scale : ℤ) (address : CompleteTransportAddress)
    (leg : PhysicalH2InsertionLeg) (inserted : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) :
    normalizedPrincipalOuterInsertionFace
        (dilateCompleteTransportAddress scale address) leg
        ((scale : ℂ) • inserted)
        outerAdvectingMode outerTransportedMode outerReceiverMode =
      (scale : ℂ) ^ 2 *
        normalizedPrincipalOuterInsertionFace address leg inserted
          outerAdvectingMode outerTransportedMode outerReceiverMode := by
  cases leg <;>
    simp [normalizedPrincipalOuterInsertionFace, normalizedAdvectiveInteraction,
      dilateCompleteTransportAddress,
      complexDot, dotProduct_smul, smul_dotProduct, smul_eq_mul] <;>
    ring

@[simp]
theorem normalizedPhysicalH2TriadClockSquare_dilate
    (scale : ℤ) (address : CompleteTransportAddress) :
    normalizedPhysicalH2TriadClockSquare
        (dilateCompleteTransportAddress scale address) =
      (scale : ℝ) ^ 2 * normalizedPhysicalH2TriadClockSquare address := by
  unfold normalizedPhysicalH2TriadClockSquare
  rw [completeTransportReceiver_dilate]
  simp only [dilateCompleteTransportAddress, frequencySquared_dilate]
  ring

theorem normalizedPhysicalH2TriadClockSquare_pos
    {address : CompleteTransportAddress} (haddress : address ≠ (0, 0)) :
    0 < normalizedPhysicalH2TriadClockSquare address := by
  unfold normalizedPhysicalH2TriadClockSquare
  by_cases hfirst : address.1 = 0
  · have hsecond : address.2 ≠ 0 := by
      intro hsecond
      exact haddress (Prod.ext hfirst hsecond)
    linarith [frequencySquared_pos hsecond,
      sq_nonneg (0 : ℝ),
      show 0 ≤ frequencySquared address.1 by
        unfold frequencySquared
        positivity,
      show 0 ≤ frequencySquared (completeTransportReceiver address) by
        unfold frequencySquared
        positivity]
  · linarith [frequencySquared_pos hfirst,
      show 0 ≤ frequencySquared address.2 by
        unfold frequencySquared
        positivity,
      show 0 ≤ frequencySquared (completeTransportReceiver address) by
        unfold frequencySquared
        positivity]

/-- **All three insertion legs have exact net frequency degree four.**  This identity transports
the complete normalized principal occurrence, not merely its scalar outer coefficient. -/
theorem normalizedClockedPhysicalH2QuarticPrincipalSymbol_dilate
    {scale : ℤ} (hscale : scale ≠ 0)
    {address : CompleteTransportAddress} (haddress : address ≠ (0, 0))
    (leg : PhysicalH2InsertionLeg) (innerAlpha : SpatialFrequency)
    (innerAdvectingMode innerTransportedMode : ComplexVector)
    (outerAdvectingMode outerTransportedMode outerReceiverMode : ComplexVector) :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (dilateCompleteTransportAddress scale address) leg
        (dilateFrequency scale innerAlpha)
        innerAdvectingMode innerTransportedMode
        outerAdvectingMode outerTransportedMode outerReceiverMode =
      (scale : ℂ) ^ 4 *
        normalizedClockedPhysicalH2QuarticPrincipalSymbol address leg innerAlpha
          innerAdvectingMode innerTransportedMode
          outerAdvectingMode outerTransportedMode outerReceiverMode := by
  have hdilated := dilateCompleteTransportAddress_ne_zero hscale haddress
  have hscaleReal : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale
  have hscaleComplex : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  have hclock : normalizedPhysicalH2TriadClockSquare address ≠ 0 :=
    (normalizedPhysicalH2TriadClockSquare_pos haddress).ne'
  unfold normalizedClockedPhysicalH2QuarticPrincipalSymbol
  rw [if_neg hdilated, if_neg haddress,
    physicalH2QuarticPrincipalExchangeSwing_dilate,
    normalizedPhysicalH2TriadClockSquare_dilate,
    physicalH2InsertionFrequency_dilate,
    normalizedPrincipalProjectedSourceAtom_dilate hscale,
    normalizedPrincipalOuterInsertionFace_dilate]
  push_cast
  field_simp

/-! ## A frequency-concentrated noncancellation witness -/

/-- Outer pins `p = (1,0,0)` and `q = (0,1,0)`; closure retains
`r = (-1,-1,0)`. -/
def principalWitnessOuterAddress : CompleteTransportAddress :=
  ((![1, 0, 0] : SpatialFrequency), (![0, 1, 0] : SpatialFrequency))

/-- Inner advecting pin `alpha = (0,0,1)`; the retained transported pin is
`beta = p - alpha = (1,0,-1)`. -/
def principalWitnessInnerAlpha : SpatialFrequency := ![0, 0, 1]

def principalWitnessInnerAdvectingMode : ComplexVector := ![1, 0, 0]
def principalWitnessInnerTransportedMode : ComplexVector := ![0, 1, 0]
def principalWitnessOuterAdvectingMode : ComplexVector := ![0, 1, 0]
def principalWitnessOuterTransportedMode : ComplexVector := ![0, 0, 1]
def principalWitnessOuterReceiverMode : ComplexVector := ![0, 0, 1]

/-- The witness keeps every frequency and amplitude occurrence needed to reconstruct the
principal face.  No terminal value or norm quotient is used as its identity. -/
structure PhysicalH2QuarticPrincipalWitnessFiber where
  outerAddress : CompleteTransportAddress
  insertionLeg : PhysicalH2InsertionLeg
  innerAlpha : SpatialFrequency
  innerBeta : SpatialFrequency
  innerJoined : innerAlpha + innerBeta =
    physicalH2InsertionFrequency outerAddress insertionLeg
  innerAdvectingMode : ComplexVector
  innerTransportedMode : ComplexVector
  outerAdvectingMode : ComplexVector
  outerTransportedMode : ComplexVector
  outerReceiverMode : ComplexVector

/-- The complete reconstruction fibre of the explicit advancing-leg witness. -/
def principalWitnessFiber : PhysicalH2QuarticPrincipalWitnessFiber where
  outerAddress := principalWitnessOuterAddress
  insertionLeg := .advecting
  innerAlpha := principalWitnessInnerAlpha
  innerBeta := transportedFrequencyAt
    (physicalH2InsertionFrequency principalWitnessOuterAddress .advecting)
    principalWitnessInnerAlpha
  innerJoined := advecting_add_transportedFrequencyAt _ _
  innerAdvectingMode := principalWitnessInnerAdvectingMode
  innerTransportedMode := principalWitnessInnerTransportedMode
  outerAdvectingMode := principalWitnessOuterAdvectingMode
  outerTransportedMode := principalWitnessOuterTransportedMode
  outerReceiverMode := principalWitnessOuterReceiverMode

@[simp]
theorem principalWitness_receiver :
    completeTransportReceiver principalWitnessOuterAddress =
      (![(-1 : ℤ), -1, 0] : SpatialFrequency) := by
  ext component
  fin_cases component <;>
    norm_num [principalWitnessOuterAddress, completeTransportReceiver]

@[simp]
theorem principalWitness_innerBeta :
    transportedFrequencyAt
        (physicalH2InsertionFrequency principalWitnessOuterAddress .advecting)
        principalWitnessInnerAlpha =
      (![1, 0, -1] : SpatialFrequency) := by
  ext component
  fin_cases component <;>
    norm_num [principalWitnessOuterAddress, principalWitnessInnerAlpha,
      transportedFrequencyAt]

/-- Every entering amplitude is divergence-free at its own addressed frequency. -/
theorem principalWitness_innerAdvecting_divergenceFree :
    complexDot (complexFrequencyVector principalWitnessInnerAlpha)
      principalWitnessInnerAdvectingMode = 0 := by
  norm_num [principalWitnessInnerAlpha, principalWitnessInnerAdvectingMode,
    complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]

theorem principalWitness_innerTransported_divergenceFree :
    complexDot
        (complexFrequencyVector
          (transportedFrequencyAt
            (physicalH2InsertionFrequency principalWitnessOuterAddress .advecting)
            principalWitnessInnerAlpha))
        principalWitnessInnerTransportedMode = 0 := by
  rw [principalWitness_innerBeta]
  norm_num [principalWitnessInnerTransportedMode, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

theorem principalWitness_outerTransported_divergenceFree :
    complexDot (complexFrequencyVector principalWitnessOuterAddress.2)
      principalWitnessOuterTransportedMode = 0 := by
  norm_num [principalWitnessOuterAddress, principalWitnessOuterTransportedMode,
    complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]

theorem principalWitness_outerReceiver_divergenceFree :
    complexDot
        (complexFrequencyVector
          (completeTransportReceiver principalWitnessOuterAddress))
        principalWitnessOuterReceiverMode = 0 := by
  rw [principalWitness_receiver]
  norm_num [principalWitnessOuterReceiverMode, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

/-- The inner Leray passage is active and returns `-e₂`; it is neither zero nor a discarded
longitudinal component. -/
theorem principalWitness_projectedSourceAtom :
    normalizedPrincipalProjectedSourceAtom
        (physicalH2InsertionFrequency principalWitnessOuterAddress .advecting)
        principalWitnessInnerAlpha
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode =
      (![0, -1, 0] : ComplexVector) := by
  ext component
  fin_cases component <;>
    norm_num [normalizedPrincipalProjectedSourceAtom,
      normalizedAdvectiveInteraction, principalWitnessOuterAddress,
      principalWitnessInnerAlpha, principalWitnessInnerAdvectingMode,
      principalWitnessInnerTransportedMode, transportedFrequencyAt,
      lerayProjectMode, frequencySquared, complexDot, dotProduct,
      complexFrequencyVector, Fin.sum_univ_succ]

theorem principalWitness_principalSwing :
    physicalH2QuarticPrincipalExchangeSwing principalWitnessOuterAddress = -3 := by
  norm_num [physicalH2QuarticPrincipalExchangeSwing, principalWitnessOuterAddress,
    completeTransportReceiver, frequencySquared, Fin.sum_univ_succ]

theorem principalWitness_clockSquare :
    normalizedPhysicalH2TriadClockSquare principalWitnessOuterAddress = 4 := by
  norm_num [normalizedPhysicalH2TriadClockSquare, principalWitnessOuterAddress,
    completeTransportReceiver, frequencySquared, Fin.sum_univ_succ]

theorem principalWitness_outerInsertionFace :
    normalizedPrincipalOuterInsertionFace principalWitnessOuterAddress .advecting
        (normalizedPrincipalProjectedSourceAtom
          (physicalH2InsertionFrequency principalWitnessOuterAddress .advecting)
          principalWitnessInnerAlpha
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode)
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode = -1 := by
  rw [principalWitness_projectedSourceAtom]
  norm_num [normalizedPrincipalOuterInsertionFace, normalizedAdvectiveInteraction,
    principalWitnessOuterAddress, principalWitnessOuterTransportedMode,
    principalWitnessOuterReceiverMode, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

/-- **Exact noncancellation at unit scale.** -/
theorem principalWitness_symbol_eq_three_fourths :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        principalWitnessOuterAddress .advecting principalWitnessInnerAlpha
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode = (3 / 4 : ℂ) := by
  have haddress : principalWitnessOuterAddress ≠ (0, 0) := by
    intro hzero
    have := congrArg (fun address : CompleteTransportAddress ↦ address.1 0) hzero
    norm_num [principalWitnessOuterAddress] at this
  unfold normalizedClockedPhysicalH2QuarticPrincipalSymbol
  rw [if_neg haddress, principalWitness_principalSwing,
    principalWitness_clockSquare, principalWitness_outerInsertionFace]
  norm_num

/-- The exchanged occurrence also returns `3/4`: exchange reverses both the scalar swing and the
divergence-free outer face. -/
theorem principalWitness_exchanged_symbol_eq_three_fourths :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (completeTransportExchange principalWitnessOuterAddress) .advecting
        principalWitnessInnerAlpha
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
        principalWitnessOuterTransportedMode = (3 / 4 : ℂ) := by
  norm_num [normalizedClockedPhysicalH2QuarticPrincipalSymbol,
    physicalH2QuarticPrincipalExchangeSwing, normalizedPhysicalH2TriadClockSquare,
    normalizedPrincipalOuterInsertionFace, normalizedPrincipalProjectedSourceAtom,
    normalizedAdvectiveInteraction, principalWitnessOuterAddress,
    principalWitnessInnerAlpha, principalWitnessInnerAdvectingMode,
    principalWitnessInnerTransportedMode, principalWitnessOuterAdvectingMode,
    principalWitnessOuterTransportedMode, principalWitnessOuterReceiverMode,
    completeTransportExchange, completeTransportReceiver, transportedFrequencyAt,
    lerayProjectMode, frequencySquared, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

/-- Exchange pairing preserves rather than cancels this principal occurrence. -/
theorem principalWitness_exchange_pair_eq_three_halves :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
          principalWitnessOuterAddress .advecting principalWitnessInnerAlpha
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode +
        normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (completeTransportExchange principalWitnessOuterAddress) .advecting
          principalWitnessInnerAlpha
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
          principalWitnessOuterTransportedMode = (3 / 2 : ℂ) := by
  rw [principalWitness_symbol_eq_three_fourths,
    principalWitness_exchanged_symbol_eq_three_fourths]
  norm_num

/-- Reality reflection retains the original nonzero occurrence.  The two frequency derivatives
both reverse, while the real amplitude data are fixed by conjugation. -/
theorem principalWitness_reality_symbol_eq_three_fourths :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (physicalH2RealityAddress principalWitnessOuterAddress) .advecting
        (-principalWitnessInnerAlpha)
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode = (3 / 4 : ℂ) := by
  norm_num [normalizedClockedPhysicalH2QuarticPrincipalSymbol,
    physicalH2QuarticPrincipalExchangeSwing, normalizedPhysicalH2TriadClockSquare,
    normalizedPrincipalOuterInsertionFace, normalizedPrincipalProjectedSourceAtom,
    normalizedAdvectiveInteraction, principalWitnessOuterAddress,
    principalWitnessInnerAlpha, principalWitnessInnerAdvectingMode,
    principalWitnessInnerTransportedMode, principalWitnessOuterAdvectingMode,
    principalWitnessOuterTransportedMode, principalWitnessOuterReceiverMode,
    physicalH2RealityAddress, completeTransportReceiver, transportedFrequencyAt,
    lerayProjectMode, frequencySquared, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

/-- Reality reflection also retains the exchanged occurrence. -/
theorem principalWitness_exchanged_reality_symbol_eq_three_fourths :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (physicalH2RealityAddress
          (completeTransportExchange principalWitnessOuterAddress)) .advecting
        (-principalWitnessInnerAlpha)
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
        principalWitnessOuterTransportedMode = (3 / 4 : ℂ) := by
  norm_num [normalizedClockedPhysicalH2QuarticPrincipalSymbol,
    physicalH2QuarticPrincipalExchangeSwing, normalizedPhysicalH2TriadClockSquare,
    normalizedPrincipalOuterInsertionFace, normalizedPrincipalProjectedSourceAtom,
    normalizedAdvectiveInteraction, principalWitnessOuterAddress,
    principalWitnessInnerAlpha, principalWitnessInnerAdvectingMode,
    principalWitnessInnerTransportedMode, principalWitnessOuterAdvectingMode,
    principalWitnessOuterTransportedMode, principalWitnessOuterReceiverMode,
    physicalH2RealityAddress, completeTransportExchange, completeTransportReceiver,
    transportedFrequencyAt, lerayProjectMode, frequencySquared, complexDot,
    dotProduct, complexFrequencyVector, Fin.sum_univ_succ]

/-- The exchange pair together with its reality pair adds to the nonzero real face `3`. -/
theorem principalWitness_exchange_reality_total_eq_three :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
          principalWitnessOuterAddress .advecting principalWitnessInnerAlpha
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode +
        normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (completeTransportExchange principalWitnessOuterAddress) .advecting
          principalWitnessInnerAlpha
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
          principalWitnessOuterTransportedMode +
        normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (physicalH2RealityAddress principalWitnessOuterAddress) .advecting
          (-principalWitnessInnerAlpha)
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode +
        normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (physicalH2RealityAddress
            (completeTransportExchange principalWitnessOuterAddress)) .advecting
          (-principalWitnessInnerAlpha)
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
          principalWitnessOuterTransportedMode = (3 : ℂ) := by
  rw [principalWitness_symbol_eq_three_fourths,
    principalWitness_exchanged_symbol_eq_three_fourths,
    principalWitness_reality_symbol_eq_three_fourths,
    principalWitness_exchanged_reality_symbol_eq_three_fourths]
  norm_num

/-- The full all-leg homogeneity theorem specializes to the explicit witness family. -/
theorem principalWitness_symbol_dilate
    {scale : ℤ} (hscale : scale ≠ 0) :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (dilateCompleteTransportAddress scale principalWitnessOuterAddress) .advecting
        (dilateFrequency scale principalWitnessInnerAlpha)
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode =
      (scale : ℂ) ^ 4 * (3 / 4 : ℂ) := by
  have haddress : principalWitnessOuterAddress ≠ (0, 0) := by
    intro hzero
    have := congrArg (fun address : CompleteTransportAddress ↦ address.1 0) hzero
    norm_num [principalWitnessOuterAddress] at this
  rw [normalizedClockedPhysicalH2QuarticPrincipalSymbol_dilate hscale haddress,
    principalWitness_symbol_eq_three_fourths]

/-- The exchanged member of the witness family has the same exact fourth-degree dilation. -/
theorem principalWitness_exchanged_symbol_dilate
    {scale : ℤ} (hscale : scale ≠ 0) :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (dilateCompleteTransportAddress scale
          (completeTransportExchange principalWitnessOuterAddress)) .advecting
        (dilateFrequency scale principalWitnessInnerAlpha)
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
        principalWitnessOuterTransportedMode =
      (scale : ℂ) ^ 4 * (3 / 4 : ℂ) := by
  have haddress :
      completeTransportExchange principalWitnessOuterAddress ≠ (0, 0) := by
    intro hzero
    have := congrArg (fun address : CompleteTransportAddress ↦ address.1 0) hzero
    norm_num [principalWitnessOuterAddress, completeTransportExchange] at this
  rw [normalizedClockedPhysicalH2QuarticPrincipalSymbol_dilate hscale haddress,
    principalWitness_exchanged_symbol_eq_three_fourths]

/-- Exchange noncancellation persists at every nonzero integer scale with exact degree four. -/
theorem principalWitness_exchange_pair_dilate
    {scale : ℤ} (hscale : scale ≠ 0) :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (dilateCompleteTransportAddress scale principalWitnessOuterAddress) .advecting
          (dilateFrequency scale principalWitnessInnerAlpha)
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode +
        normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (dilateCompleteTransportAddress scale
            (completeTransportExchange principalWitnessOuterAddress)) .advecting
          (dilateFrequency scale principalWitnessInnerAlpha)
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterReceiverMode
          principalWitnessOuterTransportedMode =
      (scale : ℂ) ^ 4 * (3 / 2 : ℂ) := by
  rw [principalWitness_symbol_dilate hscale,
    principalWitness_exchanged_symbol_dilate hscale]
  ring

/-- Every nonzero integer dilation retains a nonzero principal occurrence. -/
theorem principalWitness_symbol_dilate_ne_zero
    {scale : ℤ} (hscale : scale ≠ 0) :
    normalizedClockedPhysicalH2QuarticPrincipalSymbol
        (dilateCompleteTransportAddress scale principalWitnessOuterAddress) .advecting
        (dilateFrequency scale principalWitnessInnerAlpha)
        principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
        principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
        principalWitnessOuterReceiverMode ≠ 0 := by
  rw [principalWitness_symbol_dilate hscale]
  exact mul_ne_zero (pow_ne_zero 4 (by exact_mod_cast hscale)) (by norm_num)

/-- Against any natural cubic coefficient `bound`, the explicit scale `4 * bound + 1` has
strictly larger real principal amplitude than `bound * scale^3`.  This is a quantitative,
frequency-concentrated obstruction to a uniform order-three amplitude bound. -/
theorem principalWitness_quarticAmplitude_exceeds_nat_orderThree_bound (bound : ℕ) :
    let scale : ℝ := 4 * (bound : ℝ) + 1
    scale ^ 4 * (3 / 4 : ℝ) > (bound : ℝ) * scale ^ 3 := by
  dsimp only
  have hbound : 0 ≤ (bound : ℝ) := by positivity
  nlinarith [sq_nonneg ((4 : ℝ) * bound + 1),
    mul_nonneg hbound (sq_nonneg ((4 : ℝ) * bound + 1))]

/-- There is no degree-three homogeneous coefficient representing this fixed-amplitude witness
under every nonzero integer dilation. -/
theorem principalWitness_not_homogeneous_degree_three :
    ¬ ∃ coefficient : ℂ, ∀ scale : ℤ, scale ≠ 0 →
      normalizedClockedPhysicalH2QuarticPrincipalSymbol
          (dilateCompleteTransportAddress scale principalWitnessOuterAddress) .advecting
          (dilateFrequency scale principalWitnessInnerAlpha)
          principalWitnessInnerAdvectingMode principalWitnessInnerTransportedMode
          principalWitnessOuterAdvectingMode principalWitnessOuterTransportedMode
          principalWitnessOuterReceiverMode =
        (scale : ℂ) ^ 3 * coefficient := by
  rintro ⟨coefficient, hcoefficient⟩
  have hone := hcoefficient 1 (by norm_num)
  have htwo := hcoefficient 2 (by norm_num)
  rw [principalWitness_symbol_dilate (by norm_num : (1 : ℤ) ≠ 0)] at hone
  rw [principalWitness_symbol_dilate (by norm_num : (2 : ℤ) ≠ 0)] at htwo
  norm_num at hone htwo
  rw [← hone] at htwo
  norm_num at htwo

#print axioms clockedPhysicalH2QuarticOccurrenceFace_eq_quadratic_add_principal
#print axioms closedTriadQuarticPrincipalSwing_cyclic_sum_eq_zero
#print axioms complexDot_normalizedPrincipalProjectedSourceAtom_eq_zero
#print axioms normalizedClockedPhysicalH2QuarticPrincipalSymbol_dilate
#print axioms principalWitness_exchange_reality_total_eq_three
#print axioms principalWitness_exchange_pair_dilate
#print axioms principalWitness_quarticAmplitude_exceeds_nat_orderThree_bound
#print axioms principalWitness_not_homogeneous_degree_three

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedQuarticPrincipalSymbol
