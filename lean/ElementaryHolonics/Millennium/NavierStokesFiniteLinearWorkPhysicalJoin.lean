import ElementaryHolonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionBaseEnergy

/-!
# Physical join for the finite linear work decomposition

**[proved-derived]**  This owner tests the work-side Fourier/physical join without suppressing
either aperture.  A common finite Fourier population has an exact Hermitian and symmetric-phase
Parseval law.  Applied to the strain population, this identifies the coefficient work with a
receiver-truncated physical reading.  Comparing that reading with the existing full-vorticity
direction receiver exposes the genuine output tail left at fixed depth.

The same aperture bookkeeping is used for transport: antisymmetry closes on an exchange-stable
interaction population, while every failure of such closure is retained as an explicit
boundary-shell population.  No terminal or uniform summability claim is introduced.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Exact finite Parseval on one common aperture -/

/-- Scalar finite Parseval with both populations carried by the same explicit aperture. -/
theorem integral_conj_finiteFourierSynthesis_mul_finiteFourierSynthesis
    (left right : SpatialFrequency → ℂ) (modes : Finset SpatialFrequency) :
    (∫ q : SpatialTorus,
      (starRingEnd ℂ) (finiteFourierSynthesis left modes q) *
        finiteFourierSynthesis right modes q) =
      ∑ frequency ∈ modes,
        (starRingEnd ℂ) (left frequency) * right frequency := by
  classical
  have hreorder : ∀ q : SpatialTorus,
      (starRingEnd ℂ) (finiteFourierSynthesis left modes q) *
          finiteFourierSynthesis right modes q =
        ∑ first ∈ modes, ∑ second ∈ modes,
          ((starRingEnd ℂ) (left second) * right first) *
            (UnitAddTorus.mFourier (-second) q *
              UnitAddTorus.mFourier first q) := by
    intro q
    simp only [finiteFourierSynthesis, ContinuousMap.coe_mk, smul_eq_mul,
      map_sum, map_mul, ← UnitAddTorus.mFourier_neg,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _hfirst
    apply Finset.sum_congr rfl
    intro second _hsecond
    ring
  have hintegrable : ∀ first ∈ modes, ∀ second ∈ modes,
      Integrable (fun q : SpatialTorus ↦
        ((starRingEnd ℂ) (left second) * right first) *
          (UnitAddTorus.mFourier (-second) q *
            UnitAddTorus.mFourier first q)) := by
    intro first _hfirst second _hsecond
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          ((starRingEnd ℂ) (left second) * right first) *
            (UnitAddTorus.mFourier (-second) q *
              UnitAddTorus.mFourier first q)
        continuous_toFun := by fun_prop }
  rw [integral_congr_ae (Filter.Eventually.of_forall hreorder)]
  rw [integral_finsetSum _ (fun first hfirst ↦
    integrable_finsetSum _ (hintegrable first hfirst))]
  apply Finset.sum_congr rfl
  intro first hfirst
  rw [integral_finsetSum _ (hintegrable first hfirst)]
  simp_rw [integral_const_mul, integral_mFourier_neg_mul_mFourier]
  simp [hfirst]

/-- Taking one vector component commutes with finite Fourier synthesis. -/
theorem finiteFourierSynthesis_apply_component
    (coefficient : SpatialFrequency → ComplexVector)
    (modes : Finset SpatialFrequency) (q : SpatialTorus) (component : Fin 3) :
    finiteFourierSynthesis coefficient modes q component =
      finiteFourierSynthesis
        (fun frequency ↦ coefficient frequency component) modes q := by
  unfold finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply]

/-- Vector Hermitian Parseval follows componentwise from the scalar common-aperture law. -/
theorem integral_complexVectorHermitianPairing_finiteFourierSynthesis
    (left right : SpatialFrequency → ComplexVector)
    (modes : Finset SpatialFrequency) :
    (∫ q : SpatialTorus,
      complexVectorHermitianPairing
        (finiteFourierSynthesis left modes q)
        (finiteFourierSynthesis right modes q)) =
      ∑ frequency ∈ modes,
        complexVectorHermitianPairing (left frequency) (right frequency) := by
  classical
  unfold complexVectorHermitianPairing
  rw [integral_finsetSum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro component _hcomponent
    simp_rw [finiteFourierSynthesis_apply_component]
    exact
      integral_conj_finiteFourierSynthesis_mul_finiteFourierSynthesis
        (fun frequency ↦ left frequency component)
        (fun frequency ↦ right frequency component) modes
  · intro component _hcomponent
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          (starRingEnd ℂ) (finiteFourierSynthesis left modes q component) *
            finiteFourierSynthesis right modes q component
        continuous_toFun := by fun_prop }

/-- Symmetric phase Parseval preserves the one-copy real work before any magnitude receiver. -/
theorem integral_complexVectorSymmetricPhasePairing_finiteFourierSynthesis
    (left right : SpatialFrequency → ComplexVector)
    (modes : Finset SpatialFrequency) :
    (∫ q : SpatialTorus,
      complexVectorSymmetricPhasePairing
        (finiteFourierSynthesis left modes q)
        (finiteFourierSynthesis right modes q)) =
      ∑ frequency ∈ modes,
        complexVectorSymmetricPhasePairing (left frequency) (right frequency) := by
  have hforward : Integrable (fun q : SpatialTorus ↦
      complexVectorHermitianPairing
        (finiteFourierSynthesis left modes q)
        (finiteFourierSynthesis right modes q)) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          complexVectorHermitianPairing
            (finiteFourierSynthesis left modes q)
            (finiteFourierSynthesis right modes q)
        continuous_toFun := by
          unfold complexVectorHermitianPairing
          fun_prop }
  have hreverse : Integrable (fun q : SpatialTorus ↦
      complexVectorHermitianPairing
        (finiteFourierSynthesis right modes q)
        (finiteFourierSynthesis left modes q)) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          complexVectorHermitianPairing
            (finiteFourierSynthesis right modes q)
            (finiteFourierSynthesis left modes q)
        continuous_toFun := by
          unfold complexVectorHermitianPairing
          fun_prop }
  unfold complexVectorSymmetricPhasePairing
  rw [integral_const_mul, integral_add hforward hreverse,
    integral_complexVectorHermitianPairing_finiteFourierSynthesis,
    integral_complexVectorHermitianPairing_finiteFourierSynthesis]
  calc
    (1 / 2 : ℂ) *
        ((∑ frequency ∈ modes,
            complexVectorHermitianPairing (left frequency) (right frequency)) +
          ∑ frequency ∈ modes,
            complexVectorHermitianPairing (right frequency) (left frequency)) =
      (1 / 2 : ℂ) *
        ∑ frequency ∈ modes,
          (complexVectorHermitianPairing (left frequency) (right frequency) +
            complexVectorHermitianPairing (right frequency) (left frequency)) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.mul_sum]

/-! ## The actual strain work reaches a receiver-truncated physical reading -/

/-- The finite interaction source on the strain side after the cumulative multiplier has crossed
to the velocity pin. -/
def finitePairCompatibleStrainFilteredSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) (k : SpatialFrequency) : ComplexVector :=
  finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
    (openPeriodicVorticityFourierMode solution t)
    (multiplierFilter
      (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
      (openPeriodicVelocityFourierMode solution t)) k

/-- The exact physical reading selected by the finite output receiver.  Both Fourier syntheses use
the one common depth aperture, while the complete interaction lineage remains inside the source
coefficients. -/
def finitePairCompatibleReceiverTruncatedStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) (q : SpatialTorus) : ℂ :=
  complexVectorSymmetricPhasePairing
    (finiteFourierSynthesis
      (openPeriodicVorticityFourierMode solution t)
      (smoothDyadicBandNativeAperture depth) q)
    (finiteFourierSynthesis
      (finitePairCompatibleStrainFilteredSource solution t depth radius)
      (smoothDyadicBandNativeAperture depth) q)

/-- **Exact actual Parseval join.**  The strain-filtered term in the finite nonlinear-work
decomposition is the torus integral of the receiver-truncated physical reading. -/
theorem finitePairCompatibleStrainFilteredStretchingWork_eq_integral_receiverTruncated
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleStrainFilteredStretchingWork solution t depth radius =
      ∫ q : SpatialTorus,
        finitePairCompatibleReceiverTruncatedStrainReading
          solution t depth radius q := by
  unfold finitePairCompatibleStrainFilteredStretchingWork
    finitePairCompatibleReceiverTruncatedStrainReading
    finitePairCompatibleStrainFilteredSource
  exact (integral_complexVectorSymmetricPhasePairing_finiteFourierSynthesis
    (openPeriodicVorticityFourierMode solution t)
    (fun k ↦
      finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
        (openPeriodicVorticityFourierMode solution t)
        (multiplierFilter
          (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
          (openPeriodicVelocityFourierMode solution t)) k)
    (smoothDyadicBandNativeAperture depth)).symm

/-- The genuine pointwise output tail between the full direction reading and the exact
receiver-truncated Parseval reading.  It is present even after the interaction aperture has
stabilized. -/
def finitePairCompatibleStrainOutputTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) (q : SpatialTorus) : ℂ :=
  finiteDepthDyadicHodgeStrainReading solution t q depth -
    finitePairCompatibleReceiverTruncatedStrainReading solution t depth radius q

/-- The old identification fibre is exactly the negative integral of the exposed output tail.
Thus pair-compatible interaction radius alone cannot erase the receiver-frequency mismatch. -/
theorem finitePairCompatibleStrainDirectionIdentificationDefect_eq_neg_integral_outputTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleStrainDirectionIdentificationDefect
        solution t depth radius =
      -(∫ q : SpatialTorus,
        finitePairCompatibleStrainOutputTail solution t depth radius q) := by
  have hvorticityContinuous : Continuous (fun q : SpatialTorus ↦
      openPeriodicComplexVorticityAt solution t q) := by
    exact (complexTorusVorticitySlice solution t).continuous
  have hfull : Integrable (fun q : SpatialTorus ↦
      finiteDepthDyadicHodgeStrainReading solution t q depth) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          finiteDepthDyadicHodgeStrainReading solution t q depth
        continuous_toFun := by
          unfold finiteDepthDyadicHodgeStrainReading
            complexStretchingReading symmetricComplexJacobianPart
            complexMatrixAction complexDot dotProduct Matrix.mulVec
            openPeriodicDyadicHodgeJacobianBand
          fun_prop }
  have htruncated : Integrable (fun q : SpatialTorus ↦
      finitePairCompatibleReceiverTruncatedStrainReading
        solution t depth radius q) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          finitePairCompatibleReceiverTruncatedStrainReading
            solution t depth radius q
        continuous_toFun := by
          unfold finitePairCompatibleReceiverTruncatedStrainReading
            complexVectorSymmetricPhasePairing complexVectorHermitianPairing
          fun_prop }
  unfold finitePairCompatibleStrainDirectionIdentificationDefect
    finitePairCompatibleStrainOutputTail
  rw [finitePairCompatibleStrainFilteredStretchingWork_eq_integral_receiverTruncated,
    integral_sub hfull htruncated]
  abel

/-- The identification fibre is controlled by the literal physical output-tail mass.  This is an
actual tail estimate, not a generated receipt; no claim that radius alone makes it vanish is
made. -/
theorem norm_finitePairCompatibleStrainDirectionIdentificationDefect_le_outputTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    ‖finitePairCompatibleStrainDirectionIdentificationDefect
        solution t depth radius‖ ≤
      ∫ q : SpatialTorus,
        ‖finitePairCompatibleStrainOutputTail solution t depth radius q‖ := by
  rw [finitePairCompatibleStrainDirectionIdentificationDefect_eq_neg_integral_outputTail,
    norm_neg]
  exact norm_integral_le_integral_norm _

/-! ## Exact transport exchange and its depth-uniform boundary estimate -/

/-- One exchanged transport face read with the real cumulative finite-depth multiplier. -/
def finiteDepthWeightedTransportExchange
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer
    (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
    triad advectingMode transportedMode receiverMode

/-- The exchanged transport cancels exactly when the two receiving pins see the same cumulative
weight; otherwise the surviving term is precisely the multiplier jump across that edge. -/
theorem finiteDepthWeightedTransportExchange_eq_multiplierJump
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    finiteDepthWeightedTransportExchange depth triad
        advectingMode transportedMode receiverMode =
      ((finiteDepthBoundaryWeight depth triad.transported : ℂ) -
        (finiteDepthBoundaryWeight depth triad.receiver : ℂ)) *
      triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode := by
  exact weightedExchangedTriadTransfer_eq_difference_mul
    (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
    triad advectingMode transportedMode receiverMode hdivergence

/-- Same-weight exchanged pins cancel exactly before any norm. -/
theorem finiteDepthWeightedTransportExchange_eq_zero_of_weight_eq
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hweight : finiteDepthBoundaryWeight depth triad.transported =
      finiteDepthBoundaryWeight depth triad.receiver) :
    finiteDepthWeightedTransportExchange depth triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [finiteDepthWeightedTransportExchange_eq_multiplierJump
    depth triad advectingMode transportedMode receiverMode hdivergence,
    hweight, sub_self, zero_mul]

/-- The multiplier jump is bounded by one independently of depth.  This is the explicit
boundary-shell estimate left when exact same-weight cancellation is unavailable. -/
theorem norm_finiteDepthWeightedTransportExchange_le_triadicEnergyFace
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    ‖finiteDepthWeightedTransportExchange depth triad
        advectingMode transportedMode receiverMode‖ ≤
      ‖triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode‖ := by
  rw [finiteDepthWeightedTransportExchange_eq_multiplierJump
    depth triad advectingMode transportedMode receiverMode hdivergence,
    norm_mul]
  have htransported :=
    smoothDyadicCumulativeBoundaryMultiplier_re_mem_unitInterval
      depth triad.transported
  have hreceiver :=
    smoothDyadicCumulativeBoundaryMultiplier_re_mem_unitInterval
      depth triad.receiver
  have hweightTransported :
      finiteDepthBoundaryWeight depth triad.transported =
        (smoothDyadicCumulativeBoundaryMultiplier depth triad.transported).re := by
    rw [← finiteDepthBoundaryWeight_complex]
    simp
  have hweightReceiver :
      finiteDepthBoundaryWeight depth triad.receiver =
        (smoothDyadicCumulativeBoundaryMultiplier depth triad.receiver).re := by
    rw [← finiteDepthBoundaryWeight_complex]
    simp
  have hjump :
      |finiteDepthBoundaryWeight depth triad.transported -
        finiteDepthBoundaryWeight depth triad.receiver| ≤ 1 := by
    rw [hweightTransported, hweightReceiver]
    rw [abs_le]
    constructor <;> linarith [htransported.1, htransported.2,
      hreceiver.1, hreceiver.2]
  have hcomplexJump :
      ‖((finiteDepthBoundaryWeight depth triad.transported : ℂ) -
        (finiteDepthBoundaryWeight depth triad.receiver : ℂ))‖ ≤ 1 := by
    simpa [← Complex.ofReal_sub, Complex.norm_real] using hjump
  exact mul_le_of_le_one_left (norm_nonneg _) hcomplexJump

/-- The actual finite exchanged-transport population on any declared collection of closed
triads.  The population is explicit because output-dependent pair-compatible apertures do not
silently supply exchange closure. -/
def finiteDepthOpenTransportExchangePopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ)
    (population : Finset AddressedClosedFourierTriad) : ℂ :=
  ∑ triad ∈ population,
    finiteDepthWeightedTransportExchange depth triad
      (openPeriodicVelocityFourierMode solution t triad.advecting)
      (openPeriodicVorticityFourierMode solution t triad.transported)
      (openPeriodicVorticityFourierMode solution t triad.receiver)

/-- **Depth-uniform finite boundary-shell estimate.**  Every actual exchanged population is
bounded by the corresponding unweighted triadic faces, independently of depth.  Same-weight
faces vanish by the preceding exact theorem; only multiplier-crossing faces remain. -/
theorem norm_finiteDepthOpenTransportExchangePopulation_le_boundaryFaces
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ)
    (population : Finset AddressedClosedFourierTriad) :
    ‖finiteDepthOpenTransportExchangePopulation solution t depth population‖ ≤
      ∑ triad ∈ population,
        ‖triadicEnergyFace triad.advecting triad.transported
          (openPeriodicVelocityFourierMode solution t triad.advecting)
          (openPeriodicVorticityFourierMode solution t triad.transported)
          (openPeriodicVorticityFourierMode solution t triad.receiver)‖ := by
  unfold finiteDepthOpenTransportExchangePopulation
  calc
    ‖∑ triad ∈ population,
        finiteDepthWeightedTransportExchange depth triad
          (openPeriodicVelocityFourierMode solution t triad.advecting)
          (openPeriodicVorticityFourierMode solution t triad.transported)
          (openPeriodicVorticityFourierMode solution t triad.receiver)‖ ≤
      ∑ triad ∈ population,
        ‖finiteDepthWeightedTransportExchange depth triad
          (openPeriodicVelocityFourierMode solution t triad.advecting)
          (openPeriodicVorticityFourierMode solution t triad.transported)
          (openPeriodicVorticityFourierMode solution t triad.receiver)‖ :=
        norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro triad _htriad
      exact norm_finiteDepthWeightedTransportExchange_le_triadicEnergyFace
        depth triad
        (openPeriodicVelocityFourierMode solution t triad.advecting)
        (openPeriodicVorticityFourierMode solution t triad.transported)
        (openPeriodicVorticityFourierMode solution t triad.receiver)
        (openPeriodicVelocityFourierMode_divergenceFree solution t triad.advecting)

section Audit

#print axioms integral_conj_finiteFourierSynthesis_mul_finiteFourierSynthesis
#print axioms integral_complexVectorHermitianPairing_finiteFourierSynthesis
#print axioms integral_complexVectorSymmetricPhasePairing_finiteFourierSynthesis
#print axioms finitePairCompatibleStrainFilteredStretchingWork_eq_integral_receiverTruncated
#print axioms finitePairCompatibleStrainDirectionIdentificationDefect_eq_neg_integral_outputTail
#print axioms norm_finitePairCompatibleStrainDirectionIdentificationDefect_le_outputTail
#print axioms finiteDepthWeightedTransportExchange_eq_multiplierJump
#print axioms finiteDepthWeightedTransportExchange_eq_zero_of_weight_eq
#print axioms norm_finiteDepthWeightedTransportExchange_le_triadicEnergyFace
#print axioms norm_finiteDepthOpenTransportExchangePopulation_le_boundaryFaces
#print axioms norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy
#print axioms norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence_kineticEnergy

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
