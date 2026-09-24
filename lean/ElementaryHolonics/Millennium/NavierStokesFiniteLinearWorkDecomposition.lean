import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
import ElementaryHolonics.Millennium.NavierStokesPairCompatibleApertureConvergence
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelCancellation

/-!
# Finite linear work: phase-first transport and stretching decomposition

**[proved-derived; formal-checked]**  The one-copy finite-depth boundary work is first retained as
one signed phase population.  Pair-compatible finite convolution then splits it into stretching
and transport.  Each part is passed through the same cumulative multiplier square: the stretching
side returns a strain-filtered term and its multiplier boundary, while the transport side returns
its multiplier boundary and the transported-filter cross-boundary term.

The finite convolution population converges to the actual finite-depth signed work.  Hence the
absolute-value receiver is applied only after the scale population has already telescoped to its
single boundary and after the four signed terms have interacted.  The geometric direction owner
is retained separately below as the exact pointwise receiver for the strain-filtered population.
No depth limit, time-integrability assertion, scale summability, or terminal conclusion is made.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The real cumulative multiplier and phase algebra -/

/-- The real chart underlying the existing complex cumulative boundary multiplier. -/
def finiteDepthBoundaryWeight (depth : ℕ) (frequency : SpatialFrequency) : ℝ :=
  tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency -
    tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency

theorem finiteDepthBoundaryWeight_complex
    (depth : ℕ) (frequency : SpatialFrequency) :
    (finiteDepthBoundaryWeight depth frequency : ℂ) =
      smoothDyadicCumulativeBoundaryMultiplier depth frequency := by
  rw [finiteDepthBoundaryWeight, smoothDyadicCumulativeBoundaryMultiplier,
    Complex.ofReal_sub]

theorem complexVectorSymmetricPhasePairing_add_right_public
    (left first second : ComplexVector) :
    complexVectorSymmetricPhasePairing left (first + second) =
      complexVectorSymmetricPhasePairing left first +
        complexVectorSymmetricPhasePairing left second := by
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem complexVectorSymmetricPhasePairing_sub_right
    (left first second : ComplexVector) :
    complexVectorSymmetricPhasePairing left (first - second) =
      complexVectorSymmetricPhasePairing left first -
        complexVectorSymmetricPhasePairing left second := by
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  simp only [Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

theorem continuous_complexVectorSymmetricPhasePairing_right
    (left : ComplexVector) :
    Continuous (fun right : ComplexVector ↦
      complexVectorSymmetricPhasePairing left right) := by
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  fun_prop

/-! ## One pair-compatible finite interaction population -/

/-- The finite projected nonlinear work whose output population is already the common native
depth aperture, while every output uses its own reflection-closed interaction aperture. -/
def finitePairCompatibleBoundaryNonlinearWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth k : ℂ) *
      complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t k)
        (finiteOpenVorticityNonlinearCoefficient solution t
          (pairCompatibleFrequencyAperture k radius) k)

/-- The receiver-filtered finite stretching work. -/
def finitePairCompatibleReceiverStretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth k : ℂ) *
      complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t k)
        (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
          (openPeriodicVorticityFourierMode solution t)
          (openPeriodicVelocityFourierMode solution t) k)

/-- The receiver-filtered finite vorticity-transport work. -/
def finitePairCompatibleReceiverTransportWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth k : ℂ) *
      complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t k)
        (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
          (openPeriodicVelocityFourierMode solution t)
          (openPeriodicVorticityFourierMode solution t) k)

/-- Curl incidence splits the finite projected source before any norm is applied. -/
theorem finitePairCompatibleBoundaryNonlinearWork_eq_stretching_sub_transport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleBoundaryNonlinearWork solution t depth radius =
      finitePairCompatibleReceiverStretchingWork solution t depth radius -
        finitePairCompatibleReceiverTransportWork solution t depth radius := by
  classical
  unfold finitePairCompatibleBoundaryNonlinearWork
    finitePairCompatibleReceiverStretchingWork
    finitePairCompatibleReceiverTransportWork
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
    solution t (pairCompatibleFrequencyAperture k radius) k
      (pairCompatibleFrequencyAperture_isTransportPaired k radius),
    complexVectorSymmetricPhasePairing_sub_right]
  ring

/-! ## Multiplier boundaries and the retained transport cross-boundary -/

/-- Stretching after the cumulative multiplier has crossed to the velocity/strain pin. -/
def finitePairCompatibleStrainFilteredStretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    complexVectorSymmetricPhasePairing
      (openPeriodicVorticityFourierMode solution t k)
      (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
        (openPeriodicVorticityFourierMode solution t)
        (multiplierFilter (fun frequency ↦
          (finiteDepthBoundaryWeight depth frequency : ℂ))
          (openPeriodicVelocityFourierMode solution t)) k)

/-- The stretching multiplier boundary, with its exact multiplier-difference expansion supplied
by `finiteMultiplierFlowCommutatorCoefficient_eq_sum_difference`. -/
def finitePairCompatibleStretchingMultiplierBoundaryWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    complexVectorSymmetricPhasePairing
      (openPeriodicVorticityFourierMode solution t k)
      (finiteMultiplierFlowCommutatorCoefficient
        (pairCompatibleFrequencyAperture k radius)
        (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
        (openPeriodicVorticityFourierMode solution t)
        (openPeriodicVelocityFourierMode solution t) k)

/-- The vorticity-transport multiplier boundary. -/
def finitePairCompatibleTransportMultiplierBoundaryWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    complexVectorSymmetricPhasePairing
      (openPeriodicVorticityFourierMode solution t k)
      (finiteMultiplierFlowCommutatorCoefficient
        (pairCompatibleFrequencyAperture k radius)
        (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
        (openPeriodicVelocityFourierMode solution t)
        (openPeriodicVorticityFourierMode solution t) k)

/-- The finite transported-filter term.  This is the concrete cross-boundary endpoint left when
the output-dependent pair-compatible apertures prevent a global exchange of transported and
receiving pins. -/
def finitePairCompatibleTransportCrossBoundaryWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    complexVectorSymmetricPhasePairing
      (openPeriodicVorticityFourierMode solution t k)
      (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
        (openPeriodicVelocityFourierMode solution t)
        (multiplierFilter (fun frequency ↦
          (finiteDepthBoundaryWeight depth frequency : ℂ))
          (openPeriodicVorticityFourierMode solution t)) k)

theorem finitePairCompatibleReceiverStretchingWork_eq_filtered_add_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleReceiverStretchingWork solution t depth radius =
      finitePairCompatibleStrainFilteredStretchingWork solution t depth radius +
        finitePairCompatibleStretchingMultiplierBoundaryWork
          solution t depth radius := by
  classical
  unfold finitePairCompatibleReceiverStretchingWork
    finitePairCompatibleStrainFilteredStretchingWork
    finitePairCompatibleStretchingMultiplierBoundaryWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← complexVectorSymmetricPhasePairing_real_smul_right]
  unfold finiteMultiplierFlowCommutatorCoefficient multiplierFilter
  rw [← complexVectorSymmetricPhasePairing_add_right_public]
  congr 1
  abel

theorem finitePairCompatibleReceiverTransportWork_eq_crossBoundary_add_boundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleReceiverTransportWork solution t depth radius =
      finitePairCompatibleTransportCrossBoundaryWork solution t depth radius +
        finitePairCompatibleTransportMultiplierBoundaryWork solution t depth radius := by
  classical
  unfold finitePairCompatibleReceiverTransportWork
    finitePairCompatibleTransportCrossBoundaryWork
    finitePairCompatibleTransportMultiplierBoundaryWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← complexVectorSymmetricPhasePairing_real_smul_right]
  unfold finiteMultiplierFlowCommutatorCoefficient multiplierFilter
  rw [← complexVectorSymmetricPhasePairing_add_right_public]
  congr 1
  abel

/-- **Exact finite phase decomposition.**  The four returned populations are formed before real
projection or magnitude: strain-filtered stretching, the stretching multiplier boundary, the
transport cross-boundary, and the transport multiplier boundary. -/
theorem finitePairCompatibleBoundaryNonlinearWork_eq_direction_plus_boundaries
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleBoundaryNonlinearWork solution t depth radius =
      finitePairCompatibleStrainFilteredStretchingWork solution t depth radius +
        finitePairCompatibleStretchingMultiplierBoundaryWork solution t depth radius -
      finitePairCompatibleTransportCrossBoundaryWork solution t depth radius -
        finitePairCompatibleTransportMultiplierBoundaryWork solution t depth radius := by
  rw [finitePairCompatibleBoundaryNonlinearWork_eq_stretching_sub_transport,
    finitePairCompatibleReceiverStretchingWork_eq_filtered_add_boundary,
    finitePairCompatibleReceiverTransportWork_eq_crossBoundary_add_boundary]
  abel

/-! ## Passage to the actual finite-depth boundary work -/

theorem tendsto_finitePairCompatibleBoundaryNonlinearWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleBoundaryNonlinearWork solution t depth radius)
      atTop
      (nhds (linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t))) := by
  classical
  unfold finitePairCompatibleBoundaryNonlinearWork
    linearMultiplierCoefficientWork
  apply tendsto_finsetSum
  intro k _hk
  have hsource :=
    tendsto_finiteOpenVorticityNonlinearCoefficient_pairCompatible solution t k
  have hpair :=
    (continuous_complexVectorSymmetricPhasePairing_right
      (openPeriodicVorticityFourierMode solution t k)).continuousAt.tendsto.comp hsource
  have hpair' : Tendsto
      (fun radius : ℕ ↦
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t k)
          (finiteOpenVorticityNonlinearCoefficient solution t
            (pairCompatibleFrequencyAperture k radius) k))
      atTop
      (nhds (complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t k)
        (vorticityNonlinearMode solution t k))) := by
    change Tendsto
      ((fun right : ComplexVector ↦
          complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t k) right) ∘
        (fun radius : ℕ ↦
          finiteOpenVorticityNonlinearCoefficient solution t
            (pairCompatibleFrequencyAperture k radius) k))
      atTop
      (nhds (complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t k)
        (vorticityNonlinearMode solution t k)))
    exact hpair
  have hweighted : Tendsto
      (fun radius : ℕ ↦
        (finiteDepthBoundaryWeight depth k : ℂ) *
          complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t k)
            (finiteOpenVorticityNonlinearCoefficient solution t
              (pairCompatibleFrequencyAperture k radius) k))
      atTop
      (nhds ((finiteDepthBoundaryWeight depth k : ℂ) *
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t k)
          (vorticityNonlinearMode solution t k))) :=
    tendsto_const_nhds.mul hpair'
  simpa only [finiteDepthBoundaryWeight_complex] using hweighted

/-- The actual finite scale sum is the limit of the single phase-sensitive four-term
decomposition.  In particular no scalewise magnitude has entered the passage. -/
theorem tendsto_finitePairCompatibleBoundaryNonlinearWork_re_to_actualScaleSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦
        (finitePairCompatibleBoundaryNonlinearWork solution t depth radius).re)
      atTop
      (nhds (∑ scale ∈ Finset.range depth,
        openSmoothDyadicLinearBandActualSignedWorkRate solution t scale)) := by
  have hlimit := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_finitePairCompatibleBoundaryNonlinearWork solution t depth)
  rw [sum_openSmoothDyadicLinearBandActualSignedWorkRate_eq_lowPass_boundary]
  exact hlimit

/-- The real receiver of the finite decomposition is still one signed four-term population. -/
theorem finitePairCompatibleBoundaryNonlinearWork_re_eq_direction_plus_boundaries
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    (finitePairCompatibleBoundaryNonlinearWork solution t depth radius).re =
      (finitePairCompatibleStrainFilteredStretchingWork
        solution t depth radius).re +
      (finitePairCompatibleStretchingMultiplierBoundaryWork
        solution t depth radius).re -
      (finitePairCompatibleTransportCrossBoundaryWork
        solution t depth radius).re -
      (finitePairCompatibleTransportMultiplierBoundaryWork
        solution t depth radius).re := by
  exact congrArg Complex.re
    (finitePairCompatibleBoundaryNonlinearWork_eq_direction_plus_boundaries
      solution t depth radius)

/-- The magnitude receiver for the four signed terms, formed only after their phase-sensitive
interaction has returned the finite-depth boundary. -/
def finitePairCompatibleBoundaryWorkMajorant
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℝ :=
  |(finitePairCompatibleStrainFilteredStretchingWork
      solution t depth radius).re| +
    |(finitePairCompatibleStretchingMultiplierBoundaryWork
      solution t depth radius).re| +
    |(finitePairCompatibleTransportCrossBoundaryWork
      solution t depth radius).re| +
    |(finitePairCompatibleTransportMultiplierBoundaryWork
      solution t depth radius).re|

private theorem abs_actual_le_four_term_majorant_add
    (actual approximate strain stretchBoundary crossBoundary transportBoundary
      tolerance : ℝ)
    (happroximate :
      approximate = strain + stretchBoundary - crossBoundary - transportBoundary)
    (herror : dist approximate actual < tolerance) :
    |actual| ≤
      |strain| + |stretchBoundary| + |crossBoundary| + |transportBoundary| +
        tolerance := by
  have happAbs :
      |approximate| ≤
        |strain| + |stretchBoundary| + |crossBoundary| + |transportBoundary| := by
    rw [happroximate]
    calc
      |strain + stretchBoundary - crossBoundary - transportBoundary| ≤
          |strain + stretchBoundary - crossBoundary| + |transportBoundary| :=
        abs_sub _ _
      _ ≤ (|strain + stretchBoundary| + |crossBoundary|) +
          |transportBoundary| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (|strain| + |stretchBoundary| + |crossBoundary|) +
          |transportBoundary| := by
        gcongr
        exact abs_add_le _ _
  have herr : |actual - approximate| < tolerance := by
    simpa only [Real.dist_eq, abs_sub_comm] using herror
  have hactual : |actual| ≤ |approximate| + |actual - approximate| := by
    calc
      |actual| = |approximate + (actual - approximate)| := by
        congr 1
        ring
      _ ≤ |approximate| + |actual - approximate| :=
        abs_add_le (approximate : ℝ) (actual - approximate)
  exact hactual.trans ((add_le_add happAbs herr.le).trans_eq (by ring))

/-- **Phase-first finite-depth inequality.**  For every positive tolerance, sufficiently large
pair-compatible apertures bound the absolute value of the *already summed* actual work by the
four returned populations.  No absolute value is taken scale by scale or interaction by
interaction. -/
theorem eventually_abs_actualFiniteScaleWork_le_direction_plus_boundaries
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∀ᶠ radius : ℕ in atTop,
      |∑ scale ∈ Finset.range depth,
          openSmoothDyadicLinearBandActualSignedWorkRate solution t scale| ≤
        finitePairCompatibleBoundaryWorkMajorant solution t depth radius + tolerance := by
  let actual : ℝ := ∑ scale ∈ Finset.range depth,
    openSmoothDyadicLinearBandActualSignedWorkRate solution t scale
  have hlimit :=
    tendsto_finitePairCompatibleBoundaryNonlinearWork_re_to_actualScaleSum
      solution t depth
  have heventually : ∀ᶠ radius : ℕ in atTop,
      dist (finitePairCompatibleBoundaryNonlinearWork
        solution t depth radius).re actual < tolerance :=
    (Metric.tendsto_nhds.1 hlimit) tolerance htolerance
  filter_upwards [heventually] with radius hradius
  apply abs_actual_le_four_term_majorant_add
    actual
    (finitePairCompatibleBoundaryNonlinearWork solution t depth radius).re
    (finitePairCompatibleStrainFilteredStretchingWork solution t depth radius).re
    (finitePairCompatibleStretchingMultiplierBoundaryWork solution t depth radius).re
    (finitePairCompatibleTransportCrossBoundaryWork solution t depth radius).re
    (finitePairCompatibleTransportMultiplierBoundaryWork solution t depth radius).re
    tolerance
  · exact finitePairCompatibleBoundaryNonlinearWork_re_eq_direction_plus_boundaries
      solution t depth radius
  · exact hradius

/-! ## The geometric receiver retained by the strain-filtered term -/

/-- The signed pointwise finite-depth strain reading; scales still interact before a norm. -/
def finiteDepthDyadicHodgeStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (depth : ℕ) : ℂ :=
  ∑ scale ∈ Finset.range depth,
    complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
      (symmetricComplexJacobianPart
        (openPeriodicDyadicHodgeJacobianBand solution t scale q))

/-- The exact unresolved physical/Fourier identification fibre.  Its left endpoint is the
strain-filtered finite convolution occurring in the actual work decomposition; its right endpoint
is the torus integral of the existing finite-depth physical Hodge strain reading.  A future
Parseval/reindexing passage must show that the appropriate cofinal form of this fibre vanishes;
the present owner does not assume that conclusion. -/
def finitePairCompatibleStrainDirectionIdentificationDefect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℂ :=
  finitePairCompatibleStrainFilteredStretchingWork solution t depth radius -
    ∫ q : SpatialTorus, finiteDepthDyadicHodgeStrainReading solution t q depth

/-- **Exact shortest obstruction identity.**  The coefficient-side strain population reaches the
existing physical direction receiver plus one explicit reconstruction fibre.  This records the
missing equality without installing it as a premise or concealing it in a terminal estimate. -/
theorem finitePairCompatibleStrainFilteredStretchingWork_eq_directionIntegral_add_defect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    finitePairCompatibleStrainFilteredStretchingWork solution t depth radius =
      (∫ q : SpatialTorus,
        finiteDepthDyadicHodgeStrainReading solution t q depth) +
      finitePairCompatibleStrainDirectionIdentificationDefect
        solution t depth radius := by
  unfold finitePairCompatibleStrainDirectionIdentificationDefect
  abel

/-- Before using the nonzero direction chart, the exact direction-remainder mass already bounds
the signed finite-depth strain population. -/
theorem norm_finiteDepthDyadicHodgeStrainReading_le_directionCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    ‖finiteDepthDyadicHodgeStrainReading solution t q depth‖ ≤
      ∑ scale ∈ Finset.range depth,
        openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale := by
  unfold finiteDepthDyadicHodgeStrainReading
  calc
    ‖∑ scale ∈ Finset.range depth,
        complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      ∑ scale ∈ Finset.range depth,
        ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ :=
        norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro scale _hscale
      exact norm_openPeriodicDyadicHodgeStrainReading_le_spatialDirectionCoherenceMass
        solution t q scale

/-- On the nonzero vorticity chart, the same signed finite-depth population is controlled by the
spatial cross-coherence receiver. -/
theorem norm_finiteDepthDyadicHodgeStrainReading_le_spatialCrossCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (depth : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖finiteDepthDyadicHodgeStrainReading solution t q depth‖ ≤
      ∑ scale ∈ Finset.range depth,
        ( (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2) := by
  unfold finiteDepthDyadicHodgeStrainReading
  calc
    ‖∑ scale ∈ Finset.range depth,
        complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      ∑ scale ∈ Finset.range depth,
        ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ :=
        norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro scale _hscale
      exact norm_openPeriodicDyadicHodgeStrainReading_le_spatialCrossCoherenceMass
        solution t q scale hvorticity

section Audit

#print axioms finitePairCompatibleBoundaryNonlinearWork_eq_stretching_sub_transport
#print axioms finitePairCompatibleReceiverStretchingWork_eq_filtered_add_boundary
#print axioms finitePairCompatibleReceiverTransportWork_eq_crossBoundary_add_boundary
#print axioms finitePairCompatibleBoundaryNonlinearWork_eq_direction_plus_boundaries
#print axioms tendsto_finitePairCompatibleBoundaryNonlinearWork_re_to_actualScaleSum
#print axioms eventually_abs_actualFiniteScaleWork_le_direction_plus_boundaries
#print axioms finitePairCompatibleStrainFilteredStretchingWork_eq_directionIntegral_add_defect
#print axioms norm_finiteDepthDyadicHodgeStrainReading_le_directionCoherenceMass
#print axioms norm_finiteDepthDyadicHodgeStrainReading_le_spatialCrossCoherenceMass

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
