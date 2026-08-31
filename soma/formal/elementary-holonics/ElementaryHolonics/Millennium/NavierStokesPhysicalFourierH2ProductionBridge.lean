import ElementaryHolonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3

/-!
# The physical/Fourier H2 production bridge

**[proved-derived; formal-checked]** The derivative-weighted curl test is not an unrelated
vorticity receiver.  At every Fourier mode its Hermitian pairing is exactly the homogeneous
order-one-plus-order-two Leray work: the curl multiplier contributes one Stokes factor and the
test contributes the remaining inhomogeneous factor.  This file establishes that modewise chart
for the actual sharp nonlinear source, then carries it through every finite aperture and the
complete coefficient population.

The final physical incidence is kept explicit and closed here.  Order-one and order-two Parseval,
the two periodic top-transport cancellations, and the finite word reindexings compose to identify
the complete projected coefficient work with the already-founded coordinate commutator current
`coordinateH2NonlinearProductionCurrent`.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

set_option maxHeartbeats 2400000

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## One-mode Hodge work identity -/

/-- A single Fourier mode satisfies the divergence-free incidence required by the Hodge work
chart.  The zero mode is included and carries zero curl work. -/
def IsDivergenceFreeMode (frequency : SpatialFrequency) (mode : ComplexVector) : Prop :=
  complexDot (complexFrequencyVector frequency) mode = 0

/-- The homogeneous coordinate `H2` work at one projected source mode.  The Stokes factor is the
sum of all first ordered derivative faces; its square is the sum of all ordered second derivative
faces.  The minus sign is the Navier--Stokes source orientation. -/
def homogeneousCoordinateH2ModeWork
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector) : ℝ :=
  -(torusStokesEigenvalue frequency + torusStokesEigenvalue frequency ^ 2) *
    sourceTestProductionReading velocityMode sourceMode

/-- Complex Hermitian work before the real production receiver is applied. -/
def complexHermitianWork (left right : ComplexVector) : ℂ :=
  ∑ component : Fin 3, (starRingEnd ℂ) (left component) * right component

/-- The derivative scale is recovered as an addressed curl receiver rather than introduced as a
bare transcendental scalar.  The two basis incidences and the returned third component determine
the unit-torus calibration. -/
def unitTorusCurlScale : ℂ :=
  frequencyCurlMultiplier (![1, 0, 0] : SpatialFrequency)
    (![0, 1, 0] : ComplexVector) 2

theorem frequencyCurlMultiplier_eq_unitTorusCurlScale_smul
    (frequency : SpatialFrequency) (mode : ComplexVector) :
    frequencyCurlMultiplier frequency mode =
      unitTorusCurlScale • complexCross (complexFrequencyVector frequency) mode := by
  ext component
  fin_cases component <;>
    simp [unitTorusCurlScale, frequencyCurlMultiplier, complexCross, crossProduct,
      complexFrequencyVector]

theorem unitTorusCurlScale_normSquare_frequencySquared
    (frequency : SpatialFrequency) :
    (starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale *
        (frequencySquared frequency : ℂ) =
      (torusStokesEigenvalue frequency : ℂ) := by
  simp [unitTorusCurlScale, frequencyCurlMultiplier, complexCross, crossProduct,
    complexFrequencyVector, torusStokesEigenvalue]
  rw [map_ofNat (starRingEnd ℂ) 2]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The same constraint-derived calibration is the multiplier for one addressed coordinate
derivative. -/
def addressedCoordinateMultiplier
    (coordinate : Fin 3) (frequency : SpatialFrequency) : ℂ :=
  unitTorusCurlScale * (frequency coordinate : ℂ)

/-- Fourier coefficients of a genuine coordinate derivative use the addressed calibration. -/
theorem actualJacobianFourierMode_eq_addressedCoordinateMultiplier
    (field : InitialVelocity) (hfield : ContDiff ℝ 1 field)
    (hperiodic : IsOnePeriodic field) (frequency : SpatialFrequency)
    (component coordinate : Fin 3) :
    actualJacobianFourierMode field hfield hperiodic frequency component coordinate =
      addressedCoordinateMultiplier coordinate frequency *
        vectorSpatialFourierCoeff field hfield.continuous hperiodic frequency component := by
  rw [actualJacobianFourierMode_eq_multiplier]
  congr 1
  simp [addressedCoordinateMultiplier, unitTorusCurlScale,
    frequencyCurlMultiplier, complexCross, crossProduct, complexFrequencyVector]

/-- The sum of the three addressed derivative scale squares is the Stokes eigenvalue. -/
theorem sum_addressedCoordinateMultiplier_star_mul
    (frequency : SpatialFrequency) :
    (∑ coordinate : Fin 3,
      (starRingEnd ℂ) (addressedCoordinateMultiplier coordinate frequency) *
        addressedCoordinateMultiplier coordinate frequency) =
      (torusStokesEigenvalue frequency : ℂ) := by
  unfold addressedCoordinateMultiplier
  simp only [map_mul]
  have hstarInt : ∀ coordinate : Fin 3,
      (starRingEnd ℂ) (frequency coordinate : ℂ) =
        (frequency coordinate : ℂ) := by
    intro coordinate
    simp
  have hsum :
      (∑ coordinate : Fin 3,
        ((frequency coordinate : ℂ) * (frequency coordinate : ℂ))) =
        (frequencySquared frequency : ℂ) := by
    simp [frequencySquared, Fin.sum_univ_succ, pow_two]
  calc
    (∑ coordinate : Fin 3,
        (starRingEnd ℂ) unitTorusCurlScale *
            (starRingEnd ℂ) (frequency coordinate : ℂ) *
          (unitTorusCurlScale * (frequency coordinate : ℂ))) =
      ((starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale) *
        (∑ coordinate : Fin 3,
          (frequency coordinate : ℂ) * (frequency coordinate : ℂ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro coordinate _hcoordinate
            rw [hstarInt coordinate]
            ring
    _ = ((starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale) *
        (frequencySquared frequency : ℂ) := by rw [hsum]
    _ = (torusStokesEigenvalue frequency : ℂ) :=
      unitTorusCurlScale_normSquare_frequencySquared frequency

theorem sourceTestProductionReading_eq_re_complexHermitianWork
    (left right : ComplexVector) :
    sourceTestProductionReading left right = (complexHermitianWork left right).re :=
  rfl

private theorem complexHermitianWork_frequencyCurlMultiplier
    (frequency : SpatialFrequency) (left right : ComplexVector)
    (_hleft : IsDivergenceFreeMode frequency left)
    (hright : IsDivergenceFreeMode frequency right) :
    complexHermitianWork
        (frequencyCurlMultiplier frequency left)
        (frequencyCurlMultiplier frequency right) =
      (torusStokesEigenvalue frequency : ℂ) * complexHermitianWork left right := by
  let leftStar : ComplexVector := fun component ↦ (starRingEnd ℂ) (left component)
  have hcross := cross_dot_cross
    (complexFrequencyVector frequency) leftStar
    (complexFrequencyVector frequency) right
  have hself :
      dotProduct (complexFrequencyVector frequency)
          (complexFrequencyVector frequency) = (frequencySquared frequency : ℂ) := by
    simpa [complexDot] using complexDot_frequency_self frequency
  have hrightRaw :
      dotProduct (complexFrequencyVector frequency) right = 0 := by
    simpa [IsDivergenceFreeMode, complexDot] using hright
  rw [hself, hrightRaw] at hcross
  simp only [zero_mul, sub_zero] at hcross
  have hstarCross : ∀ component : Fin 3,
      (starRingEnd ℂ)
          (complexCross (complexFrequencyVector frequency) left component) =
        complexCross (complexFrequencyVector frequency) leftStar component := by
    intro component
    fin_cases component <;>
      simp [complexCross, crossProduct, complexFrequencyVector, leftStar]
  have hcross' :
      (∑ component : Fin 3,
        (starRingEnd ℂ)
            (complexCross (complexFrequencyVector frequency) left component) *
          complexCross (complexFrequencyVector frequency) right component) =
        (frequencySquared frequency : ℂ) * complexHermitianWork left right := by
    simp_rw [hstarCross]
    simpa [complexCross, complexDot, dotProduct, leftStar, complexHermitianWork,
      complexFrequencyVector, Fin.sum_univ_succ, add_assoc, mul_comm] using hcross
  unfold complexHermitianWork at hcross'
  rw [frequencyCurlMultiplier_eq_unitTorusCurlScale_smul,
    frequencyCurlMultiplier_eq_unitTorusCurlScale_smul]
  unfold complexHermitianWork
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    (∑ component : Fin 3,
        (starRingEnd ℂ) unitTorusCurlScale *
            (starRingEnd ℂ)
              (complexCross (complexFrequencyVector frequency) left component) *
          (unitTorusCurlScale *
            complexCross (complexFrequencyVector frequency) right component)) =
      ((starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale) *
        (∑ component : Fin 3,
          (starRingEnd ℂ)
              (complexCross (complexFrequencyVector frequency) left component) *
            complexCross (complexFrequencyVector frequency) right component) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro component _hcomponent
        ring
    _ = ((starRingEnd ℂ) unitTorusCurlScale * unitTorusCurlScale) *
        ((frequencySquared frequency : ℂ) *
          (∑ component : Fin 3,
            (starRingEnd ℂ) (left component) * right component)) := by
      rw [hcross']
    _ = (torusStokesEigenvalue frequency : ℂ) *
        ∑ component : Fin 3, (starRingEnd ℂ) (left component) * right component := by
      rw [← unitTorusCurlScale_normSquare_frequencySquared frequency]
      ring

/-- Hermitian curl--curl work is the Stokes-weighted Hermitian vector work on the transverse
fibre.  This is the exact three-dimensional Hodge identity before any summation or norm. -/
theorem sourceTestProductionReading_frequencyCurlMultiplier
    (frequency : SpatialFrequency) (left right : ComplexVector)
    (hleft : IsDivergenceFreeMode frequency left)
    (hright : IsDivergenceFreeMode frequency right) :
    sourceTestProductionReading
        (frequencyCurlMultiplier frequency left)
        (frequencyCurlMultiplier frequency right) =
      torusStokesEigenvalue frequency * sourceTestProductionReading left right := by
  rw [sourceTestProductionReading_eq_re_complexHermitianWork,
    complexHermitianWork_frequencyCurlMultiplier frequency left right hleft hright]
  simp [sourceTestProductionReading_eq_re_complexHermitianWork]

theorem sourceTestProductionReading_real_smul_test
    (scale : ℝ) (test source : ComplexVector) :
    sourceTestProductionReading (((scale : ℂ)) • test) source =
      scale * sourceTestProductionReading test source := by
  unfold sourceTestProductionReading
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  have hfactor :
      (∑ component : Fin 3,
        (scale : ℂ) * (starRingEnd ℂ) (test component) * source component) =
        (scale : ℂ) *
          ∑ component : Fin 3,
            (starRingEnd ℂ) (test component) * source component := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro component _hcomponent
    ring
  rw [hfactor]
  simp

theorem sourceTestProductionReading_neg_source
    (test source : ComplexVector) :
    sourceTestProductionReading test (-source) =
      -sourceTestProductionReading test source := by
  simp [sourceTestProductionReading, ← Finset.sum_neg_distrib]

/-- Leray projection is invisible to the Hermitian energy receiver whenever the test mode is
transverse.  This is the exact complex self-adjoint incidence needed to replace the projected
sharp source by the literal advective coefficient in Parseval. -/
theorem sourceTestProductionReading_lerayProjectMode
    (frequency : SpatialFrequency) (test source : ComplexVector)
    (htest : IsDivergenceFreeMode frequency test) :
    sourceTestProductionReading test (lerayProjectMode frequency source) =
      sourceTestProductionReading test source := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [lerayProjectMode_zero]
  · rw [lerayProjectMode, if_neg hfrequency]
    unfold IsDivergenceFreeMode at htest
    unfold sourceTestProductionReading
    have hconjTransverse :
        (∑ component : Fin 3,
          (starRingEnd ℂ) (test component) *
            complexFrequencyVector frequency component) = 0 := by
      have hstar := congrArg (starRingEnd ℂ) htest
      simp only [map_zero] at hstar
      simpa [complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_succ,
        mul_comm] using hstar
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    rw [show
      (∑ component : Fin 3,
        (starRingEnd ℂ) (test component) *
          ((complexDot (complexFrequencyVector frequency) source /
              (frequencySquared frequency : ℂ)) *
            complexFrequencyVector frequency component)) = 0 by
        calc
          _ = (complexDot (complexFrequencyVector frequency) source /
                (frequencySquared frequency : ℂ)) *
              (∑ component : Fin 3,
                (starRingEnd ℂ) (test component) *
                  complexFrequencyVector frequency component) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro component _hcomponent
                ring
          _ = 0 := by rw [hconjTransverse, mul_zero]]
    simp

/-- First-derivative projected work at one mode. -/
def projectedCoordinateH1ModeWork
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector) : ℝ :=
  -torusStokesEigenvalue frequency *
    sourceTestProductionReading velocityMode sourceMode

/-- Ordered second-derivative projected work at one mode. -/
def projectedCoordinateH2ModeWork
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector) : ℝ :=
  -(torusStokesEigenvalue frequency ^ 2) *
    sourceTestProductionReading velocityMode sourceMode

theorem homogeneousCoordinateH2ModeWork_eq_orderOne_add_orderTwo
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector) :
    homogeneousCoordinateH2ModeWork frequency velocityMode sourceMode =
      projectedCoordinateH1ModeWork frequency velocityMode sourceMode +
        projectedCoordinateH2ModeWork frequency velocityMode sourceMode := by
  unfold homogeneousCoordinateH2ModeWork projectedCoordinateH1ModeWork
    projectedCoordinateH2ModeWork
  ring

/-- The derivative-weighted negative curl-source reading is exactly the sum of the order-one and
order-two projected coefficient works.  This is the sign-sensitive one-mode bridge used by the
finite aperture and cofinal passages below. -/
theorem derivativeWeighted_negCurlReading_eq_orderOne_add_orderTwo
    (frequency : SpatialFrequency) (velocityMode sourceMode : ComplexVector)
    (hvelocity : IsDivergenceFreeMode frequency velocityMode)
    (hsource : IsDivergenceFreeMode frequency sourceMode) :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) •
          frequencyCurlMultiplier frequency velocityMode)
        (-frequencyCurlMultiplier frequency sourceMode) =
      projectedCoordinateH1ModeWork frequency velocityMode sourceMode +
        projectedCoordinateH2ModeWork frequency velocityMode sourceMode := by
  rw [sourceTestProductionReading_real_smul_test,
    sourceTestProductionReading_neg_source,
    sourceTestProductionReading_frequencyCurlMultiplier
      frequency velocityMode sourceMode hvelocity hsource]
  unfold projectedCoordinateH1ModeWork projectedCoordinateH2ModeWork
  ring

/-! ## The actual open sharp source at one mode -/

theorem openPeriodicVelocityMode_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    IsDivergenceFreeMode frequency
      (openPeriodicVelocityFourierMode solution t frequency) := by
  unfold IsDivergenceFreeMode
  exact complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (fun x ↦ velocity x t.1)
    ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le (by norm_num))
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩)
    frequency

theorem openSharpSourceMode_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    IsDivergenceFreeMode frequency
      (unweightedSharpNonlinearSourceCoefficient
        (openVelocityWeightedH3State solution t) frequency) := by
  unfold IsDivergenceFreeMode
  rw [unweightedSharpNonlinearSourceCoefficient_open_eq]
  exact complexDot_lerayProjectMode_eq_zero frequency _

/-- The actual sharp source is literally the Leray projection of the Fourier coefficient of
`Du(u)`, with no finite convolution aperture. -/
theorem unweightedSharpNonlinearSourceCoefficient_eq_leray_openActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    unweightedSharpNonlinearSourceCoefficient
        (openVelocityWeightedH3State solution t) frequency =
      lerayProjectMode frequency
        (openActualAdvectionMode solution t frequency) := by
  rw [unweightedSharpNonlinearSourceCoefficient_open_eq,
    lerayProjectMode_openActualAdvectionMode_eq]
  rfl

/-- Consequently the projected source and the literal advective coefficient return the same
Hermitian energy work against the actual divergence-free velocity mode. -/
theorem sourceTestProductionReading_openSharpSource_eq_actualAdvection
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    sourceTestProductionReading
        (openPeriodicVelocityFourierMode solution t frequency)
        (unweightedSharpNonlinearSourceCoefficient
          (openVelocityWeightedH3State solution t) frequency) =
      sourceTestProductionReading
        (openPeriodicVelocityFourierMode solution t frequency)
        (openActualAdvectionMode solution t frequency) := by
  rw [unweightedSharpNonlinearSourceCoefficient_eq_leray_openActualAdvectionMode]
  exact sourceTestProductionReading_lerayProjectMode frequency _ _
    (openPeriodicVelocityMode_divergenceFree solution t frequency)

/-- The actual projected order-one coefficient work at the compactly extended source time. -/
def compactProjectedCoordinateH1ModeWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  let t := compactInteriorTime ha hab hbT sourceTime
  projectedCoordinateH1ModeWork frequency
    (openPeriodicVelocityFourierMode solution t frequency)
    (unweightedSharpNonlinearSourceCoefficient
      (openVelocityWeightedH3State solution t) frequency)

/-- The actual projected ordered-second-derivative coefficient work at the same addressed time. -/
def compactProjectedCoordinateH2ModeWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  let t := compactInteriorTime ha hab hbT sourceTime
  projectedCoordinateH2ModeWork frequency
    (openPeriodicVelocityFourierMode solution t frequency)
    (unweightedSharpNonlinearSourceCoefficient
      (openVelocityWeightedH3State solution t) frequency)

/-- **Exact actual one-mode bridge.**  The complete sharp-source curl test is the sum of the
order-one and order-two projected coefficient works.  The compact extension does not disturb the
incidence: the test, velocity and source all use the same clamped interior time. -/
theorem compactH2ProductionCompleteTestReading_eq_projectedOrderOne_add_orderTwo
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) :
    compactH2ProductionCompleteTestReading solution ha hab hbT frequency sourceTime
        (compactH2CurlEnergyTestMode
          solution ha hab hbT frequency sourceTime) =
      compactProjectedCoordinateH1ModeWork
          solution ha hab hbT frequency sourceTime +
        compactProjectedCoordinateH2ModeWork
          solution ha hab hbT frequency sourceTime := by
  let t : Ioo (0 : ℝ) T := compactInteriorTime ha hab hbT sourceTime
  change sourceTestProductionReading
      ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) •
        openPeriodicVorticityFourierMode solution t frequency)
      (vorticityNonlinearMode solution t frequency) = _
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier,
    vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient]
  exact derivativeWeighted_negCurlReading_eq_orderOne_add_orderTwo frequency
    (openPeriodicVelocityFourierMode solution t frequency)
    (unweightedSharpNonlinearSourceCoefficient
      (openVelocityWeightedH3State solution t) frequency)
    (openPeriodicVelocityMode_divergenceFree solution t frequency)
    (openSharpSourceMode_divergenceFree solution t frequency)

/-! ## Exact finite-aperture and complete coefficient populations -/

/-- The actual first-derivative projected work through one finite Fourier aperture. -/
def compactFiniteProjectedCoordinateH1At
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    compactProjectedCoordinateH1ModeWork
      solution ha hab hbT frequency sourceTime

/-- The actual ordered-second-derivative projected work through the same aperture. -/
def compactFiniteProjectedCoordinateH2At
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    compactProjectedCoordinateH2ModeWork
      solution ha hab hbT frequency sourceTime

/-- **[proved-derived; formal-checked]** Every finite aperture preserves the exact separation
between the order-one and order-two Parseval faces. -/
theorem compactFiniteH2CurlCompleteAt_eq_projectedOrderOne_add_orderTwo
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) (sourceTime : ℝ) :
    compactFiniteH2CurlCompleteAt
        solution ha hab hbT modes sourceTime =
      compactFiniteProjectedCoordinateH1At
          solution ha hab hbT modes sourceTime +
        compactFiniteProjectedCoordinateH2At
          solution ha hab hbT modes sourceTime := by
  unfold compactFiniteH2CurlCompleteAt compactFiniteProjectedCoordinateH1At
    compactFiniteProjectedCoordinateH2At
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  exact compactH2ProductionCompleteTestReading_eq_projectedOrderOne_add_orderTwo
    solution ha hab hbT frequency sourceTime

/-- The complete first-derivative projected Fourier population.  The zero mode remains an
explicit summand and vanishes because its Stokes weight is zero. -/
def compactCofinalProjectedCoordinateH1At
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) : ℝ :=
  ∑' frequency : SpatialFrequency,
    compactProjectedCoordinateH1ModeWork
      solution ha hab hbT frequency sourceTime

/-- The complete ordered-second-derivative projected Fourier population. -/
def compactCofinalProjectedCoordinateH2At
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) : ℝ :=
  ∑' frequency : SpatialFrequency,
    compactProjectedCoordinateH2ModeWork
      solution ha hab hbT frequency sourceTime

/-- The complete derivative-weighted sharp-source-curl population. -/
def compactCofinalH2CurlCompleteAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) : ℝ :=
  ∑' frequency : SpatialFrequency,
    compactH2ProductionCompleteTestReading
      solution ha hab hbT frequency sourceTime
        (compactH2CurlEnergyTestMode
          solution ha hab hbT frequency sourceTime)

/-- Modewise Hodge transport composes exactly across the complete coefficient population.  This
identity is independent of a summability proof; the physical Parseval theorem below supplies the
genuine summability and value of both separated faces. -/
theorem compactCofinalH2CurlCompleteAt_eq_tsum_projectedOrderOne_add_orderTwo
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalH2CurlCompleteAt solution ha hab hbT sourceTime =
      ∑' frequency : SpatialFrequency,
        (compactProjectedCoordinateH1ModeWork
            solution ha hab hbT frequency sourceTime +
          compactProjectedCoordinateH2ModeWork
            solution ha hab hbT frequency sourceTime) := by
  apply tsum_congr
  intro frequency
  exact compactH2ProductionCompleteTestReading_eq_projectedOrderOne_add_orderTwo
    solution ha hab hbT frequency sourceTime

/-- Exact order-one removal of the Leray chart in the complete population. -/
theorem compactCofinalProjectedCoordinateH1At_eq_actualAdvection
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalProjectedCoordinateH1At solution ha hab hbT sourceTime =
      ∑' frequency : SpatialFrequency,
        -torusStokesEigenvalue frequency *
          sourceTestProductionReading
            (openPeriodicVelocityFourierMode solution
              (compactInteriorTime ha hab hbT sourceTime) frequency)
            (openActualAdvectionMode solution
              (compactInteriorTime ha hab hbT sourceTime) frequency) := by
  unfold compactCofinalProjectedCoordinateH1At
    compactProjectedCoordinateH1ModeWork projectedCoordinateH1ModeWork
  apply tsum_congr
  intro frequency
  dsimp only
  rw [sourceTestProductionReading_openSharpSource_eq_actualAdvection]

/-- Exact order-two removal of the same Leray chart. -/
theorem compactCofinalProjectedCoordinateH2At_eq_actualAdvection
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalProjectedCoordinateH2At solution ha hab hbT sourceTime =
      ∑' frequency : SpatialFrequency,
        -(torusStokesEigenvalue frequency ^ 2) *
          sourceTestProductionReading
            (openPeriodicVelocityFourierMode solution
              (compactInteriorTime ha hab hbT sourceTime) frequency)
            (openActualAdvectionMode solution
              (compactInteriorTime ha hab hbT sourceTime) frequency) := by
  unfold compactCofinalProjectedCoordinateH2At
    compactProjectedCoordinateH2ModeWork projectedCoordinateH2ModeWork
  apply tsum_congr
  intro frequency
  dsimp only
  rw [sourceTestProductionReading_openSharpSource_eq_actualAdvection]

/-! ## Exact separator between the inherited polar chart and the energy receiver -/

/-- **[counterexample; formal-checked]** Bilinear direction orthogonality does not imply
Hermitian energy orthogonality for a complex Fourier receiver.  This exact two-component
separator prevents the physical-point direction split from being silently substituted for the
Fourier energy test. -/
theorem bilinearDirectionRemainder_not_energyOrthogonal :
    let receiver : ComplexVector := ![2 + 2 * Complex.I, 4 - Complex.I, 0]
    let source : ComplexVector := ![1, 0, 0]
    complexDot receiver (receiverDirectionRemainder receiver source) = 0 ∧
      sourceTestProductionReading receiver
        (receiverDirectionRemainder receiver source) = -(4 / 3 : ℝ) := by
  dsimp
  constructor
  · apply complexDot_receiverDirectionRemainder_eq_zero
    norm_num [complexDot, dotProduct, Fin.sum_univ_succ, Complex.ext_iff]
  · have hnorm :
        Complex.normSq
          ((2 + 2 * Complex.I) * (2 + 2 * Complex.I) +
            (4 - Complex.I) * (4 - Complex.I)) = 225 := by
      norm_num [Complex.normSq]
    norm_num [receiverDirectionRemainder, receiverAlignedAmplitude,
      sourceTestProductionReading, complexDot, dotProduct, Fin.sum_univ_succ,
      Complex.ext_iff, div_eq_mul_inv, hnorm]

/-! ## Order-one physical/Fourier Parseval -/

/-- One component of one addressed first derivative, descended to the genuine torus. -/
def firstDerivativeComponentLift
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (coordinate component : Fin 3) :=
  smoothSliceComponentLift (spatialDirectionalJet field coordinate)
    (spatialDirectionalJet_contDiff field hfield coordinate)
    (spatialDirectionalJet_isOnePeriodic field hperiodic coordinate) component

theorem vectorSpatialFourierCoeff_spatialDirectionalJet_eq_addressed
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (coordinate component : Fin 3)
    (frequency : SpatialFrequency) :
    vectorSpatialFourierCoeff (spatialDirectionalJet field coordinate)
        (spatialDirectionalJet_contDiff field hfield coordinate).continuous
        (spatialDirectionalJet_isOnePeriodic field hperiodic coordinate)
        frequency component =
      addressedCoordinateMultiplier coordinate frequency *
        vectorSpatialFourierCoeff field hfield.continuous hperiodic frequency component := by
  change vectorSpatialFourierCoeff (directionalDerivativeField field coordinate)
      (directionalDerivativeField_contDiff_infty hfield coordinate).continuous
      (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
      frequency component = _
  rw [vectorSpatialFourierCoeff_directionalDerivativeField
    field (hfield.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic frequency
      component coordinate]
  exact actualJacobianFourierMode_eq_addressedCoordinateMultiplier
    field (hfield.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic frequency
      component coordinate

theorem mFourierCoeff_firstDerivativeComponentLift
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (coordinate component : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (firstDerivativeComponentLift field hfield hperiodic coordinate component)
        frequency =
      addressedCoordinateMultiplier coordinate frequency *
        vectorSpatialFourierCoeff field hfield.continuous hperiodic frequency component := by
  have hmcoeff :
      UnitAddTorus.mFourierCoeff
          (firstDerivativeComponentLift field hfield hperiodic coordinate component)
          frequency =
        vectorSpatialFourierCoeff (spatialDirectionalJet field coordinate)
          (spatialDirectionalJet_contDiff field hfield coordinate).continuous
          (spatialDirectionalJet_isOnePeriodic field hperiodic coordinate)
          frequency component := by
    rw [vectorSpatialFourierCoeff_apply]
    rfl
  rw [hmcoeff]
  exact vectorSpatialFourierCoeff_spatialDirectionalJet_eq_addressed
    field hfield hperiodic coordinate component frequency

/-- At one frequency, summing the three first-derivative Parseval faces returns the first Stokes
weight on the base Hermitian coefficient pair. -/
theorem sum_firstDerivativeCoefficientPair_eq_stokes
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right)
    (component : Fin 3) (frequency : SpatialFrequency) :
    (∑ coordinate : Fin 3,
      (starRingEnd ℂ)
          (UnitAddTorus.mFourierCoeff
            (firstDerivativeComponentLift
              left hleft hleftPeriodic coordinate component) frequency) *
        UnitAddTorus.mFourierCoeff
          (firstDerivativeComponentLift
            right hright hrightPeriodic coordinate component) frequency) =
      (torusStokesEigenvalue frequency : ℂ) *
        (starRingEnd ℂ)
          (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
            frequency component) *
        vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
          frequency component := by
  simp_rw [mFourierCoeff_firstDerivativeComponentLift]
  simp only [map_mul]
  calc
    (∑ coordinate : Fin 3,
        (starRingEnd ℂ) (addressedCoordinateMultiplier coordinate frequency) *
            (starRingEnd ℂ)
              (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
                frequency component) *
          (addressedCoordinateMultiplier coordinate frequency *
            vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
              frequency component)) =
      (∑ coordinate : Fin 3,
        (starRingEnd ℂ) (addressedCoordinateMultiplier coordinate frequency) *
          addressedCoordinateMultiplier coordinate frequency) *
        ((starRingEnd ℂ)
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
              frequency component) *
          vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
            frequency component) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro coordinate _hcoordinate
              ring
    _ = _ := by
      rw [sum_addressedCoordinateMultiplier_star_mul]
      ring

/-- **Exact order-one cross Parseval.**  The complete Stokes-weighted Hermitian coefficient
population is the physical torus pairing of all three addressed first derivatives. -/
theorem hasSum_stokes_complexHermitianWork_eq_firstDerivativePairing
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        (torusStokesEigenvalue frequency : ℂ) *
          complexHermitianWork
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic frequency)
            (vectorSpatialFourierCoeff right hright.continuous hrightPeriodic frequency))
      (∑ component : Fin 3, ∑ coordinate : Fin 3,
        ∫ q : SpatialTorus,
          (starRingEnd ℂ)
              (firstDerivativeComponentLift
                left hleft hleftPeriodic coordinate component q) *
            firstDerivativeComponentLift
              right hright hrightPeriodic coordinate component q) := by
  have hcomponent : ∀ component : Fin 3,
      HasSum
        (fun frequency : SpatialFrequency ↦
          (torusStokesEigenvalue frequency : ℂ) *
            (starRingEnd ℂ)
              (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
                frequency component) *
            vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
              frequency component)
        (∑ coordinate : Fin 3,
          ∫ q : SpatialTorus,
            (starRingEnd ℂ)
                (firstDerivativeComponentLift
                  left hleft hleftPeriodic coordinate component q) *
              firstDerivativeComponentLift
                right hright hrightPeriodic coordinate component q) := by
    intro component
    have hcoordinate : ∀ coordinate : Fin 3,
        HasSum
          (fun frequency : SpatialFrequency ↦
            (starRingEnd ℂ)
                (UnitAddTorus.mFourierCoeff
                  (firstDerivativeComponentLift
                    left hleft hleftPeriodic coordinate component) frequency) *
              UnitAddTorus.mFourierCoeff
                (firstDerivativeComponentLift
                  right hright hrightPeriodic coordinate component) frequency)
          (∫ q : SpatialTorus,
            (starRingEnd ℂ)
                (firstDerivativeComponentLift
                  left hleft hleftPeriodic coordinate component q) *
              firstDerivativeComponentLift
                right hright hrightPeriodic coordinate component q) := by
      intro coordinate
      let leftField :=
        firstDerivativeComponentLift left hleft hleftPeriodic coordinate component
      let rightField :=
        firstDerivativeComponentLift right hright hrightPeriodic coordinate component
      have hsummable : Summable (fun frequency : SpatialFrequency ↦
          (starRingEnd ℂ) (UnitAddTorus.mFourierCoeff leftField frequency) *
            UnitAddTorus.mFourierCoeff rightField frequency) := by
        have hraw := UnitAddTorus.hasSum_prod_mFourierCoeff
          (leftField.toLp 2 volume ℂ) (rightField.toLp 2 volume ℂ)
        simpa only [UnitAddTorus.mFourierCoeff_toLp] using hraw.summable
      have hvalue := tsum_conj_mFourierCoeff_mul_eq_integral leftField rightField
      rw [← hvalue]
      exact hsummable.hasSum
    have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun coordinate _hcoordinate ↦ hcoordinate coordinate)
    exact hsum.congr_fun (fun frequency ↦
      sum_firstDerivativeCoefficientPair_eq_stokes
        left right hleft hright hleftPeriodic hrightPeriodic component frequency |>.symm)
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun component _hcomponent ↦ hcomponent component)
  refine hsum.congr_fun (fun frequency ↦ ?_)
  unfold complexHermitianWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  ring

/-! ## Order-two physical/Fourier Parseval -/

/-- One component of one ordered second derivative on the torus. -/
def secondDerivativeComponentLift
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (first second component : Fin 3) :=
  smoothSliceComponentLift (secondSpatialCoordinateJet field first second)
    (secondSpatialCoordinateJet_contDiff field hfield first second)
    (secondSpatialCoordinateJet_isOnePeriodic field hperiodic first second) component

theorem vectorSpatialFourierCoeff_secondSpatialCoordinateJet_eq_addressed
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (first second component : Fin 3)
    (frequency : SpatialFrequency) :
    vectorSpatialFourierCoeff (secondSpatialCoordinateJet field first second)
        (secondSpatialCoordinateJet_contDiff field hfield first second).continuous
        (secondSpatialCoordinateJet_isOnePeriodic field hperiodic first second)
        frequency component =
      (addressedCoordinateMultiplier first frequency *
        addressedCoordinateMultiplier second frequency) *
        vectorSpatialFourierCoeff field hfield.continuous hperiodic frequency component := by
  unfold secondSpatialCoordinateJet
  rw [vectorSpatialFourierCoeff_spatialDirectionalJet_eq_addressed
    (spatialDirectionalJet field second)
      (spatialDirectionalJet_contDiff field hfield second)
      (spatialDirectionalJet_isOnePeriodic field hperiodic second)
      first component frequency]
  rw [vectorSpatialFourierCoeff_spatialDirectionalJet_eq_addressed
    field hfield hperiodic second component frequency]
  ring

theorem mFourierCoeff_secondDerivativeComponentLift
    (field : InitialVelocity) (hfield : ContDiff ℝ (⊤ : ℕ∞) field)
    (hperiodic : IsOnePeriodic field) (first second component : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (secondDerivativeComponentLift
          field hfield hperiodic first second component) frequency =
      (addressedCoordinateMultiplier first frequency *
        addressedCoordinateMultiplier second frequency) *
        vectorSpatialFourierCoeff field hfield.continuous hperiodic frequency component := by
  have hmcoeff :
      UnitAddTorus.mFourierCoeff
          (secondDerivativeComponentLift
            field hfield hperiodic first second component) frequency =
        vectorSpatialFourierCoeff (secondSpatialCoordinateJet field first second)
          (secondSpatialCoordinateJet_contDiff field hfield first second).continuous
          (secondSpatialCoordinateJet_isOnePeriodic field hperiodic first second)
          frequency component := by
    rw [vectorSpatialFourierCoeff_apply]
    rfl
  rw [hmcoeff]
  exact vectorSpatialFourierCoeff_secondSpatialCoordinateJet_eq_addressed
    field hfield hperiodic first second component frequency

theorem sum_secondDerivativeMultiplier_star_mul
    (frequency : SpatialFrequency) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      (starRingEnd ℂ)
          (addressedCoordinateMultiplier first frequency *
            addressedCoordinateMultiplier second frequency) *
        (addressedCoordinateMultiplier first frequency *
          addressedCoordinateMultiplier second frequency)) =
      ((torusStokesEigenvalue frequency : ℂ) ^ 2) := by
  simp only [map_mul]
  calc
    (∑ first : Fin 3, ∑ second : Fin 3,
        ((starRingEnd ℂ) (addressedCoordinateMultiplier first frequency) *
            (starRingEnd ℂ) (addressedCoordinateMultiplier second frequency)) *
          (addressedCoordinateMultiplier first frequency *
            addressedCoordinateMultiplier second frequency)) =
      (∑ first : Fin 3,
        (starRingEnd ℂ) (addressedCoordinateMultiplier first frequency) *
          addressedCoordinateMultiplier first frequency) *
        (∑ second : Fin 3,
          (starRingEnd ℂ) (addressedCoordinateMultiplier second frequency) *
            addressedCoordinateMultiplier second frequency) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro first _hfirst
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro second _hsecond
              ring
    _ = _ := by
      rw [sum_addressedCoordinateMultiplier_star_mul]
      ring

theorem sum_secondDerivativeCoefficientPair_eq_stokes_sq
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right)
    (component : Fin 3) (frequency : SpatialFrequency) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      (starRingEnd ℂ)
          (UnitAddTorus.mFourierCoeff
            (secondDerivativeComponentLift
              left hleft hleftPeriodic first second component) frequency) *
        UnitAddTorus.mFourierCoeff
          (secondDerivativeComponentLift
            right hright hrightPeriodic first second component) frequency) =
      ((torusStokesEigenvalue frequency : ℂ) ^ 2) *
        (starRingEnd ℂ)
          (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
            frequency component) *
        vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
          frequency component := by
  simp_rw [mFourierCoeff_secondDerivativeComponentLift]
  simp only [map_mul]
  calc
    (∑ first : Fin 3, ∑ second : Fin 3,
        (((starRingEnd ℂ) (addressedCoordinateMultiplier first frequency) *
            (starRingEnd ℂ) (addressedCoordinateMultiplier second frequency)) *
          (starRingEnd ℂ)
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
              frequency component)) *
          ((addressedCoordinateMultiplier first frequency *
              addressedCoordinateMultiplier second frequency) *
            vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
              frequency component)) =
      (∑ first : Fin 3, ∑ second : Fin 3,
        (starRingEnd ℂ)
            (addressedCoordinateMultiplier first frequency *
              addressedCoordinateMultiplier second frequency) *
          (addressedCoordinateMultiplier first frequency *
            addressedCoordinateMultiplier second frequency)) *
        ((starRingEnd ℂ)
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
              frequency component) *
          vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
            frequency component) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro first _hfirst
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro second _hsecond
              rw [map_mul]
              ring
    _ = _ := by
      rw [sum_secondDerivativeMultiplier_star_mul]
      ring

/-- **Exact order-two cross Parseval.**  The squared-Stokes Hermitian population is the physical
torus pairing of all nine ordered second derivatives. -/
theorem hasSum_stokes_sq_complexHermitianWork_eq_secondDerivativePairing
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        ((torusStokesEigenvalue frequency : ℂ) ^ 2) *
          complexHermitianWork
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic frequency)
            (vectorSpatialFourierCoeff right hright.continuous hrightPeriodic frequency))
      (∑ component : Fin 3, ∑ first : Fin 3, ∑ second : Fin 3,
        ∫ q : SpatialTorus,
          (starRingEnd ℂ)
              (secondDerivativeComponentLift
                left hleft hleftPeriodic first second component q) *
            secondDerivativeComponentLift
              right hright hrightPeriodic first second component q) := by
  have hcomponent : ∀ component : Fin 3,
      HasSum
        (fun frequency : SpatialFrequency ↦
          ((torusStokesEigenvalue frequency : ℂ) ^ 2) *
            (starRingEnd ℂ)
              (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic
                frequency component) *
            vectorSpatialFourierCoeff right hright.continuous hrightPeriodic
              frequency component)
        (∑ first : Fin 3, ∑ second : Fin 3,
          ∫ q : SpatialTorus,
            (starRingEnd ℂ)
                (secondDerivativeComponentLift
                  left hleft hleftPeriodic first second component q) *
              secondDerivativeComponentLift
                right hright hrightPeriodic first second component q) := by
    intro component
    have hpair : ∀ first second : Fin 3,
        HasSum
          (fun frequency : SpatialFrequency ↦
            (starRingEnd ℂ)
                (UnitAddTorus.mFourierCoeff
                  (secondDerivativeComponentLift
                    left hleft hleftPeriodic first second component) frequency) *
              UnitAddTorus.mFourierCoeff
                (secondDerivativeComponentLift
                  right hright hrightPeriodic first second component) frequency)
          (∫ q : SpatialTorus,
            (starRingEnd ℂ)
                (secondDerivativeComponentLift
                  left hleft hleftPeriodic first second component q) *
              secondDerivativeComponentLift
                right hright hrightPeriodic first second component q) := by
      intro first second
      let leftField := secondDerivativeComponentLift
        left hleft hleftPeriodic first second component
      let rightField := secondDerivativeComponentLift
        right hright hrightPeriodic first second component
      have hsummable : Summable (fun frequency : SpatialFrequency ↦
          (starRingEnd ℂ) (UnitAddTorus.mFourierCoeff leftField frequency) *
            UnitAddTorus.mFourierCoeff rightField frequency) := by
        have hraw := UnitAddTorus.hasSum_prod_mFourierCoeff
          (leftField.toLp 2 volume ℂ) (rightField.toLp 2 volume ℂ)
        simpa only [UnitAddTorus.mFourierCoeff_toLp] using hraw.summable
      have hvalue := tsum_conj_mFourierCoeff_mul_eq_integral leftField rightField
      rw [← hvalue]
      exact hsummable.hasSum
    have hsecond : ∀ first : Fin 3,
        HasSum
          (fun frequency : SpatialFrequency ↦ ∑ second : Fin 3,
            (starRingEnd ℂ)
                (UnitAddTorus.mFourierCoeff
                  (secondDerivativeComponentLift
                    left hleft hleftPeriodic first second component) frequency) *
              UnitAddTorus.mFourierCoeff
                (secondDerivativeComponentLift
                  right hright hrightPeriodic first second component) frequency)
          (∑ second : Fin 3,
            ∫ q : SpatialTorus,
              (starRingEnd ℂ)
                  (secondDerivativeComponentLift
                    left hleft hleftPeriodic first second component q) *
                secondDerivativeComponentLift
                  right hright hrightPeriodic first second component q) := by
      intro first
      exact hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
        (fun second _hsecond ↦ hpair first second)
    have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun first _hfirst ↦ hsecond first)
    exact hsum.congr_fun (fun frequency ↦
      sum_secondDerivativeCoefficientPair_eq_stokes_sq
        left right hleft hright hleftPeriodic hrightPeriodic component frequency |>.symm)
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun component _hcomponent ↦ hcomponent component)
  refine hsum.congr_fun (fun frequency ↦ ?_)
  unfold complexHermitianWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  ring

/-! ## Return to the literal Euclidean cube -/

theorem re_integral_firstDerivativeComponentLift_mul_eq_cube
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right)
    (coordinate component : Fin 3) :
    (∫ q : SpatialTorus,
      (starRingEnd ℂ)
          (firstDerivativeComponentLift
            left hleft hleftPeriodic coordinate component q) *
        firstDerivativeComponentLift
          right hright hrightPeriodic coordinate component q).re =
      ∫ x in unitCube,
        spatialDirectionalJet left coordinate x component *
          spatialDirectionalJet right coordinate x component := by
  let complexField : C(SpatialTorus, ℂ) :=
    ⟨fun q ↦
        (starRingEnd ℂ)
            (firstDerivativeComponentLift
              left hleft hleftPeriodic coordinate component q) *
          firstDerivativeComponentLift
            right hright hrightPeriodic coordinate component q,
      by fun_prop⟩
  let realField : C(SpatialTorus, ℝ) :=
    ⟨fun q ↦ (complexField q).re, by fun_prop⟩
  have hintegrable : Integrable complexField :=
    continuousMap_integrable_on_compact complexField
  have hre : (∫ q : SpatialTorus, complexField q).re =
      ∫ q : SpatialTorus, realField q := by
    change Complex.reCLM (∫ q : SpatialTorus, complexField q) = _
    rw [← Complex.reCLM.integral_comp_comm hintegrable]
    rfl
  have hchart := integral_euclideanToSpatialTorus_unitCube realField
  simp only [MeasureTheory.volume_pi, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] at hchart
  calc
    (∫ q : SpatialTorus,
        (starRingEnd ℂ)
            (firstDerivativeComponentLift
              left hleft hleftPeriodic coordinate component q) *
          firstDerivativeComponentLift
            right hright hrightPeriodic coordinate component q).re =
      ∫ q : SpatialTorus, realField q := hre
    _ = ∫ x in unitCube, realField (euclideanToSpatialTorus x) := hchart.symm
    _ = ∫ x in unitCube,
        spatialDirectionalJet left coordinate x component *
          spatialDirectionalJet right coordinate x component := by
      apply setIntegral_congr_fun
      · unfold unitCube
        exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
          isCompact_Icc |>.measurableSet
      · intro x _hx
        simp [realField, complexField, firstDerivativeComponentLift,
          smoothSliceComponentLift, periodicTorusLift_projection,
          complexVelocityComponent]

theorem re_integral_secondDerivativeComponentLift_mul_eq_cube
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right)
    (first second component : Fin 3) :
    (∫ q : SpatialTorus,
      (starRingEnd ℂ)
          (secondDerivativeComponentLift
            left hleft hleftPeriodic first second component q) *
        secondDerivativeComponentLift
          right hright hrightPeriodic first second component q).re =
      ∫ x in unitCube,
        secondSpatialCoordinateJet left first second x component *
          secondSpatialCoordinateJet right first second x component := by
  let complexField : C(SpatialTorus, ℂ) :=
    ⟨fun q ↦
        (starRingEnd ℂ)
            (secondDerivativeComponentLift
              left hleft hleftPeriodic first second component q) *
          secondDerivativeComponentLift
            right hright hrightPeriodic first second component q,
      by fun_prop⟩
  let realField : C(SpatialTorus, ℝ) :=
    ⟨fun q ↦ (complexField q).re, by fun_prop⟩
  have hintegrable : Integrable complexField :=
    continuousMap_integrable_on_compact complexField
  have hre : (∫ q : SpatialTorus, complexField q).re =
      ∫ q : SpatialTorus, realField q := by
    change Complex.reCLM (∫ q : SpatialTorus, complexField q) = _
    rw [← Complex.reCLM.integral_comp_comm hintegrable]
    rfl
  have hchart := integral_euclideanToSpatialTorus_unitCube realField
  simp only [MeasureTheory.volume_pi, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul] at hchart
  calc
    (∫ q : SpatialTorus,
        (starRingEnd ℂ)
            (secondDerivativeComponentLift
              left hleft hleftPeriodic first second component q) *
          secondDerivativeComponentLift
            right hright hrightPeriodic first second component q).re =
      ∫ q : SpatialTorus, realField q := hre
    _ = ∫ x in unitCube, realField (euclideanToSpatialTorus x) := hchart.symm
    _ = ∫ x in unitCube,
        secondSpatialCoordinateJet left first second x component *
          secondSpatialCoordinateJet right first second x component := by
      apply setIntegral_congr_fun
      · unfold unitCube
        exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
          isCompact_Icc |>.measurableSet
      · intro x _hx
        simp [realField, complexField, secondDerivativeComponentLift,
          smoothSliceComponentLift, periodicTorusLift_projection,
          complexVelocityComponent]

theorem re_firstDerivativePairing_eq_cube
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    (∑ component : Fin 3, ∑ coordinate : Fin 3,
      ∫ q : SpatialTorus,
        (starRingEnd ℂ)
            (firstDerivativeComponentLift
              left hleft hleftPeriodic coordinate component q) *
          firstDerivativeComponentLift
            right hright hrightPeriodic coordinate component q).re =
      ∑ component : Fin 3, ∑ coordinate : Fin 3,
        ∫ x in unitCube,
          spatialDirectionalJet left coordinate x component *
            spatialDirectionalJet right coordinate x component := by
  change Complex.reCLM (∑ component : Fin 3, ∑ coordinate : Fin 3,
      ∫ q : SpatialTorus,
        (starRingEnd ℂ)
            (firstDerivativeComponentLift
              left hleft hleftPeriodic coordinate component q) *
          firstDerivativeComponentLift
            right hright hrightPeriodic coordinate component q) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  exact re_integral_firstDerivativeComponentLift_mul_eq_cube
    left right hleft hright hleftPeriodic hrightPeriodic coordinate component

theorem re_secondDerivativePairing_eq_cube
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    (∑ component : Fin 3, ∑ first : Fin 3, ∑ second : Fin 3,
      ∫ q : SpatialTorus,
        (starRingEnd ℂ)
            (secondDerivativeComponentLift
              left hleft hleftPeriodic first second component q) *
          secondDerivativeComponentLift
            right hright hrightPeriodic first second component q).re =
      ∑ component : Fin 3, ∑ first : Fin 3, ∑ second : Fin 3,
        ∫ x in unitCube,
          secondSpatialCoordinateJet left first second x component *
            secondSpatialCoordinateJet right first second x component := by
  change Complex.reCLM (∑ component : Fin 3, ∑ first : Fin 3,
      ∑ second : Fin 3,
        ∫ q : SpatialTorus,
          (starRingEnd ℂ)
              (secondDerivativeComponentLift
                left hleft hleftPeriodic first second component q) *
            secondDerivativeComponentLift
              right hright hrightPeriodic first second component q) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _hfirst
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _hsecond
  exact re_integral_secondDerivativeComponentLift_mul_eq_cube
    left right hleft hright hleftPeriodic hrightPeriodic first second component

/-- Literal real cube pairing of every addressed first derivative. -/
def firstDerivativeCubePairing (left right : InitialVelocity) : ℝ :=
  ∑ component : Fin 3, ∑ coordinate : Fin 3,
    ∫ x in unitCube,
      spatialDirectionalJet left coordinate x component *
        spatialDirectionalJet right coordinate x component

/-- Literal real cube pairing of every ordered second derivative. -/
def secondDerivativeCubePairing (left right : InitialVelocity) : ℝ :=
  ∑ component : Fin 3, ∑ first : Fin 3, ∑ second : Fin 3,
    ∫ x in unitCube,
      secondSpatialCoordinateJet left first second x component *
        secondSpatialCoordinateJet right first second x component

/-- Real order-one Parseval in the exact receiver convention used by nonlinear production. -/
theorem hasSum_stokes_sourceTestProductionReading_eq_firstDerivativeCubePairing
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        torusStokesEigenvalue frequency *
          sourceTestProductionReading
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic frequency)
            (vectorSpatialFourierCoeff right hright.continuous hrightPeriodic frequency))
      (firstDerivativeCubePairing left right) := by
  have hcomplex := hasSum_stokes_complexHermitianWork_eq_firstDerivativePairing
    left right hleft hright hleftPeriodic hrightPeriodic
  have hreal := Complex.reCLM.hasSum hcomplex
  have hlimit := re_firstDerivativePairing_eq_cube
    left right hleft hright hleftPeriodic hrightPeriodic
  unfold firstDerivativeCubePairing
  rw [← hlimit]
  refine hreal.congr_fun (fun frequency ↦ ?_)
  simp only [Complex.reCLM_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [sourceTestProductionReading_eq_re_complexHermitianWork]

/-- Real order-two Parseval for the squared Stokes multiplier. -/
theorem hasSum_stokes_sq_sourceTestProductionReading_eq_secondDerivativeCubePairing
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ (⊤ : ℕ∞) left)
    (hright : ContDiff ℝ (⊤ : ℕ∞) right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        torusStokesEigenvalue frequency ^ 2 *
          sourceTestProductionReading
            (vectorSpatialFourierCoeff left hleft.continuous hleftPeriodic frequency)
            (vectorSpatialFourierCoeff right hright.continuous hrightPeriodic frequency))
      (secondDerivativeCubePairing left right) := by
  have hcomplex := hasSum_stokes_sq_complexHermitianWork_eq_secondDerivativePairing
    left right hleft hright hleftPeriodic hrightPeriodic
  have hreal := Complex.reCLM.hasSum hcomplex
  have hlimit := re_secondDerivativePairing_eq_cube
    left right hleft hright hleftPeriodic hrightPeriodic
  unfold secondDerivativeCubePairing
  rw [← hlimit]
  refine hreal.congr_fun (fun frequency ↦ ?_)
  rw [sourceTestProductionReading_eq_re_complexHermitianWork]
  simp only [Complex.reCLM_apply, Complex.mul_re]
  norm_cast
  ring

/-! ## Physical return of the two multiplier orders -/

private def firstCoordinateWordEquiv : Fin 3 ≃ (Fin 1 → Fin 3) where
  toFun := firstCoordinateWord
  invFun := fun word ↦ word 0
  left_inv := by intro coordinate; rfl
  right_inv := by
    intro word
    funext q
    fin_cases q
    rfl

private def secondCoordinateWordEquiv : (Fin 3 × Fin 3) ≃ (Fin 2 → Fin 3) where
  toFun := fun pair ↦ secondCoordinateWord pair.1 pair.2
  invFun := fun word ↦ (word 0, word 1)
  left_inv := by intro pair; cases pair; rfl
  right_inv := by
    intro word
    funext q
    fin_cases q <;> rfl

/-- One derivative of the literal advective field is top transport plus the stretching face. -/
theorem spatialDirectionalJet_actualAdvectionField_eq_transport_add_stretching
    (u : InitialVelocity) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Space) (coordinate : Fin 3) :
    spatialDirectionalJet (actualAdvectionField u) coordinate x =
      fderiv ℝ (spatialDirectionalJet u coordinate) x (u x) +
        fderiv ℝ u x (spatialDirectionalJet u coordinate x) := by
  change fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x (spatialBasisVector coordinate) = _
  exact fderiv_advection_eq_transport_add_stretching
    u (hu.of_le (WithTop.coe_le_coe.mpr le_top)) x coordinate

/-- Two addressed derivatives of the literal advective field retain top transport and exactly
the three lower commutator faces. -/
theorem secondSpatialCoordinateJet_actualAdvectionField_eq_transport_add_lower
    (u : InitialVelocity) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Space) (first second : Fin 3) :
    secondSpatialCoordinateJet (actualAdvectionField u) first second x =
      fderiv ℝ (secondSpatialCoordinateJet u first second) x (u x) +
        fderiv ℝ (spatialDirectionalJet u second) x
          (spatialDirectionalJet u first x) +
        fderiv ℝ (spatialDirectionalJet u first) x
          (spatialDirectionalJet u second x) +
        fderiv ℝ u x (secondSpatialCoordinateJet u first second x) := by
  let wi : InitialVelocity := spatialDirectionalJet u first
  let wj : InitialVelocity := spatialDirectionalJet u second
  let W : InitialVelocity := secondSpatialCoordinateJet u first second
  have hwi : ContDiff ℝ (⊤ : ℕ∞) wi := spatialDirectionalJet_contDiff u hu first
  have hwj : ContDiff ℝ (⊤ : ℕ∞) wj := spatialDirectionalJet_contDiff u hu second
  have hfirstFun :
      spatialDirectionalJet (actualAdvectionField u) second =
        fun y ↦ fderiv ℝ wj y (u y) + fderiv ℝ u y (wj y) := by
    funext y
    simpa [wj] using
      spatialDirectionalJet_actualAdvectionField_eq_transport_add_stretching
        u hu y second
  have hDwj : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDu : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by simp)
  have htransportDiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ wj y (u y)) x :=
    (hDwj.clm_apply hu).differentiable (by simp) x
  have hstretchDiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (wj y)) x :=
    (hDu.clm_apply hwj).differentiable (by simp) x
  have htransport := fderiv_jacobianAction_eq_transport_add_lower
    wj u (hwj.of_le (WithTop.coe_le_coe.mpr le_top))
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) x first
  have hstretch := fderiv_jacobianAction_eq_transport_add_lower
    u wj (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (hwj.of_le (WithTop.coe_le_coe.mpr le_top)) x first
  have hW : W = spatialDirectionalJet wj first := rfl
  have hwiPoint : fderiv ℝ u x (spatialBasisVector first) = wi x := rfl
  have hWPoint : spatialDirectionalJet wj first x = W x := rfl
  have hsum := fderiv_fun_add htransportDiff hstretchDiff
  have hsumApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector first)) hsum
  rw [← hfirstFun] at hsumApply
  simp only [add_apply] at hsumApply
  rw [htransport, hstretch] at hsumApply
  simpa [secondSpatialCoordinateJet, spatialDirectionalJet, wi, wj, W,
    add_assoc] using hsumApply

private theorem sum_component_integral_mul_eq_integral_inner
    (left right : Space → Space) (hleft : Continuous left) (hright : Continuous right) :
    (∑ component : Fin 3,
      ∫ x in unitCube, left x component * right x component) =
      ∫ x in unitCube, inner ℝ (right x) (left x) := by
  have hcubeCompact : IsCompact (unitCube : Set Space) := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  calc
    (∑ component : Fin 3,
        ∫ x in unitCube, left x component * right x component) =
      ∫ x in unitCube,
        ∑ component : Fin 3, left x component * right x component := by
          rw [integral_finsetSum Finset.univ]
          intro component _hcomponent
          have hlc : Continuous (fun x : Space ↦ left x component) :=
            (EuclideanSpace.proj component).continuous.comp hleft
          have hrc : Continuous (fun x : Space ↦ right x component) :=
            (EuclideanSpace.proj component).continuous.comp hright
          exact (hlc.mul hrc).continuousOn.integrableOn_compact hcubeCompact
    _ = ∫ x in unitCube, inner ℝ (right x) (left x) := by
      apply setIntegral_congr_fun hcubeCompact.measurableSet
      intro x _hx
      simp [PiLp.inner_apply]

/-- The order-one physical derivative pairing returns exactly the stretching work after the
periodic top-transport face is integrated by reflection. -/
theorem firstDerivativeCubePairing_actualAdvectionField_eq_coordinateH1StretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    firstDerivativeCubePairing (fun x ↦ velocity x t)
        (actualAdvectionField (fun x ↦ velocity x t)) =
      coordinateH1StretchingWork velocity t := by
  let u : InitialVelocity := fun x ↦ velocity x t
  let a : InitialVelocity := actualAdvectionField u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := actualAdvectionField_contDiff hu
  have hcubeCompact : IsCompact (unitCube : Set Space) := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcoordinate : ∀ coordinate : Fin 3,
      (∫ x in unitCube,
          inner ℝ (spatialDirectionalJet a coordinate x)
            (spatialDirectionalJet u coordinate x)) =
        ∫ x in unitCube,
          inner ℝ
            (fderiv ℝ u x (spatialDirectionalJet u coordinate x))
            (spatialDirectionalJet u coordinate x) := by
    intro coordinate
    let w : InitialVelocity := spatialDirectionalJet u coordinate
    let transported : InitialVelocity := fun x ↦ fderiv ℝ w x (u x)
    let stretched : InitialVelocity := fun x ↦ fderiv ℝ u x (w x)
    have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
      spatialDirectionalJet_contDiff u hu coordinate
    have hDw : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ w) :=
      hw.fderiv_right (by simp)
    have hDu : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (by simp)
    have htransported : ContDiff ℝ (⊤ : ℕ∞) transported :=
      hDw.clm_apply hu
    have hstretched : ContDiff ℝ (⊤ : ℕ∞) stretched :=
      hDu.clm_apply hw
    have htransportInt : IntegrableOn
        (fun x ↦ inner ℝ (transported x) (w x)) unitCube :=
      (htransported.continuous.inner hw.continuous).continuousOn
        |>.integrableOn_compact hcubeCompact
    have hstretchInt : IntegrableOn
        (fun x ↦ inner ℝ (stretched x) (w x)) unitCube :=
      (hstretched.continuous.inner hw.continuous).continuousOn
        |>.integrableOn_compact hcubeCompact
    have htransportZero :=
      openPeriodicSolutionOn_integral_firstCoordinateTransport_eq_zero
        solution ht coordinate
    have hwFun : (fun x ↦ firstCoordinateJet velocity coordinate x t) = w := by
      funext x
      exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution ht x coordinate
    simp_rw [congrFun hwFun] at htransportZero
    change (∫ x in unitCube, inner ℝ (transported x) (w x)) = 0 at htransportZero
    calc
      (∫ x in unitCube,
          inner ℝ (spatialDirectionalJet a coordinate x) (w x)) =
        ∫ x in unitCube,
          (inner ℝ (transported x) (w x) + inner ℝ (stretched x) (w x)) := by
            apply setIntegral_congr_fun hcubeCompact.measurableSet
            intro x _hx
            dsimp [a, w, transported, stretched]
            rw [spatialDirectionalJet_actualAdvectionField_eq_transport_add_stretching
              u hu x coordinate]
            rw [inner_add_left]
      _ = (∫ x in unitCube, inner ℝ (transported x) (w x)) +
          ∫ x in unitCube, inner ℝ (stretched x) (w x) :=
        integral_add htransportInt hstretchInt
      _ = ∫ x in unitCube, inner ℝ (stretched x) (w x) := by
        rw [htransportZero, zero_add]
      _ = ∫ x in unitCube,
          inner ℝ (fderiv ℝ u x (spatialDirectionalJet u coordinate x))
            (spatialDirectionalJet u coordinate x) := by rfl
  change firstDerivativeCubePairing u a = _
  unfold firstDerivativeCubePairing
  rw [Finset.sum_comm]
  calc
    (∑ coordinate : Fin 3, ∑ component : Fin 3,
        ∫ x in unitCube,
          spatialDirectionalJet u coordinate x component *
            spatialDirectionalJet a coordinate x component) =
      ∑ coordinate : Fin 3,
        ∫ x in unitCube,
          inner ℝ (spatialDirectionalJet a coordinate x)
            (spatialDirectionalJet u coordinate x) := by
        apply Finset.sum_congr rfl
        intro coordinate _hcoordinate
        exact sum_component_integral_mul_eq_integral_inner
          (spatialDirectionalJet u coordinate)
          (spatialDirectionalJet a coordinate)
          (spatialDirectionalJet_contDiff u hu coordinate).continuous
          (spatialDirectionalJet_contDiff a ha coordinate).continuous
    _ = ∑ coordinate : Fin 3,
        ∫ x in unitCube,
          inner ℝ (fderiv ℝ u x (spatialDirectionalJet u coordinate x))
            (spatialDirectionalJet u coordinate x) := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      exact hcoordinate coordinate
    _ = coordinateH1StretchingWork velocity t := by
      unfold coordinateH1StretchingWork
      exact Fintype.sum_equiv firstCoordinateWordEquiv _ _ (fun coordinate ↦ by
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        have hword : firstCoordinateWordEquiv coordinate =
            firstCoordinateWord coordinate := rfl
        rw [hword]
        change _ = inner ℝ
          (fderiv ℝ u x (firstCoordinateJet velocity coordinate x t))
          (firstCoordinateJet velocity coordinate x t)
        rw [openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
          solution ht x coordinate])

/-- The order-two physical derivative pairing returns exactly the three-face lower commutator
work after the periodic top-transport face is integrated by reflection. -/
theorem secondDerivativeCubePairing_actualAdvectionField_eq_coordinateH2LowerWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    secondDerivativeCubePairing (fun x ↦ velocity x t)
        (actualAdvectionField (fun x ↦ velocity x t)) =
      coordinateH2LowerWork velocity t := by
  let u : InitialVelocity := fun x ↦ velocity x t
  let a : InitialVelocity := actualAdvectionField u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := actualAdvectionField_contDiff hu
  have hcubeCompact : IsCompact (unitCube : Set Space) := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hpair : ∀ first second : Fin 3,
      (∫ x in unitCube,
          inner ℝ (secondSpatialCoordinateJet a first second x)
            (secondSpatialCoordinateJet u first second x)) =
        ∫ x in unitCube,
          inner ℝ (secondCoordinateLowerCommutator velocity t first second x)
            (secondSpatialCoordinateJet u first second x) := by
    intro first second
    let wi : InitialVelocity := spatialDirectionalJet u first
    let wj : InitialVelocity := spatialDirectionalJet u second
    let W : InitialVelocity := secondSpatialCoordinateJet u first second
    let transported : InitialVelocity := fun x ↦ fderiv ℝ W x (u x)
    let lower : InitialVelocity := fun x ↦
      fderiv ℝ wj x (wi x) + fderiv ℝ wi x (wj x) + fderiv ℝ u x (W x)
    have hwi : ContDiff ℝ (⊤ : ℕ∞) wi :=
      spatialDirectionalJet_contDiff u hu first
    have hwj : ContDiff ℝ (⊤ : ℕ∞) wj :=
      spatialDirectionalJet_contDiff u hu second
    have hW : ContDiff ℝ (⊤ : ℕ∞) W :=
      secondSpatialCoordinateJet_contDiff u hu first second
    have hDW : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ W) :=
      hW.fderiv_right (by simp)
    have hDwi : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ wi) :=
      hwi.fderiv_right (by simp)
    have hDwj : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ wj) :=
      hwj.fderiv_right (by simp)
    have hDu : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (by simp)
    have htransported : ContDiff ℝ (⊤ : ℕ∞) transported :=
      hDW.clm_apply hu
    have hlower : ContDiff ℝ (⊤ : ℕ∞) lower :=
      ((hDwj.clm_apply hwi).add (hDwi.clm_apply hwj)).add (hDu.clm_apply hW)
    have htransportInt : IntegrableOn
        (fun x ↦ inner ℝ (transported x) (W x)) unitCube :=
      (htransported.continuous.inner hW.continuous).continuousOn
        |>.integrableOn_compact hcubeCompact
    have hlowerInt : IntegrableOn
        (fun x ↦ inner ℝ (lower x) (W x)) unitCube :=
      (hlower.continuous.inner hW.continuous).continuousOn
        |>.integrableOn_compact hcubeCompact
    have htransportZero :=
      openPeriodicSolutionOn_integral_secondCoordinateTransport_eq_zero
        solution ht first second
    have hWFun : (fun x ↦ secondCoordinateJet velocity first second x t) = W := by
      funext x
      exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
        solution ht x first second
    have hwiFun : (fun x ↦ firstCoordinateJet velocity first x t) = wi := by
      funext x
      exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution ht x first
    have hwjFun : (fun x ↦ firstCoordinateJet velocity second x t) = wj := by
      funext x
      exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution ht x second
    simp_rw [congrFun hWFun] at htransportZero
    change (∫ x in unitCube, inner ℝ (transported x) (W x)) = 0 at htransportZero
    have hlowerPhysical : lower =
        fun x ↦ secondCoordinateLowerCommutator velocity t first second x := by
      funext x
      dsimp [lower, wi, wj, W, secondCoordinateLowerCommutator]
      rw [hwiFun, hwjFun]
      simp_rw [congrFun hwiFun, congrFun hwjFun]
      simp_rw [openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
        solution ht x first second]
      simp [wi, wj, u]
    calc
      (∫ x in unitCube,
          inner ℝ (secondSpatialCoordinateJet a first second x) (W x)) =
        ∫ x in unitCube,
          (inner ℝ (transported x) (W x) + inner ℝ (lower x) (W x)) := by
            apply setIntegral_congr_fun hcubeCompact.measurableSet
            intro x _hx
            dsimp [a, W, transported, lower, wi, wj]
            rw [secondSpatialCoordinateJet_actualAdvectionField_eq_transport_add_lower
              u hu x first second]
            simp only [inner_add_left]
            abel
      _ = (∫ x in unitCube, inner ℝ (transported x) (W x)) +
          ∫ x in unitCube, inner ℝ (lower x) (W x) :=
        integral_add htransportInt hlowerInt
      _ = ∫ x in unitCube, inner ℝ (lower x) (W x) := by
        rw [htransportZero, zero_add]
      _ = ∫ x in unitCube,
          inner ℝ (secondCoordinateLowerCommutator velocity t first second x)
            (secondSpatialCoordinateJet u first second x) := by
        rw [hlowerPhysical]
  change secondDerivativeCubePairing u a = _
  unfold secondDerivativeCubePairing
  calc
    (∑ component : Fin 3, ∑ first : Fin 3, ∑ second : Fin 3,
        ∫ x in unitCube,
          secondSpatialCoordinateJet u first second x component *
            secondSpatialCoordinateJet a first second x component) =
      ∑ first : Fin 3, ∑ second : Fin 3, ∑ component : Fin 3,
        ∫ x in unitCube,
          secondSpatialCoordinateJet u first second x component *
            secondSpatialCoordinateJet a first second x component := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro first _hfirst
        rw [Finset.sum_comm]
    _ = ∑ first : Fin 3, ∑ second : Fin 3,
        ∫ x in unitCube,
          inner ℝ (secondSpatialCoordinateJet a first second x)
            (secondSpatialCoordinateJet u first second x) := by
      apply Finset.sum_congr rfl
      intro first _hfirst
      apply Finset.sum_congr rfl
      intro second _hsecond
      exact sum_component_integral_mul_eq_integral_inner
        (secondSpatialCoordinateJet u first second)
        (secondSpatialCoordinateJet a first second)
        (secondSpatialCoordinateJet_contDiff u hu first second).continuous
        (secondSpatialCoordinateJet_contDiff a ha first second).continuous
    _ = ∑ first : Fin 3, ∑ second : Fin 3,
        ∫ x in unitCube,
          inner ℝ (secondCoordinateLowerCommutator velocity t first second x)
            (secondSpatialCoordinateJet u first second x) := by
      apply Finset.sum_congr rfl
      intro first _hfirst
      apply Finset.sum_congr rfl
      intro second _hsecond
      exact hpair first second
    _ = coordinateH2LowerWork velocity t := by
      unfold coordinateH2LowerWork
      calc
        (∑ first : Fin 3, ∑ second : Fin 3,
            ∫ x in unitCube,
              inner ℝ (secondCoordinateLowerCommutator velocity t first second x)
                (secondSpatialCoordinateJet u first second x)) =
          ∑ pair : Fin 3 × Fin 3,
            ∫ x in unitCube,
              inner ℝ (secondCoordinateLowerCommutator velocity t pair.1 pair.2 x)
                (secondSpatialCoordinateJet u pair.1 pair.2 x) := by
            symm
            rw [Fintype.sum_prod_type]
        _ = ∑ word : Fin 2 → Fin 3,
            ∫ x in unitCube,
              inner ℝ (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
                (coordinateJetField velocity 2 word x t) := by
          exact Fintype.sum_equiv secondCoordinateWordEquiv _ _ (fun pair ↦ by
            apply setIntegral_congr_fun hcubeCompact.measurableSet
            intro x _hx
            have hword : secondCoordinateWordEquiv pair =
                secondCoordinateWord pair.1 pair.2 := rfl
            rw [hword]
            change _ = inner ℝ (secondCoordinateLowerCommutator velocity t pair.1 pair.2 x)
              (secondCoordinateJet velocity pair.1 pair.2 x t)
            rw [openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
              solution ht x pair.1 pair.2])

/-! ## Cofinal composition with the sharp-source curl current -/

/-- The constant Stokes-multiplier face of the compact sharp-source current has the exact signed
physical stretching work as its cofinal sum. -/
theorem hasSum_compactProjectedCoordinateH1ModeWork_eq_neg_coordinateH1StretchingWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        compactProjectedCoordinateH1ModeWork
          solution ha hab hbT frequency sourceTime)
      (-coordinateH1StretchingWork velocity
        (compactInteriorTime ha hab hbT sourceTime).1) := by
  let t : Ioo (0 : ℝ) T := compactInteriorTime ha hab hbT sourceTime
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let adv : InitialVelocity := actualAdvectionField u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have huPeriodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hadv : ContDiff ℝ (⊤ : ℕ∞) adv := actualAdvectionField_contDiff hu
  have hadvPeriodic : IsOnePeriodic adv :=
    actualAdvectionField_isOnePeriodic huPeriodic
  have hparseval := hasSum_stokes_sourceTestProductionReading_eq_firstDerivativeCubePairing
    u adv hu hadv huPeriodic hadvPeriodic
  have hphysical :=
    firstDerivativeCubePairing_actualAdvectionField_eq_coordinateH1StretchingWork
      solution t.2
  have hnegative := hparseval.neg
  change firstDerivativeCubePairing u adv =
    coordinateH1StretchingWork velocity t.1 at hphysical
  rw [hphysical] at hnegative
  refine hnegative.congr_fun (fun frequency ↦ ?_)
  unfold compactProjectedCoordinateH1ModeWork projectedCoordinateH1ModeWork
  dsimp only
  rw [sourceTestProductionReading_openSharpSource_eq_actualAdvection]
  change -torusStokesEigenvalue frequency *
      sourceTestProductionReading
        (vectorSpatialFourierCoeff u hu.continuous huPeriodic frequency)
        (vectorSpatialFourierCoeff adv hadv.continuous hadvPeriodic frequency) = _
  ring

/-- The squared Stokes-multiplier face has the exact signed nine-word lower commutator work as
its cofinal sum. -/
theorem hasSum_compactProjectedCoordinateH2ModeWork_eq_neg_coordinateH2LowerWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        compactProjectedCoordinateH2ModeWork
          solution ha hab hbT frequency sourceTime)
      (-coordinateH2LowerWork velocity
        (compactInteriorTime ha hab hbT sourceTime).1) := by
  let t : Ioo (0 : ℝ) T := compactInteriorTime ha hab hbT sourceTime
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let adv : InitialVelocity := actualAdvectionField u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have huPeriodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hadv : ContDiff ℝ (⊤ : ℕ∞) adv := actualAdvectionField_contDiff hu
  have hadvPeriodic : IsOnePeriodic adv :=
    actualAdvectionField_isOnePeriodic huPeriodic
  have hparseval := hasSum_stokes_sq_sourceTestProductionReading_eq_secondDerivativeCubePairing
    u adv hu hadv huPeriodic hadvPeriodic
  have hphysical :=
    secondDerivativeCubePairing_actualAdvectionField_eq_coordinateH2LowerWork
      solution t.2
  have hnegative := hparseval.neg
  change secondDerivativeCubePairing u adv =
    coordinateH2LowerWork velocity t.1 at hphysical
  rw [hphysical] at hnegative
  refine hnegative.congr_fun (fun frequency ↦ ?_)
  unfold compactProjectedCoordinateH2ModeWork projectedCoordinateH2ModeWork
  dsimp only
  rw [sourceTestProductionReading_openSharpSource_eq_actualAdvection]
  change -(torusStokesEigenvalue frequency ^ 2) *
      sourceTestProductionReading
        (vectorSpatialFourierCoeff u hu.continuous huPeriodic frequency)
        (vectorSpatialFourierCoeff adv hadv.continuous hadvPeriodic frequency) = _
  ring

/-- Public cofinal value of the order-one face.  This is the pointwise signed stretching current
whose time integral is the physical work chart used by the matched service. -/
theorem compactCofinalProjectedCoordinateH1At_eq_neg_coordinateH1StretchingWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalProjectedCoordinateH1At solution ha hab hbT sourceTime =
      -coordinateH1StretchingWork velocity
        (compactInteriorTime ha hab hbT sourceTime).1 := by
  unfold compactCofinalProjectedCoordinateH1At
  exact (hasSum_compactProjectedCoordinateH1ModeWork_eq_neg_coordinateH1StretchingWork
    solution ha hab hbT sourceTime).tsum_eq

/-- Public cofinal value of the distinct squared-multiplier/commutator face. -/
theorem compactCofinalProjectedCoordinateH2At_eq_neg_coordinateH2LowerWork
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalProjectedCoordinateH2At solution ha hab hbT sourceTime =
      -coordinateH2LowerWork velocity
        (compactInteriorTime ha hab hbT sourceTime).1 := by
  unfold compactCofinalProjectedCoordinateH2At
  exact (hasSum_compactProjectedCoordinateH2ModeWork_eq_neg_coordinateH2LowerWork
    solution ha hab hbT sourceTime).tsum_eq

/-- **[proved-derived; formal-checked] Exact source-specific physical/Fourier join.**  The cofinal
derivative-weighted sharp-source curl current is the literal signed coordinate `H2` nonlinear
production current.  The zero-mode fibre remains in the sum, both multiplier orders are separate,
Leray is removed by Hermitian transversality, and the two top-transport faces vanish only through
the established periodic solution law. -/
theorem compactCofinalH2CurlCompleteAt_eq_coordinateH2NonlinearProductionCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (sourceTime : ℝ) :
    compactCofinalH2CurlCompleteAt solution ha hab hbT sourceTime =
      coordinateH2NonlinearProductionCurrent velocity
        (compactInteriorTime ha hab hbT sourceTime).1 := by
  have hfirst :=
    hasSum_compactProjectedCoordinateH1ModeWork_eq_neg_coordinateH1StretchingWork
      solution ha hab hbT sourceTime
  have hsecond :=
    hasSum_compactProjectedCoordinateH2ModeWork_eq_neg_coordinateH2LowerWork
      solution ha hab hbT sourceTime
  have hcomplete := hfirst.add hsecond
  rw [compactCofinalH2CurlCompleteAt_eq_tsum_projectedOrderOne_add_orderTwo]
  rw [hcomplete.tsum_eq]
  unfold coordinateH2NonlinearProductionCurrent
  ring

/-! ## Audit -/

#print axioms bilinearDirectionRemainder_not_energyOrthogonal
#print axioms hasSum_stokes_sourceTestProductionReading_eq_firstDerivativeCubePairing
#print axioms hasSum_stokes_sq_sourceTestProductionReading_eq_secondDerivativeCubePairing
#print axioms firstDerivativeCubePairing_actualAdvectionField_eq_coordinateH1StretchingWork
#print axioms secondDerivativeCubePairing_actualAdvectionField_eq_coordinateH2LowerWork
#print axioms compactCofinalH2CurlCompleteAt_eq_coordinateH2NonlinearProductionCurrent

end Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
