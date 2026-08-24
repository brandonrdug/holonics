import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction

/-!
# Complete Fourier reconstruction of the actual torus Jacobian

**[proved-derived]** The full genuine-torus Jacobian entry field of every strict-interior smooth
solution slice is the uniformly convergent Fourier series of its actual derivative coefficients.
This closes the infinite-population attachment which a finite Hodge band alone cannot supply.

The proof first mounts the smooth slice in the complete native weighted `H³` carrier.  Its first
Fourier moment is absolutely summable, so every differentiated coefficient population is
summable.  Mathlib's multivariate torus Fourier basis then returns uniform convergence to the
literal continuous entry field.  No cutoff, terminal value, or logarithmic estimate is assumed.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- One retained scalar entry of the complete actual torus Jacobian field. -/
def openPeriodicTorusJacobianEntry
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) : C(SpatialTorus, ℂ) where
  toFun := fun q ↦
    openPeriodicTorusJacobianArraySlice solution t q component coordinate
  continuous_toFun := by fun_prop

/-- The scalar entry coefficient is the corresponding face of the established complete Jacobian
coefficient array. -/
theorem mFourierCoeff_openPeriodicTorusJacobianEntry
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicTorusJacobianEntry solution t component coordinate) frequency =
      openPeriodicJacobianFourierMode solution t frequency component coordinate := by
  have harray := congrFun
    (congrFun
      (mFourierCoeff_openPeriodicTorusJacobianArraySlice solution t frequency)
      component) coordinate
  rw [mFourierCoeff_apply_apply] at harray
  exact harray

/-- Every actual Jacobian-entry coefficient population is absolutely summable.  This spends only
the first Fourier moment already carried by the native smooth-slice `H³` receiver. -/
theorem summable_norm_openPeriodicJacobianFourierMode_entry
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      ‖openPeriodicJacobianFourierMode solution t frequency component coordinate‖ := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 u hu hperiodic
  have hmoment :=
    summable_coordinate_mul_norm_nativeUnweightedComponent state component coordinate
  have hscaled := hmoment.mul_left (2 * Real.pi)
  apply hscaled.congr
  intro frequency
  have hcoefficient := actualJacobianFourierMode_eq_multiplier
    u (hu.of_le (by norm_num)) hperiodic frequency component coordinate
  change 2 * Real.pi *
      (|(frequency coordinate : ℝ)| *
        ‖nativeUnweightedComponent state component frequency‖) =
    ‖actualJacobianFourierMode u (hu.of_le (by norm_num)) hperiodic frequency
      component coordinate‖
  rw [hcoefficient]
  have hunweighted := unweighted_smoothSliceVectorWeightedH3_apply
    u hu hperiodic component frequency
  change nativeUnweightedComponent state component frequency = _ at hunweighted
  rw [hunweighted]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, Complex.norm_intCast]
  ring

/-- Hence the Fourier coefficients of the literal scalar Jacobian entry are summable. -/
theorem summable_mFourierCoeff_openPeriodicTorusJacobianEntry
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) :
    Summable (UnitAddTorus.mFourierCoeff
      (openPeriodicTorusJacobianEntry solution t component coordinate)) := by
  apply Summable.of_norm
  simpa only [mFourierCoeff_openPeriodicTorusJacobianEntry] using
    summable_norm_openPeriodicJacobianFourierMode_entry
      solution t component coordinate

/-- **Complete uniform reconstruction.**  The actual continuous Jacobian entry is the uniform
sum of all its addressed lattice pins. -/
theorem hasSum_openPeriodicJacobianFourierSeries
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        openPeriodicJacobianFourierMode solution t frequency component coordinate •
          UnitAddTorus.mFourier frequency)
      (openPeriodicTorusJacobianEntry solution t component coordinate) := by
  have hsum := UnitAddTorus.hasSum_mFourier_series_of_summable
    (summable_mFourierCoeff_openPeriodicTorusJacobianEntry
      solution t component coordinate)
  simpa only [mFourierCoeff_openPeriodicTorusJacobianEntry] using hsum

/-- Pointwise form of the same complete reconstruction at every genuine-torus receiver. -/
theorem hasSum_openPeriodicJacobianFourierSeries_apply
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) (q : SpatialTorus) :
    HasSum
      (fun frequency : SpatialFrequency ↦
        openPeriodicJacobianFourierMode solution t frequency component coordinate *
          UnitAddTorus.mFourier frequency q)
      (openPeriodicTorusJacobianArraySlice solution t q component coordinate) := by
  simpa [openPeriodicTorusJacobianEntry] using
    (ContinuousMap.evalCLM ℂ q).hasSum
      (hasSum_openPeriodicJacobianFourierSeries solution t component coordinate)

/-! ## Every finite aperture retains its complete unresolved tail -/

/-- The exact Fourier reconstruction fibre outside one declared finite mode population. -/
def openPeriodicJacobianFourierTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency)
    (component coordinate : Fin 3) (q : SpatialTorus) : ℂ :=
  ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
    openPeriodicJacobianFourierMode solution t frequency.1 component coordinate *
      UnitAddTorus.mFourier frequency.1 q

/-- A finite Jacobian projector is exactly the finite part of the complete entry series. -/
theorem openPeriodicJacobianBandProjector_apply_eq_sum_entry
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency)
    (component coordinate : Fin 3) (q : SpatialTorus) :
    openPeriodicJacobianBandProjector solution t modes q component coordinate =
      ∑ frequency ∈ modes,
        openPeriodicJacobianFourierMode solution t frequency component coordinate *
          UnitAddTorus.mFourier frequency q := by
  unfold openPeriodicJacobianBandProjector finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  ring

/-- Exact aperture decomposition of the literal torus Jacobian entry.  The complement is a
convergent addressed population, not a discarded error scalar. -/
theorem openPeriodicTorusJacobianArraySlice_eq_band_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency)
    (component coordinate : Fin 3) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q component coordinate =
      openPeriodicJacobianBandProjector solution t modes q component coordinate +
        openPeriodicJacobianFourierTail solution t modes component coordinate q := by
  let series : SpatialFrequency → ℂ := fun frequency ↦
    openPeriodicJacobianFourierMode solution t frequency component coordinate *
      UnitAddTorus.mFourier frequency q
  have hsum : HasSum series
      (openPeriodicTorusJacobianArraySlice solution t q component coordinate) :=
    hasSum_openPeriodicJacobianFourierSeries_apply
      solution t component coordinate q
  have hsplit := hsum.summable.sum_add_tsum_subtype_compl modes
  rw [openPeriodicJacobianBandProjector_apply_eq_sum_entry]
  exact hsum.tsum_eq.symm.trans hsplit.symm

/-- The norm of the retained tail is bounded by the exact tail population of coefficient norms.
The torus characters cost one and do not erase any frequency address. -/
theorem norm_openPeriodicJacobianFourierTail_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency)
    (component coordinate : Fin 3) (q : SpatialTorus) :
    ‖openPeriodicJacobianFourierTail solution t modes component coordinate q‖ ≤
      ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
        ‖openPeriodicJacobianFourierMode solution t frequency.1 component coordinate‖ := by
  unfold openPeriodicJacobianFourierTail
  have hfull :=
    summable_norm_openPeriodicJacobianFourierMode_entry solution t component coordinate
  have hsubtype := hfull.subtype
    {frequency : SpatialFrequency | frequency ∉ modes}
  have hcharacter (frequency : SpatialFrequency) :
      ‖UnitAddTorus.mFourier frequency q‖ = 1 := by
    simp [UnitAddTorus.mFourier, norm_prod]
  have hterms : Summable fun frequency :
      {frequency : SpatialFrequency // frequency ∉ modes} ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 component coordinate *
        UnitAddTorus.mFourier frequency.1 q‖ := by
    simpa only [Function.comp_apply, norm_mul, hcharacter, mul_one]
      using hsubtype
  calc
    ‖∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
        openPeriodicJacobianFourierMode solution t frequency.1 component coordinate *
          UnitAddTorus.mFourier frequency.1 q‖ ≤
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
          ‖openPeriodicJacobianFourierMode solution t frequency.1 component coordinate *
            UnitAddTorus.mFourier frequency.1 q‖ :=
      norm_tsum_le_tsum_norm hterms
    _ = ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
        ‖openPeriodicJacobianFourierMode solution t frequency.1 component coordinate‖ := by
      apply tsum_congr
      intro frequency
      rw [norm_mul, hcharacter, mul_one]

/-- All nine complement populations retained as one Jacobian-array reconstruction fibre. -/
def openPeriodicJacobianArrayFourierTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ComplexJacobianArray :=
  fun component coordinate ↦
    openPeriodicJacobianFourierTail solution t modes component coordinate q

/-- The finite array projector plus its addressed infinite complement is the literal complete
Jacobian-entry field. -/
theorem openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q =
      openPeriodicJacobianBandProjector solution t modes q +
        openPeriodicJacobianArrayFourierTail solution t modes q := by
  funext component coordinate
  exact openPeriodicTorusJacobianArraySlice_eq_band_add_tail
    solution t modes component coordinate q

/-- The exact nine-face coefficient-tail mass.  It is a later scalar receiver of the complete
subtype-indexed complement, not its replacement. -/
def openPeriodicJacobianCoefficientTailMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) : ℝ :=
  ‖fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
    ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
      ‖openPeriodicJacobianFourierMode solution t frequency.1 component coordinate‖‖

/-- The complete complement array is pointwise bounded by its exact coefficient-tail mass. -/
theorem norm_openPeriodicJacobianArrayFourierTail_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicJacobianArrayFourierTail solution t modes q‖ ≤
      openPeriodicJacobianCoefficientTailMass solution t modes := by
  rw [pi_norm_le_iff_of_nonneg (by
    unfold openPeriodicJacobianCoefficientTailMass
    positivity)]
  intro component
  rw [pi_norm_le_iff_of_nonneg (by
    unfold openPeriodicJacobianCoefficientTailMass
    positivity)]
  intro coordinate
  have hnonneg :
      0 ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖ := tsum_nonneg fun _ ↦ norm_nonneg _
  calc
    ‖openPeriodicJacobianArrayFourierTail solution t modes q component coordinate‖ ≤
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
          ‖openPeriodicJacobianFourierMode solution t frequency.1
            component coordinate‖ :=
      norm_openPeriodicJacobianFourierTail_le
        solution t modes component coordinate q
    _ = ‖(fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component coordinate‖) component coordinate‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ ‖(fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component coordinate‖) component‖ :=
      norm_le_pi_norm
        (fun innerCoordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component innerCoordinate‖) coordinate
    _ ≤ ‖fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component coordinate‖‖ :=
      norm_le_pi_norm
        (fun outerComponent : Fin 3 ↦ fun outerCoordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ modes},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              outerComponent outerCoordinate‖) component

/-- Every finite Fourier aperture now bounds the actual coordinate Jacobian receiver by the norm
of the retained finite array plus its complete coefficient reconstruction fibre. -/
theorem coordinateJacobianReceiver_le_band_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (modes : Finset SpatialFrequency) :
    coordinateJacobianReceiver solution t ≤
      9 * (‖openPeriodicJacobianBandProjector solution ⟨t, ht⟩ modes‖ +
        openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩ modes) := by
  refine (coordinateJacobianReceiver_le_nine_mul_arraySliceNorm
    solution ht).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _)
    (by unfold openPeriodicJacobianCoefficientTailMass; positivity))).mpr
  intro q
  rw [openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((openPeriodicJacobianBandProjector solution ⟨t, ht⟩ modes).norm_coe_le_norm q)
      (norm_openPeriodicJacobianArrayFourierTail_le
        solution ⟨t, ht⟩ modes q))

section Audit

#print axioms mFourierCoeff_openPeriodicTorusJacobianEntry
#print axioms summable_norm_openPeriodicJacobianFourierMode_entry
#print axioms hasSum_openPeriodicJacobianFourierSeries
#print axioms hasSum_openPeriodicJacobianFourierSeries_apply
#print axioms openPeriodicTorusJacobianArraySlice_eq_band_add_tail
#print axioms norm_openPeriodicJacobianFourierTail_le
#print axioms openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail
#print axioms coordinateJacobianReceiver_le_band_add_tail

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
