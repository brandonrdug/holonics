import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianReceiver
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors

/-!
# The entrywise Hodge face returns the actual Jacobian receiver

**[proved-derived]** The annular Hodge owner retains the nine complexified matrix entries of a
spatial Jacobian, whereas coordinate continuation consumes the operator norm of the complete real
Fréchet derivative.  This owner constructs the missing receiver transition without identifying
those two norms.

The source occurrence is a real continuous linear endomorphism of the three-dimensional spatial
carrier.  Its complexified matrix retains every output-component/derivative-coordinate face.  A
finite basis expansion proves the explicit comparison `‖D‖ ≤ 9 ‖matrix(D)‖`.  The same transition
is then installed pointwise and at the genuine-torus supremum receiver for an admitted solution
slice.  The constant is deliberately coarse; no harmonic-analysis or continuation conclusion is
assumed here.
-/

noncomputable section

open Set
open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Every addressed real Jacobian entry, complexified but otherwise unchanged. -/
def complexJacobianArrayOfCLM (D : Space →L[ℝ] Space) : ComplexJacobianArray :=
  fun component coordinate ↦
    (D (spatialBasisVector coordinate) component : ℂ)

/-- The Euclidean norm of one column is bounded by three times the entrywise supremum receiver. -/
theorem norm_apply_spatialBasisVector_le_three_mul_arrayNorm
    (D : Space →L[ℝ] Space) (coordinate : Fin 3) :
    ‖D (spatialBasisVector coordinate)‖ ≤
      3 * ‖complexJacobianArrayOfCLM D‖ := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let column : Space := D (spatialBasisVector coordinate)
  have hrepr : ∑ component : Fin 3, (column component) • b component = column := by
    simpa [b, EuclideanSpace.basisFun_repr] using b.sum_repr column
  change ‖column‖ ≤ 3 * ‖complexJacobianArrayOfCLM D‖
  rw [← hrepr]
  calc
    ‖∑ component : Fin 3, (column component) • b component‖ ≤
        ∑ component : Fin 3, ‖(column component) • b component‖ :=
      norm_sum_le _ _
    _ = ∑ component : Fin 3, ‖complexJacobianArrayOfCLM D component coordinate‖ := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      change ‖(column component) • b component‖ =
        ‖((column component : ℝ) : ℂ)‖
      rw [norm_smul, b.norm_eq_one, mul_one, Real.norm_eq_abs,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ _component : Fin 3, ‖complexJacobianArrayOfCLM D‖ := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact (norm_le_pi_norm
        (complexJacobianArrayOfCLM D component) coordinate).trans
          (norm_le_pi_norm (complexJacobianArrayOfCLM D) component)
    _ = 3 * ‖complexJacobianArrayOfCLM D‖ := by
      simp

/-- In three dimensions, the complete operator norm is controlled by the retained entry array.
The factor nine is the two finite basis populations (`3 × 3`), not an asserted norm identity. -/
theorem norm_clm_le_nine_mul_complexJacobianArrayNorm
    (D : Space →L[ℝ] Space) :
    ‖D‖ ≤ 9 * ‖complexJacobianArrayOfCLM D‖ := by
  refine ContinuousLinearMap.opNorm_le_bound D (by positivity) ?_
  intro v
  have hcoordinates : ∀ coordinate : Fin 3, |v coordinate| ≤ ‖v‖ := by
    intro coordinate
    exact abs_component_le_norm v coordinate
  calc
    ‖D v‖ ≤ ‖v‖ * ∑ coordinate : Fin 3,
        ‖D (spatialBasisVector coordinate)‖ :=
      norm_clm_apply_le_bound_mul_sum_coordinate D v ‖v‖ hcoordinates
    _ ≤ ‖v‖ * ∑ _coordinate : Fin 3,
        (3 * ‖complexJacobianArrayOfCLM D‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact norm_apply_spatialBasisVector_le_three_mul_arrayNorm D coordinate
    _ = (9 * ‖complexJacobianArrayOfCLM D‖) * ‖v‖ := by
      simp
      ring

/-- The complete complexified Jacobian-entry field on the genuine spatial torus. -/
def openPeriodicTorusJacobianArraySlice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, ComplexJacobianArray) where
  toFun := fun q ↦ complexJacobianArrayOfCLM
    (openPeriodicTorusJacobianSlice solution t q)
  continuous_toFun := by
    unfold complexJacobianArrayOfCLM
    fun_prop

/-- Pullback along the quotient returns every literal complexified Euclidean Jacobian entry. -/
@[simp]
theorem openPeriodicTorusJacobianArraySlice_projection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (x : Space) (component coordinate : Fin 3) :
    openPeriodicTorusJacobianArraySlice solution t (euclideanToSpatialTorus x)
        component coordinate =
      (fderiv ℝ (fun y ↦ velocity y t.1) x
          (spatialBasisVector coordinate) component : ℂ) := by
  simp [openPeriodicTorusJacobianArraySlice, complexJacobianArrayOfCLM,
    openPeriodicTorusJacobianSlice_projection]

/-- Each torus-array entry is literally the quotient lift used to define the corresponding
actual Jacobian Fourier coefficient. -/
theorem openPeriodicTorusJacobianArraySlice_apply_eq_periodicTorusLift
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (component coordinate : Fin 3) :
    openPeriodicTorusJacobianArraySlice solution t q component coordinate =
      periodicTorusLift
        (complexJacobianComponent (fun x ↦ velocity x t.1) component coordinate)
        (continuous_complexJacobianComponent
          (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
          component coordinate)
        (isOnePeriodic_complexJacobianComponent
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
          component coordinate) q := by
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
  simp [complexJacobianComponent, velocityJacobianAt, jacobianMatrix_apply,
    spatialBasisVector]

/-- Fourier integration commutes with both finite coordinate projections of the retained
Jacobian-entry array. -/
theorem mFourierCoeff_apply_apply
    (field : C(SpatialTorus, ComplexJacobianArray))
    (frequency : SpatialFrequency) (component coordinate : Fin 3) :
    UnitAddTorus.mFourierCoeff field frequency component coordinate =
      UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ field q component coordinate) frequency := by
  let integrand : C(SpatialTorus, ComplexJacobianArray) :=
    { toFun := fun q ↦ UnitAddTorus.mFourier (-frequency) q • field q
      continuous_toFun := by fun_prop }
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  let firstProjection : ComplexJacobianArray →L[ℂ] (Fin 3 → ℂ) :=
    ContinuousLinearMap.proj component
  let secondProjection : (Fin 3 → ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.proj coordinate
  let projection : ComplexJacobianArray →L[ℂ] ℂ :=
    secondProjection.comp firstProjection
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
  have hprojection := projection.integral_comp_comm hintegrable
  simpa [projection, firstProjection, secondProjection, integrand] using
    hprojection.symm

/-- The Fourier receiver of the complete actual Jacobian array is exactly the established
nine-entry `openPeriodicJacobianFourierMode`; no finite cutoff or reconstruction premise enters. -/
theorem mFourierCoeff_openPeriodicTorusJacobianArraySlice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicTorusJacobianArraySlice solution t) frequency =
      openPeriodicJacobianFourierMode solution t frequency := by
  funext component coordinate
  rw [mFourierCoeff_apply_apply]
  unfold openPeriodicJacobianFourierMode actualJacobianFourierMode
    torusSpatialFourierCoeff
  congr 1
  funext q
  exact openPeriodicTorusJacobianArraySlice_apply_eq_periodicTorusLift
    solution t q component coordinate

/-- At every torus point, the actual operator-valued Jacobian is controlled by its complete
entrywise Hodge receiver. -/
theorem norm_openPeriodicTorusJacobianSlice_le_nine_mul_arrayNorm
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianSlice solution t q‖ ≤
      9 * ‖openPeriodicTorusJacobianArraySlice solution t q‖ :=
  norm_clm_le_nine_mul_complexJacobianArrayNorm _

/-- The genuine-torus supremum Jacobian receiver is bounded by nine times the supremum norm of
the complete entry field.  This is the exact port through which the 27 Hodge kernels enter the
coordinate continuation estimate. -/
theorem coordinateJacobianReceiver_le_nine_mul_arraySliceNorm
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateJacobianReceiver solution t ≤
      9 * ‖openPeriodicTorusJacobianArraySlice solution ⟨t, ht⟩‖ := by
  rw [coordinateJacobianReceiver_eq solution ht]
  exact (ContinuousMap.norm_le _ (by positivity)).mpr (fun q ↦
    (norm_openPeriodicTorusJacobianSlice_le_nine_mul_arrayNorm
      solution ⟨t, ht⟩ q).trans
        (mul_le_mul_of_nonneg_left
          ((openPeriodicTorusJacobianArraySlice solution ⟨t, ht⟩).norm_coe_le_norm q)
          (by norm_num)))

section Audit

#print axioms norm_apply_spatialBasisVector_le_three_mul_arrayNorm
#print axioms norm_clm_le_nine_mul_complexJacobianArrayNorm
#print axioms openPeriodicTorusJacobianArraySlice_projection
#print axioms mFourierCoeff_openPeriodicTorusJacobianArraySlice
#print axioms coordinateJacobianReceiver_le_nine_mul_arraySliceNorm

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
