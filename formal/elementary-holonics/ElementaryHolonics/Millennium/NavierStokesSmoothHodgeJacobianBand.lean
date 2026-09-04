import ElementaryHolonics.Millennium.NavierStokesHodgeBandReconstruction
import ElementaryHolonics.Millennium.NavierStokesDeLaValleePoussin
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Hodge Jacobian multiplier in an actual smooth adjacent-band chart

**[proved-derived]** This owner inserts the already checked nonzero-mode Hodge ascent into the
actual adjacent de la Vallée Poussin scale chart.  It retains all three indices of the resulting
kernel: Jacobian output component, derivative coordinate, and vorticity input component.

The return is exact at three levels:

* the multiplier is the adjacent scalar chart times the Hodge Jacobian mode;
* every physical kernel entry has that multiplier as its Fourier coefficient at every lattice
  frequency, including outside its finite support;
* physical convolution by the matrix kernel is exactly the finite Fourier multiplier action on a
  continuous vorticity field.

The elementary convolution estimate below exposes the precise analytic frontier.  A
radius-independent Jacobian-band estimate follows from a radius-independent `L1` bound for the 27
entry kernels.  The scalar de la Vallée Poussin `L1` estimate does not prove that assertion: the
entries contain the degree-zero Hodge factor `k_j k_l / |k|^2`.  No such periodic annular Hodge
kernel estimate is assumed here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFejerKernelConvolution
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := inferInstance

/-! ## The three-index Hodge multiplier -/

/-- The `input`-th column of the Hodge Jacobian multiplier, obtained by applying the already
checked Hodge ascent to the corresponding coordinate basis vector. -/
def hodgeJacobianMultiplierEntry
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) : ℂ :=
  hodgeJacobianMode frequency (Pi.single input 1) component coordinate

/-- The full adjacent-band Hodge multiplier acting on one vorticity coefficient. -/
def adjacentHodgeJacobianMode
    (radius : ℕ) (frequency : SpatialFrequency) (vorticityMode : ComplexVector) :
    ComplexJacobianArray :=
  (adjacentValleePoussinWeight radius frequency : ℂ) •
    hodgeJacobianMode frequency vorticityMode

/-- Hodge ascent is exactly the sum of its three addressed input columns. -/
theorem hodgeJacobianMode_eq_sum_multiplierEntry
    (frequency : SpatialFrequency) (vorticityMode : ComplexVector)
    (component coordinate : Fin 3) :
    hodgeJacobianMode frequency vorticityMode component coordinate =
      ∑ input : Fin 3,
        hodgeJacobianMultiplierEntry frequency component coordinate input *
          vorticityMode input := by
  fin_cases component <;> fin_cases coordinate <;>
    simp [hodgeJacobianMultiplierEntry, hodgeJacobianMode,
      nonzeroModeHodgeReconstruction, fourierJacobianMode, complexCross,
      complexFrequencyVector, crossProduct, Fin.sum_univ_succ] <;>
    ring

/-- The adjacent Hodge multiplier is the corresponding three-column matrix action. -/
theorem adjacentHodgeJacobianMode_eq_sum_multiplierEntry
    (radius : ℕ) (frequency : SpatialFrequency) (vorticityMode : ComplexVector)
    (component coordinate : Fin 3) :
    adjacentHodgeJacobianMode radius frequency vorticityMode component coordinate =
      ∑ input : Fin 3,
        ((adjacentValleePoussinWeight radius frequency : ℂ) *
          hodgeJacobianMultiplierEntry frequency component coordinate input) *
            vorticityMode input := by
  rw [adjacentHodgeJacobianMode, Pi.smul_apply, Pi.smul_apply,
    hodgeJacobianMode_eq_sum_multiplierEntry]
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _hinput
  ring

/-- The complete multiplier vanishes at the zero frequency. -/
@[simp]
theorem adjacentHodgeJacobianMode_zero
    (radius : ℕ) (vorticityMode : ComplexVector) :
    adjacentHodgeJacobianMode radius 0 vorticityMode = 0 := by
  simp [adjacentHodgeJacobianMode]

/-- The complete multiplier vanishes throughout the smaller plateau cube. -/
theorem adjacentHodgeJacobianMode_eq_zero_of_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1))
    (vorticityMode : ComplexVector) :
    adjacentHodgeJacobianMode radius frequency vorticityMode = 0 := by
  rw [adjacentHodgeJacobianMode,
    adjacentValleePoussinWeight_eq_zero_of_mem_inner radius hfrequency]
  simp

/-- The complete multiplier vanishes outside the next low-pass outer cube. -/
theorem adjacentHodgeJacobianMode_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉
      frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (vorticityMode : ComplexVector) :
    adjacentHodgeJacobianMode radius frequency vorticityMode = 0 := by
  rw [adjacentHodgeJacobianMode,
    adjacentValleePoussinWeight_eq_zero_of_not_mem_outer radius hfrequency]
  simp

/-- On every admitted solution slice, the smooth Hodge multiplier is exactly the same adjacent
multiplier applied to the actual Jacobian coefficient.  Thus the construction is not merely a
kernel with the right shape: it is the checked Hodge reconstruction composed with the existing
solution carrier. -/
theorem adjacentHodgeJacobianMode_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) (frequency : SpatialFrequency) :
    adjacentHodgeJacobianMode radius frequency
        (openPeriodicVorticityFourierMode solution t frequency) =
      (adjacentValleePoussinWeight radius frequency : ℂ) •
        openPeriodicJacobianFourierMode solution t frequency := by
  unfold adjacentHodgeJacobianMode
  rw [hodgeJacobianMode_openPeriodicVorticityFourierMode]

/-! ## The actual physical matrix kernel -/

/-- One scalar entry of the physical adjacent Hodge Jacobian kernel.  The finite synthesis uses
the exact outer support of the adjacent de la Vallée Poussin chart. -/
def adjacentHodgeJacobianKernelEntry
    (radius : ℕ) (component coordinate input : Fin 3) : C(SpatialTorus, ℂ) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (adjacentValleePoussinWeight radius frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input)
    (frequencyCube (valleePoussinOuterRadius (radius + 1)))

/-- Every entry has exactly the intended Hodge-times-adjacent multiplier coefficient at every
lattice frequency, not merely on the declared finite population. -/
theorem mFourierCoeff_adjacentHodgeJacobianKernelEntry
    (radius : ℕ) (component coordinate input : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (adjacentHodgeJacobianKernelEntry radius component coordinate input)
        frequency =
      (adjacentValleePoussinWeight radius frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input := by
  rw [adjacentHodgeJacobianKernelEntry,
    mFourierCoeff_finiteFourierSynthesis]
  split_ifs with hfrequency
  · rfl
  · rw [adjacentValleePoussinWeight_eq_zero_of_not_mem_outer
      radius hfrequency]
    simp

/-- The physical Hodge entry kernel has zero mean. -/
theorem integral_adjacentHodgeJacobianKernelEntry
    (radius : ℕ) (component coordinate input : Fin 3) :
    ∫ q : SpatialTorus,
      adjacentHodgeJacobianKernelEntry radius component coordinate input q = 0 := by
  have hcoeff := mFourierCoeff_adjacentHodgeJacobianKernelEntry
    radius component coordinate input 0
  rw [UnitAddTorus.mFourierCoeff] at hcoeff
  simpa [UnitAddTorus.mFourier_zero, hodgeJacobianMultiplierEntry] using hcoeff

/-! ## Character convolution and exact multiplier action -/

/-- The Fourier coefficient of a vector-valued field, evaluated at one input coordinate, is the
scalar Fourier coefficient of that coordinate field. -/
theorem mFourierCoeff_apply
    (field : C(SpatialTorus, ComplexVector)) (frequency : SpatialFrequency)
    (input : Fin 3) :
    UnitAddTorus.mFourierCoeff field frequency input =
      UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ field q input)
        frequency := by
  let integrand : C(SpatialTorus, ComplexVector) :=
    { toFun := fun q ↦ UnitAddTorus.mFourier (-frequency) q • field q
      continuous_toFun := by fun_prop }
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  let projection : ComplexVector →L[ℂ] ℂ := ContinuousLinearMap.proj input
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
  change projection (∫ q : SpatialTorus, integrand q) = _
  rw [← projection.integral_comp_comm hintegrable]
  apply integral_congr_ae
  filter_upwards [] with q
  rfl

/-- Convolution of one torus character against a continuous scalar field reads precisely the
matching Fourier coefficient and re-emits it at the observation point. -/
theorem mFourier_sub_apply
    (frequency : SpatialFrequency) (q y : SpatialTorus) :
    UnitAddTorus.mFourier frequency (q - y) =
      UnitAddTorus.mFourier frequency q *
        UnitAddTorus.mFourier (-frequency) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.add_apply, Pi.neg_apply, fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg,
    neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul, ← Finset.prod_mul_distrib]

/-- Convolution of one torus character against a continuous scalar field reads precisely the
matching Fourier coefficient and re-emits it at the observation point. -/
theorem integral_mFourier_mul_sub_eq
    (field : C(SpatialTorus, ℂ)) (frequency : SpatialFrequency)
    (q : SpatialTorus) :
    ∫ y : SpatialTorus,
        UnitAddTorus.mFourier frequency y * field (q - y) =
      UnitAddTorus.mFourier frequency q *
        UnitAddTorus.mFourierCoeff field frequency := by
  rw [← integral_sub_left_eq_self
    (fun z : SpatialTorus ↦
      UnitAddTorus.mFourier frequency z * field (q - z))
    (volume : Measure SpatialTorus) q]
  rw [UnitAddTorus.mFourierCoeff]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [sub_sub_cancel]
  change UnitAddTorus.mFourier frequency (q - y) * field y =
    UnitAddTorus.mFourier frequency q *
      (UnitAddTorus.mFourier (-frequency) y * field y)
  rw [mFourier_sub_apply]
  ring

/-- Physical convolution by all 27 scalar kernel entries, retaining the addressed input and
output coordinates. -/
def adjacentHodgeJacobianKernelConvolution
    (radius : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) : ComplexJacobianArray :=
  fun component coordinate ↦
    ∑ input : Fin 3,
      ∫ y : SpatialTorus,
        adjacentHodgeJacobianKernelEntry radius component coordinate input y *
          field (q - y) input

/-- **Exact physical/Fourier action identity.**  The matrix-kernel convolution is the finite
synthesis of the declared adjacent Hodge multiplier acting on the genuine Fourier coefficients
of the input field. -/
theorem adjacentHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis
    (radius : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) :
    adjacentHodgeJacobianKernelConvolution radius field q =
      finiteFourierSynthesis
        (fun frequency ↦ adjacentHodgeJacobianMode radius frequency
          (UnitAddTorus.mFourierCoeff field frequency))
        (frequencyCube (valleePoussinOuterRadius (radius + 1))) q := by
  funext component coordinate
  unfold adjacentHodgeJacobianKernelConvolution
    adjacentHodgeJacobianKernelEntry finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let modes := frequencyCube (valleePoussinOuterRadius (radius + 1))
  change
    (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        (∑ frequency ∈ modes,
          UnitAddTorus.mFourier frequency y *
            ((adjacentValleePoussinWeight radius frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          field (q - y) input) =
      ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency q *
          adjacentHodgeJacobianMode radius frequency
            (UnitAddTorus.mFourierCoeff field frequency) component coordinate
  calc
    (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        (∑ frequency ∈ modes,
          UnitAddTorus.mFourier frequency y *
            ((adjacentValleePoussinWeight radius frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          field (q - y) input) =
      ∑ input : Fin 3, ∑ frequency ∈ modes,
        ∫ y : SpatialTorus,
          (UnitAddTorus.mFourier frequency y *
            ((adjacentValleePoussinWeight radius frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                field (q - y) input := by
      apply Finset.sum_congr rfl
      intro input _hinput
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum]
      intro frequency _hfrequency
      exact continuousMap_integrable_on_compact
        { toFun := fun y : SpatialTorus ↦
            (UnitAddTorus.mFourier frequency y *
              ((adjacentValleePoussinWeight radius frequency : ℂ) *
                hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                  field (q - y) input
          continuous_toFun := by fun_prop }
    _ = ∑ frequency ∈ modes, ∑ input : Fin 3,
        ∫ y : SpatialTorus,
          (UnitAddTorus.mFourier frequency y *
            ((adjacentValleePoussinWeight radius frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                field (q - y) input := by
      rw [Finset.sum_comm]
    _ = ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency q *
          adjacentHodgeJacobianMode radius frequency
            (UnitAddTorus.mFourierCoeff field frequency) component coordinate := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      rw [adjacentHodgeJacobianMode_eq_sum_multiplierEntry]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      have hcharacter := integral_mFourier_mul_sub_eq
        { toFun := fun y : SpatialTorus ↦ field y input
          continuous_toFun := by fun_prop }
        frequency q
      rw [mFourierCoeff_apply field frequency input]
      let coefficient : ℂ :=
        (adjacentValleePoussinWeight radius frequency : ℂ) *
          hodgeJacobianMultiplierEntry frequency component coordinate input
      calc
        ∫ y : SpatialTorus,
            UnitAddTorus.mFourier frequency y * coefficient *
              field (q - y) input =
            ∫ y : SpatialTorus,
              coefficient *
                (UnitAddTorus.mFourier frequency y * field (q - y) input) := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ =
            coefficient *
              (∫ y : SpatialTorus,
                UnitAddTorus.mFourier frequency y * field (q - y) input) := by
          rw [integral_const_mul]
        _ = coefficient *
            (UnitAddTorus.mFourier frequency q *
              UnitAddTorus.mFourierCoeff
                (fun y : SpatialTorus ↦ field y input) frequency) := by
          congr 1
        _ = UnitAddTorus.mFourier frequency q *
            (coefficient *
              UnitAddTorus.mFourierCoeff
                (fun y : SpatialTorus ↦ field y input) frequency) := by ring

/-! ## The exact `L1` frontier -/

/-- The total entrywise physical `L1` mass of the matrix kernel.  This is the precise receiver
needed by the elementary `L∞ → L∞` convolution estimate. -/
def adjacentHodgeJacobianKernelL1 (radius : ℕ) : ℝ :=
  ∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
    ∫ y : SpatialTorus,
      ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖

/-- The matrix-kernel convolution is bounded pointwise by its exact total physical `L1` mass and
the uniform norm of the vorticity field. -/
theorem norm_adjacentHodgeJacobianKernelConvolution_le
    (radius : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) :
    ‖adjacentHodgeJacobianKernelConvolution radius field q‖ ≤
      adjacentHodgeJacobianKernelL1 radius * ‖field‖ := by
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (by
      unfold adjacentHodgeJacobianKernelL1
      positivity) (norm_nonneg field))]
  intro component
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (by
      unfold adjacentHodgeJacobianKernelL1
      positivity) (norm_nonneg field))]
  intro coordinate
  unfold adjacentHodgeJacobianKernelConvolution
  calc
    ‖∑ input : Fin 3,
        ∫ y : SpatialTorus,
          adjacentHodgeJacobianKernelEntry radius component coordinate input y *
            field (q - y) input‖ ≤
        ∑ input : Fin 3,
          ‖∫ y : SpatialTorus,
            adjacentHodgeJacobianKernelEntry radius component coordinate input y *
              field (q - y) input‖ := norm_sum_le _ _
    _ ≤ ∑ input : Fin 3,
          (∫ y : SpatialTorus,
            ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖) *
              ‖field‖ := by
      apply Finset.sum_le_sum
      intro input _hinput
      have hmajorant : Integrable
          (fun y : SpatialTorus ↦
            ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖ *
              ‖field‖) :=
        continuousMap_integrable_on_compact
          { toFun := fun y : SpatialTorus ↦
              ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖ *
                ‖field‖
            continuous_toFun := by fun_prop }
      calc
        ‖∫ y : SpatialTorus,
            adjacentHodgeJacobianKernelEntry radius component coordinate input y *
              field (q - y) input‖ ≤
            ∫ y : SpatialTorus,
              ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖ *
                ‖field‖ := by
          apply norm_integral_le_of_norm_le hmajorant
          filter_upwards [] with y
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (f := field (q - y)) input).trans
              (field.norm_coe_le_norm (q - y))) (norm_nonneg _)
        _ = (∫ y : SpatialTorus,
              ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖) *
                ‖field‖ := by rw [integral_mul_const]
    _ = (∑ input : Fin 3,
          ∫ y : SpatialTorus,
            ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖) *
              ‖field‖ := by rw [Finset.sum_mul]
    _ ≤ adjacentHodgeJacobianKernelL1 radius * ‖field‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
      unfold adjacentHodgeJacobianKernelL1
      calc
        (∑ input : Fin 3,
            ∫ y : SpatialTorus,
              ‖adjacentHodgeJacobianKernelEntry radius component coordinate input y‖) ≤
            ∑ coordinate' : Fin 3, ∑ input : Fin 3,
              ∫ y : SpatialTorus,
                ‖adjacentHodgeJacobianKernelEntry radius component coordinate' input y‖ := by
          apply Finset.single_le_sum
            (s := Finset.univ)
            (f := fun coordinate' : Fin 3 ↦ ∑ input : Fin 3,
              ∫ y : SpatialTorus,
                ‖adjacentHodgeJacobianKernelEntry radius component coordinate' input y‖)
          · intro coordinate' _hcoordinate'
            apply Finset.sum_nonneg
            intro input _hinput
            exact integral_nonneg fun y ↦ norm_nonneg _
          · exact Finset.mem_univ coordinate
        _ ≤ ∑ component' : Fin 3, ∑ coordinate' : Fin 3,
              ∑ input : Fin 3,
                ∫ y : SpatialTorus,
                  ‖adjacentHodgeJacobianKernelEntry radius component' coordinate' input y‖ := by
          apply Finset.single_le_sum
            (s := Finset.univ)
            (f := fun component' : Fin 3 ↦ ∑ coordinate' : Fin 3,
              ∑ input : Fin 3,
                ∫ y : SpatialTorus,
                  ‖adjacentHodgeJacobianKernelEntry radius component' coordinate' input y‖)
          · intro component' _hcomponent'
            apply Finset.sum_nonneg
            intro coordinate' _hcoordinate'
            apply Finset.sum_nonneg
            intro input _hinput
            exact integral_nonneg fun y ↦ norm_nonneg _
          · exact Finset.mem_univ component

/-- Actual smooth adjacent Hodge band of an admitted solution slice. -/
def openPeriodicSmoothHodgeJacobianBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) : C(SpatialTorus, ComplexJacobianArray) :=
  finiteFourierSynthesis
    (fun frequency ↦ adjacentHodgeJacobianMode radius frequency
      (openPeriodicVorticityFourierMode solution t frequency))
    (frequencyCube (valleePoussinOuterRadius (radius + 1)))

/-- The reconstructed smooth band is exactly the adjacent multiplier of the actual Jacobian
coefficients on the same finite outer population. -/
theorem openPeriodicSmoothHodgeJacobianBand_eq_actualAdjacentMultiplier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    openPeriodicSmoothHodgeJacobianBand solution t radius =
      finiteFourierSynthesis
        (fun frequency ↦
          (adjacentValleePoussinWeight radius frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (valleePoussinOuterRadius (radius + 1))) := by
  unfold openPeriodicSmoothHodgeJacobianBand
  congr 1
  funext frequency
  exact adjacentHodgeJacobianMode_openPeriodicVorticityFourierMode
    solution t radius frequency

/-- The actual smooth Hodge band is exactly physical matrix-kernel convolution against the
actual continuous vorticity slice. -/
theorem openPeriodicSmoothHodgeJacobianBand_eq_kernelConvolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    openPeriodicSmoothHodgeJacobianBand solution t radius q =
      adjacentHodgeJacobianKernelConvolution radius
        (complexTorusVorticitySlice solution t) q := by
  rw [adjacentHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis]
  rfl

/-- Honest pointwise actual-slice estimate at the exact kernel `L1` receiver.  Establishing a
radius-independent numerical upper bound for that receiver is the remaining annular periodic
Hodge-kernel inequality. -/
theorem norm_openPeriodicSmoothHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicSmoothHodgeJacobianBand solution t radius q‖ ≤
      adjacentHodgeJacobianKernelL1 radius * criticalVorticityRate solution t.1 := by
  rw [openPeriodicSmoothHodgeJacobianBand_eq_kernelConvolution]
  refine (norm_adjacentHodgeJacobianKernelConvolution_le radius
    (complexTorusVorticitySlice solution t) q).trans ?_
  have hfield : ‖complexTorusVorticitySlice solution t‖ ≤
      criticalVorticityRate solution t.1 := by
    rw [criticalVorticityRate_eq solution t.2]
    apply (ContinuousMap.norm_le _
      (norm_nonneg (torusVorticityEvolution solution t))).mpr
    intro q'
    exact (norm_complexifySpace_le
      (torusVorticityEvolution solution t q')).trans
        ((torusVorticityEvolution solution t).norm_coe_le_norm q')
  have hL1 : 0 ≤ adjacentHodgeJacobianKernelL1 radius := by
    unfold adjacentHodgeJacobianKernelL1
    positivity
  exact mul_le_mul_of_nonneg_left hfield hL1

section Audit

#print axioms hodgeJacobianMode_eq_sum_multiplierEntry
#print axioms mFourierCoeff_adjacentHodgeJacobianKernelEntry
#print axioms integral_mFourier_mul_sub_eq
#print axioms adjacentHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis
#print axioms norm_adjacentHodgeJacobianKernelConvolution_le
#print axioms openPeriodicSmoothHodgeJacobianBand_eq_actualAdjacentMultiplier
#print axioms openPeriodicSmoothHodgeJacobianBand_eq_kernelConvolution
#print axioms norm_openPeriodicSmoothHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
