import ElementaryHolonics.Foundation.CoordinateHaarReceiver
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeLowScale
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers

/-!
# The dyadic Hodge Haar receiver

This owner composes the exact eight subset Abel identities with the coordinate Haar calculus.
It isolates the final coefficient-side obligation as a typed `DyadicHodgeSubsetMassReturn` and
proves that any inhabitant yields a scale-uniform physical `L¹` bound with explicit factor `8`
per Hodge entry.  No singular character factor is divided.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver

open MeasureTheory
open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := inferInstance

private theorem spatialTorus_volume_eq_standardAddCircleVolume :
    @volume (UnitAddTorus (Fin 3))
        (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
          (fun _ ↦ ⟨AddCircle.haarAddCircle⟩)) =
      @volume (UnitAddTorus (Fin 3))
        (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
          (fun _ ↦ AddCircle.measureSpace 1)) := by
  change Measure.pi (fun _ : Fin 3 ↦ AddCircle.haarAddCircle) =
    Measure.pi (fun _ : Fin 3 ↦
      @volume UnitAddCircle (AddCircle.measureSpace 1))
  congr 1
  funext axis
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- The exact coefficient-side return required from one dyadic Hodge entry.  Every Boolean face
has the scale predicted by the near/far exponent balance. -/
def DyadicHodgeSubsetMassReturn
    (scale : ℕ) (component coordinate input : Fin 3) (constant : ℝ) : Prop :=
  0 ≤ constant ∧ ∀ face : CoordinateFace 3,
    dyadicHodgeSubsetMass face scale component coordinate input ≤
      constant * coordinateSubsetScale (dyadicRadius scale : ℝ) face

/-- The complex Abel factor has exactly the product of the addressed real chord squares as its
norm. -/
theorem norm_dyadicHodgeSubsetGap_eq_chordProduct
    (face : CoordinateFace 3) (q : SpatialTorus) :
    ‖dyadicHodgeSubsetGap face q‖ =
      ∏ axis ∈ face, unitCircleChord (q axis) ^ 2 := by
  classical
  unfold dyadicHodgeSubsetGap unitCircleChord
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro axis _haxis
  rw [norm_pow]

/-- All eight coefficient-mass returns imply the receiver-selected pointwise penalty bound. -/
theorem norm_dyadicHodgeJacobianKernelEntry_le_penaltyProduct
    (scale : ℕ) (component coordinate input : Fin 3) {constant : ℝ}
    (hreturn : DyadicHodgeSubsetMassReturn scale component coordinate input constant)
    (q : SpatialTorus) :
    ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖ ≤
      constant * ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (q axis) := by
  change ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖ ≤
    constant * ∏ axis,
      scalarHaarPenalty (dyadicRadius scale : ℝ) (unitCircleChord (q axis))
  apply value_le_constant_mul_penaltyProduct_of_all_subset_returns
    (show 0 < (dyadicRadius scale : ℝ) by
      exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale))
  intro face
  have hab := norm_dyadicHodgeSubsetGap_mul_kernelEntry_le_mass
    face scale component coordinate input q
  rw [norm_mul, norm_dyadicHodgeSubsetGap_eq_chordProduct] at hab
  exact hab.trans (hreturn.2 face)

/-- One returned entry has physical Haar `L¹` mass at most eight times its common subset
constant. -/
theorem integral_norm_dyadicHodgeJacobianKernelEntry_le_eight_mul
    (scale : ℕ) (component coordinate input : Fin 3) {constant : ℝ}
    (hreturn : DyadicHodgeSubsetMassReturn scale component coordinate input constant) :
    (∫ q : SpatialTorus,
      ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖) ≤
        8 * constant := by
  let kernelNorm : SpatialTorus → ℝ := fun q ↦
    ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖
  let penaltyProduct : SpatialTorus → ℝ := fun q ↦
    constant * ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (q axis)
  have hkernel : Integrable kernelNorm :=
    continuousMap_integrable_on_compact
      { toFun := kernelNorm
        continuous_toFun := by dsimp [kernelNorm]; fun_prop }
  have hpenalty : Integrable penaltyProduct :=
    continuousMap_integrable_on_compact
      { toFun := penaltyProduct
        continuous_toFun := by
          dsimp [penaltyProduct]
          apply continuous_const.mul
          apply continuous_finset_prod
          intro axis _haxis
          exact (continuous_oneCircleHaarPenalty _).comp (continuous_apply axis) }
  have hpointwise : kernelNorm ≤ penaltyProduct := by
    intro q
    exact norm_dyadicHodgeJacobianKernelEntry_le_penaltyProduct
      scale component coordinate input hreturn q
  have hpenaltyIntegral :
      (∫ q : SpatialTorus,
        ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (q axis)) ≤ 8 := by
    rw [spatialTorus_volume_eq_standardAddCircleVolume]
    exact integral_threeTorus_penaltyProduct_le_eight
      (show 1 ≤ (dyadicRadius scale : ℝ) by
        exact_mod_cast (Nat.one_le_pow scale 2 (by norm_num)))
  calc
    (∫ q : SpatialTorus, kernelNorm q) ≤ ∫ q : SpatialTorus, penaltyProduct q :=
      integral_mono hkernel hpenalty hpointwise
    _ = constant * ∫ q : SpatialTorus,
        ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (q axis) := by
      rw [integral_const_mul]
    _ ≤ constant * 8 := mul_le_mul_of_nonneg_left hpenaltyIntegral hreturn.1
    _ = 8 * constant := by ring

/-! ## From coefficient returns to the named uniform physical witness -/

/-- A common coefficient constant returned by all twenty-seven entries at every large dyadic
scale.  This is now the sole uninhabited coefficient-side interface. -/
def UniformLargeScaleDyadicHodgeSubsetMassReturn (constant : ℝ) : Prop :=
  0 ≤ constant ∧ ∀ scale : ℕ, 3 ≤ scale →
    ∀ component coordinate input : Fin 3,
      DyadicHodgeSubsetMassReturn scale component coordinate input constant

/-- Twenty-seven entrywise Haar returns give the explicit large-scale physical constant
`27 × 8 = 216`. -/
theorem dyadicHodgeJacobianKernelL1_le_twoHundredSixteen_mul
    {constant : ℝ} (hreturn : UniformLargeScaleDyadicHodgeSubsetMassReturn constant)
    (scale : ℕ) (hscale : 3 ≤ scale) :
    dyadicHodgeJacobianKernelL1 scale ≤ 216 * constant := by
  unfold dyadicHodgeJacobianKernelL1
  calc
    (∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
      ∫ q : SpatialTorus,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖) ≤
      ∑ _component : Fin 3, ∑ _coordinate : Fin 3, ∑ _input : Fin 3,
        8 * constant := by
          apply Finset.sum_le_sum
          intro component _
          apply Finset.sum_le_sum
          intro coordinate _
          apply Finset.sum_le_sum
          intro input _
          exact integral_norm_dyadicHodgeJacobianKernelEntry_le_eight_mul
            scale component coordinate input (hreturn.2 scale hscale component coordinate input)
    _ = 216 * constant := by
      simp
      ring

/-- The three exact low scales and the large-scale subset return construct the formerly
uninhabited named uniform physical-kernel witness. -/
theorem uniformDyadicHodgeJacobianKernelBound_of_subsetMassReturn
    {constant : ℝ} (hreturn : UniformLargeScaleDyadicHodgeSubsetMassReturn constant) :
    UniformDyadicHodgeJacobianKernelBound (804357 + 216 * constant) := by
  constructor
  · have hconstant := hreturn.1
    positivity
  · intro scale
    by_cases hsmall : scale ≤ 2
    · exact
        (NavierStokesDyadicHodgeLowScale.dyadicHodgeJacobianKernelL1_le_804357_of_scale_le_two
          scale hsmall).trans (by
            have hconstant := hreturn.1
            linarith)
    · have hlarge : 3 ≤ scale := by omega
      exact (dyadicHodgeJacobianKernelL1_le_twoHundredSixteen_mul hreturn scale hlarge).trans
        (by
          have hconstant := hreturn.1
          linarith)

section Audit

#print axioms norm_dyadicHodgeSubsetGap_eq_chordProduct
#print axioms norm_dyadicHodgeJacobianKernelEntry_le_penaltyProduct
#print axioms integral_norm_dyadicHodgeJacobianKernelEntry_le_eight_mul
#print axioms dyadicHodgeJacobianKernelL1_le_twoHundredSixteen_mul
#print axioms uniformDyadicHodgeJacobianKernelBound_of_subsetMassReturn

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
