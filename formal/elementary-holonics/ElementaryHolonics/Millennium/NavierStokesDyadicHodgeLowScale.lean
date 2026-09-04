import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeKernelVariation

/-!
# The three exceptional dyadic Hodge scales

The direct physical kernel has twenty-seven scalar entries.  Every coefficient in one entry has
norm at most one, and the centered aperture contains exactly `N_s^3` coefficients, where
`N_s = 2^(s+3)-1`.  Haar measure on the spatial torus is normalized.  The pointwise triangle bound
therefore gives

```text
dyadicHodgeJacobianKernelL1 s ≤ 27 N_s^3.
```

At scales zero, one and two, `N_s` is respectively `7, 15, 31`, so all three exceptional scales are
bounded by `27 * 31^3 = 804357`.  This discharges the finite beginning of the uniform-kernel
construction; the remaining return is the scale-independent large-scale estimate.

Truth status: `[proved-derived] [formal-checked]` for every theorem below.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeLowScale

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := inferInstance

/-- One physical Hodge-kernel entry is pointwise bounded by its exact coefficient population. -/
theorem norm_dyadicHodgeJacobianKernelEntry_le_count_cube
    (scale : ℕ) (component coordinate input : Fin 3) (q : SpatialTorus) :
    ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖ ≤
      (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis, norm_mul]
  have hbase :
      ‖UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  rw [hbase, one_mul]
  refine (norm_finiteCharacterSynthesisThree_le_mass
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
    (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale) ?_ ?_ ?_).trans
      (sum_norm_dyadicHodgeCubeCoefficient_le_count_cube
        scale component coordinate input)
  all_goals rw [fourier_apply]
  all_goals exact Circle.norm_coe _

/-- Normalized Haar integration does not enlarge the coefficient-population bound. -/
theorem integral_norm_dyadicHodgeJacobianKernelEntry_le_count_cube
    (scale : ℕ) (component coordinate input : Fin 3) :
    (∫ q : SpatialTorus,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖) ≤
      (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
  have hkernel : Integrable
      (fun q : SpatialTorus ↦
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖
        continuous_toFun := by fun_prop }
  have hconstant : Integrable
      (fun _q : SpatialTorus ↦ (dyadicHodgeApertureCount scale : ℝ) ^ 3) :=
    integrable_const _
  calc
    (∫ q : SpatialTorus,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input q‖) ≤
        ∫ _q : SpatialTorus, (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
      apply integral_mono hkernel hconstant
      exact norm_dyadicHodgeJacobianKernelEntry_le_count_cube
        scale component coordinate input
    _ = (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by simp

/-- The complete twenty-seven-entry physical kernel has the crude exact aperture bound. -/
theorem dyadicHodgeJacobianKernelL1_le_twentySeven_count_cube (scale : ℕ) :
    dyadicHodgeJacobianKernelL1 scale ≤
      27 * (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
  unfold dyadicHodgeJacobianKernelL1
  calc
    (∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
      ∫ y : SpatialTorus,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) ≤
        ∑ _component : Fin 3, ∑ _coordinate : Fin 3, ∑ _input : Fin 3,
          (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro component _
      apply Finset.sum_le_sum
      intro coordinate _
      apply Finset.sum_le_sum
      intro input _
      exact integral_norm_dyadicHodgeJacobianKernelEntry_le_count_cube
        scale component coordinate input
    _ = 27 * (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
      simp
      ring

/-- The exact aperture counts at the three exceptional scales. -/
theorem dyadicHodgeApertureCounts_zero_one_two :
    dyadicHodgeApertureCount 0 = 7 ∧
      dyadicHodgeApertureCount 1 = 15 ∧
      dyadicHodgeApertureCount 2 = 31 := by
  norm_num [dyadicHodgeApertureCount_eq, dyadicRadius]

/-- A single explicit constant closes scales zero through two. -/
theorem dyadicHodgeJacobianKernelL1_le_804357_of_scale_le_two
    (scale : ℕ) (hscale : scale ≤ 2) :
    dyadicHodgeJacobianKernelL1 scale ≤ 804357 := by
  refine (dyadicHodgeJacobianKernelL1_le_twentySeven_count_cube scale).trans ?_
  interval_cases scale <;>
    norm_num [dyadicHodgeApertureCount_eq, dyadicRadius]

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeLowScale

section Audit
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeLowScale
#print axioms norm_dyadicHodgeJacobianKernelEntry_le_count_cube
#print axioms integral_norm_dyadicHodgeJacobianKernelEntry_le_count_cube
#print axioms dyadicHodgeJacobianKernelL1_le_twentySeven_count_cube
#print axioms dyadicHodgeApertureCounts_zero_one_two
#print axioms dyadicHodgeJacobianKernelL1_le_804357_of_scale_le_two
end Audit
