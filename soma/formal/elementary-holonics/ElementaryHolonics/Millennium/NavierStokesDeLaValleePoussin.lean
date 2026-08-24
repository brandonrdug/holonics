import ElementaryHolonics.Millennium.NavierStokesFejerDifferenceBridge

/-!
# An exact tensor de la Vallée Poussin scale chart

**[proved-derived]** We use the inclusive integer-radius convention

`outerRadius N = 2 * N + 1`.

Thus the outer one-dimensional Fejer denominator is `2 * (N + 1)`, and
`2 F_(2N+1) - F_N` has multiplier exactly one on every integer frequency of absolute value at
most `N + 1`.  Taking the product in the three spatial coordinates gives a genuine tensor
low-pass: its multiplier is one on `frequencyCube (N + 1)` and vanishes outside
`frequencyCube (2 * N + 1)`, including the edge case `N = 0`.

The physical kernel is the product of the three one-dimensional differences.  Each factor has
Haar `L1` norm at most `3`, because the two Fejer kernels are positive and normalized.  Hence the
three-dimensional kernel has Haar `L1` norm at most `27`, uniformly in `N`, and convolution has
the corresponding radius-uniform pointwise bound.  The adjacent band is the difference of the
low-passes at `N + 1` and `N`; it vanishes on `frequencyCube (N + 1)`, is supported in
`frequencyCube (2 * N + 3)`, and has the explicit uniform convolution bound `54`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFejerMultiplier
open Soma.Holonics.Millennium.NavierStokesFejerKernelConvolution
open Soma.Holonics.Millennium.NavierStokesFejerDifferenceBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The exact finite multiplier -/

/-- The inclusive outer radius.  Its population has size `2 * (radius + 1)`. -/
def valleePoussinOuterRadius (radius : ℕ) : ℕ :=
  2 * radius + 1

@[simp]
theorem valleePoussinOuterRadius_add_one (radius : ℕ) :
    valleePoussinOuterRadius radius + 1 = 2 * (radius + 1) := by
  unfold valleePoussinOuterRadius
  omega

/-- The one-coordinate de la Vallée Poussin multiplier. -/
def coordinateValleePoussinWeight (radius : ℕ) (frequency : ℤ) : ℝ :=
  2 * coordinateHatWeight (valleePoussinOuterRadius radius) frequency -
    coordinateHatWeight radius frequency

/-- The three-coordinate tensor multiplier. -/
def tensorValleePoussinWeight (radius : ℕ) (frequency : SpatialFrequency) : ℝ :=
  ∏ coordinate : Fin 3, coordinateValleePoussinWeight radius (frequency coordinate)

/-- An absolute-frequency bound is equivalent to the closed integer interval. -/
theorem natAbs_le_iff_bounds (radius : ℕ) (frequency : ℤ) :
    frequency.natAbs ≤ radius ↔
      -(radius : ℤ) ≤ frequency ∧ frequency ≤ (radius : ℤ) := by
  rw [← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

/-- Exact one-dimensional plateau, valid also at radius zero. -/
theorem coordinateValleePoussinWeight_eq_one
    (radius : ℕ) {frequency : ℤ}
    (hfrequency : frequency.natAbs ≤ radius + 1) :
    coordinateValleePoussinWeight radius frequency = 1 := by
  by_cases hinner : frequency.natAbs ≤ radius
  · have houter : frequency.natAbs ≤ valleePoussinOuterRadius radius := by
      unfold valleePoussinOuterRadius
      omega
    simp only [coordinateValleePoussinWeight, coordinateHatWeight, if_pos hinner,
      if_pos houter]
    have hinnerSub :
        (((radius + 1 - frequency.natAbs : ℕ) : ℝ)) =
          (radius + 1 : ℝ) - frequency.natAbs := by
      rw [Nat.cast_sub (by omega : frequency.natAbs ≤ radius + 1)]
      push_cast
      rfl
    have houterSub :
        (((valleePoussinOuterRadius radius + 1 - frequency.natAbs : ℕ) : ℝ)) =
          (valleePoussinOuterRadius radius + 1 : ℝ) - frequency.natAbs := by
      rw [Nat.cast_sub (by omega :
        frequency.natAbs ≤ valleePoussinOuterRadius radius + 1)]
      push_cast
      rfl
    rw [hinnerSub, houterSub]
    have houterDenominator :
        (valleePoussinOuterRadius radius : ℝ) + 1 = 2 * (radius + 1 : ℝ) := by
      norm_cast
    rw [houterDenominator]
    have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · have habs : frequency.natAbs = radius + 1 := by omega
    have houter : frequency.natAbs ≤ valleePoussinOuterRadius radius := by
      unfold valleePoussinOuterRadius
      omega
    have hsub :
        valleePoussinOuterRadius radius + 1 - (radius + 1) = radius + 1 := by
      unfold valleePoussinOuterRadius
      omega
    simp only [coordinateValleePoussinWeight, coordinateHatWeight, if_pos houter,
      if_neg hinner]
    rw [habs, hsub]
    have houterDenominator :
        (valleePoussinOuterRadius radius : ℝ) + 1 = 2 * (radius + 1 : ℝ) := by
      norm_cast
    rw [houterDenominator]
    have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- Exact one-dimensional outer support. -/
theorem coordinateValleePoussinWeight_eq_zero_of_outer_lt
    (radius : ℕ) {frequency : ℤ}
    (hfrequency : valleePoussinOuterRadius radius < frequency.natAbs) :
    coordinateValleePoussinWeight radius frequency = 0 := by
  have houter : ¬ frequency.natAbs ≤ valleePoussinOuterRadius radius := by omega
  have hinner : ¬ frequency.natAbs ≤ radius := by
    unfold valleePoussinOuterRadius at hfrequency
    omega
  simp [coordinateValleePoussinWeight, coordinateHatWeight, houter, hinner]

/-- The tensor multiplier is exactly one throughout the inner cube. -/
theorem tensorValleePoussinWeight_eq_one
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1)) :
    tensorValleePoussinWeight radius frequency = 1 := by
  unfold tensorValleePoussinWeight
  apply Finset.prod_eq_one
  intro coordinate _hcoordinate
  apply coordinateValleePoussinWeight_eq_one
  exact (natAbs_le_iff_bounds (radius + 1) (frequency coordinate)).mpr
    ((mem_frequencyCube_iff (radius + 1) frequency).mp hfrequency coordinate)

/-- Outside the outer cube, at least one coordinate factor is exactly zero. -/
theorem tensorValleePoussinWeight_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube (valleePoussinOuterRadius radius)) :
    tensorValleePoussinWeight radius frequency = 0 := by
  rw [mem_frequencyCube_iff] at hfrequency
  push_neg at hfrequency
  obtain ⟨coordinate, hcoordinate⟩ := hfrequency
  unfold tensorValleePoussinWeight
  apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
  apply coordinateValleePoussinWeight_eq_zero_of_outer_lt
  by_contra hnot
  have habs := (natAbs_le_iff_bounds
    (valleePoussinOuterRadius radius) (frequency coordinate)).mp (Nat.le_of_not_gt hnot)
  exact (not_lt_of_ge habs.2) (hcoordinate habs.1)

/-! ## The physical tensor kernel -/

/-- The one-dimensional physical de la Vallée Poussin factor. -/
def coordinateValleePoussinKernel (radius : ℕ) : C(UnitAddCircle, ℂ) :=
  (2 : ℂ) • coordinateHatKernel (valleePoussinOuterRadius radius) -
    coordinateHatKernel radius

/-- The physical three-dimensional tensor product of the coordinate factors. -/
def tensorValleePoussinKernel (radius : ℕ) : C(SpatialTorus, ℂ) where
  toFun q := ∏ coordinate : Fin 3,
    coordinateValleePoussinKernel radius (q coordinate)
  continuous_toFun := by fun_prop

/-! ## Exact coordinate and tensor Fourier coefficients -/

/-- Normalized circle characters are exactly orthogonal. -/
theorem integral_fourier_neg_mul_fourier (first second : ℤ) :
    ∫ q : UnitAddCircle, fourier (-first) q * fourier second q =
      if first = second then 1 else 0 := by
  simpa only [ContinuousMap.inner_toLp, ← fourier_neg, ← fourier_add, add_comm] using
    (orthonormal_iff_ite.mp (@orthonormal_fourier 1 ⟨by norm_num⟩)) first second

/-- The coordinate Fejer kernel has its declared hat coefficient at every integer frequency. -/
theorem fourierCoeff_coordinateHatKernel (radius : ℕ) (frequency : ℤ) :
    fourierCoeff (fun q : UnitAddCircle ↦ coordinateHatKernel radius q) frequency =
      (coordinateHatWeight radius frequency : ℂ) := by
  rw [fourierCoeff]
  simp only [coordinateHatKernel, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [integral_finset_sum]
  · have hreorder : ∀ second : ℤ, ∀ q : UnitAddCircle,
        fourier (-frequency) q *
            ((coordinateHatWeight radius second : ℂ) * fourier second q) =
          (coordinateHatWeight radius second : ℂ) *
            (fourier (-frequency) q * fourier second q) := by
        intros
        ring
    have hintegral : ∀ second : ℤ,
        (∫ q : UnitAddCircle,
            fourier (-frequency) q *
              ((coordinateHatWeight radius second : ℂ) * fourier second q)) =
          (coordinateHatWeight radius second : ℂ) *
            (if frequency = second then 1 else 0) := by
      intro second
      rw [integral_congr_ae (Filter.Eventually.of_forall (hreorder second))]
      rw [integral_const_mul, integral_fourier_neg_mul_fourier]
    calc
      ∑ second ∈ coordinateFrequencyInterval radius,
          ∫ q : UnitAddCircle,
            fourier (-frequency) q *
              ((coordinateHatWeight radius second : ℂ) * fourier second q) =
          ∑ second ∈ coordinateFrequencyInterval radius,
            (coordinateHatWeight radius second : ℂ) *
              (if frequency = second then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro second _hsecond
        exact hintegral second
      _ = (coordinateHatWeight radius frequency : ℂ) := by
        by_cases hfrequency : frequency ∈ coordinateFrequencyInterval radius
        · rw [Finset.sum_eq_single frequency]
          · simp
          · intro other _hother hne
            simp [hne.symm]
          · exact fun hnot ↦ (hnot hfrequency).elim
        · have hzero : coordinateHatWeight radius frequency = 0 := by
            have hnotabs : ¬ frequency.natAbs ≤ radius := by
              intro habs
              apply hfrequency
              exact (mem_coordinateFrequencyInterval_iff radius frequency).mpr
                ((natAbs_le_iff_bounds radius frequency).mp habs)
            simp [coordinateHatWeight, hnotabs]
          simp [hfrequency, hzero]
  · intro second _hsecond
    exact continuousMap_integrable_on_compact
      { toFun := fun q : UnitAddCircle ↦
          fourier (-frequency) q *
            ((coordinateHatWeight radius second : ℂ) * fourier second q)
        continuous_toFun := by fun_prop }

/-- The physical coordinate difference has exactly the declared de la Vallée Poussin
coefficient at every integer frequency. -/
theorem fourierCoeff_coordinateValleePoussinKernel
    (radius : ℕ) (frequency : ℤ) :
    fourierCoeff
        (fun q : UnitAddCircle ↦ coordinateValleePoussinKernel radius q) frequency =
      (coordinateValleePoussinWeight radius frequency : ℂ) := by
  rw [fourierCoeff]
  simp only [coordinateValleePoussinKernel, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smul_eq_mul, mul_sub]
  rw [integral_sub]
  · have hreorder : ∀ q : UnitAddCircle,
        fourier (-frequency) q *
            ((2 : ℂ) * coordinateHatKernel (valleePoussinOuterRadius radius) q) =
          (2 : ℂ) * (fourier (-frequency) q *
            coordinateHatKernel (valleePoussinOuterRadius radius) q) := by
        intro q
        ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hreorder), integral_const_mul]
    change (2 : ℂ) * fourierCoeff
        (fun q : UnitAddCircle ↦
          coordinateHatKernel (valleePoussinOuterRadius radius) q) frequency -
      fourierCoeff (fun q : UnitAddCircle ↦ coordinateHatKernel radius q) frequency = _
    rw [fourierCoeff_coordinateHatKernel, fourierCoeff_coordinateHatKernel]
    simp [coordinateValleePoussinWeight]
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : UnitAddCircle ↦
          fourier (-frequency) q *
            ((2 : ℂ) * coordinateHatKernel (valleePoussinOuterRadius radius) q)
        continuous_toFun := by fun_prop }
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : UnitAddCircle ↦
          fourier (-frequency) q * coordinateHatKernel radius q
        continuous_toFun := by fun_prop }

/-- **Exact physical multiplier identity.**  The Fourier coefficient of the tensor physical
kernel is the tensor de la Vallée Poussin weight at every lattice frequency. -/
theorem mFourierCoeff_tensorValleePoussinKernel
    (radius : ℕ) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorValleePoussinKernel radius q) frequency =
      (tensorValleePoussinWeight radius frequency : ℂ) := by
  rw [UnitAddTorus.mFourierCoeff]
  simp only [UnitAddTorus.mFourier, tensorValleePoussinKernel,
    ContinuousMap.coe_mk, smul_eq_mul]
  have hreorder : ∀ q : SpatialTorus,
      (∏ coordinate : Fin 3,
          fourier ((-frequency) coordinate) (q coordinate)) *
          (∏ coordinate : Fin 3,
            coordinateValleePoussinKernel radius (q coordinate)) =
        ∏ coordinate : Fin 3,
          fourier (-(frequency coordinate)) (q coordinate) *
            coordinateValleePoussinKernel radius (q coordinate) := by
    intro q
    simp only [Pi.neg_apply]
    exact Finset.prod_mul_distrib.symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hreorder)]
  calc
    ∫ q : (Fin 3 → UnitAddCircle),
          ∏ coordinate : Fin 3,
            fourier (-(frequency coordinate)) (q coordinate) *
              coordinateValleePoussinKernel radius (q coordinate) =
        ∏ coordinate : Fin 3,
          ∫ q : UnitAddCircle,
            fourier (-(frequency coordinate)) q *
              coordinateValleePoussinKernel radius q :=
      MeasureTheory.integral_fintype_prod_volume_eq_prod
        (E := fun _ : Fin 3 ↦ UnitAddCircle)
        (fun coordinate : Fin 3 ↦ fun q : UnitAddCircle ↦
          fourier (-(frequency coordinate)) q *
            coordinateValleePoussinKernel radius q)
    _ = ∏ coordinate : Fin 3,
          fourierCoeff
            (fun q : UnitAddCircle ↦ coordinateValleePoussinKernel radius q)
            (frequency coordinate) := by rfl
    _ = (tensorValleePoussinWeight radius frequency : ℂ) := by
      simp_rw [fourierCoeff_coordinateValleePoussinKernel]
      simp [tensorValleePoussinWeight]

/-- Physical Fourier coefficients are one on the complete inner cube. -/
theorem mFourierCoeff_tensorValleePoussinKernel_eq_one
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1)) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorValleePoussinKernel radius q) frequency = 1 := by
  rw [mFourierCoeff_tensorValleePoussinKernel,
    tensorValleePoussinWeight_eq_one radius hfrequency]
  norm_num

/-- Physical Fourier coefficients vanish outside the complete outer cube. -/
theorem mFourierCoeff_tensorValleePoussinKernel_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube (valleePoussinOuterRadius radius)) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorValleePoussinKernel radius q) frequency = 0 := by
  rw [mFourierCoeff_tensorValleePoussinKernel,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer radius hfrequency]
  norm_num

/-! ## Coordinate normalization and the tensor `L1` bound -/

/-- Every coordinate Fejer kernel is real-valued. -/
@[simp]
theorem coordinateHatKernel_im (radius : ℕ) (q : UnitAddCircle) :
    (coordinateHatKernel radius q).im = 0 := by
  rw [coordinateHatKernel_eq_averagedCoordinateFejerKernel]
  simp [averagedCoordinateFejerKernel]

/-- Every coordinate Fejer kernel is pointwise nonnegative. -/
theorem coordinateHatKernel_re_nonneg (radius : ℕ) (q : UnitAddCircle) :
    0 ≤ (coordinateHatKernel radius q).re := by
  rw [coordinateHatKernel_eq_averagedCoordinateFejerKernel]
  simp only [averagedCoordinateFejerKernel, ContinuousMap.coe_mk, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Complex.normSq_nonneg _)

/-- For the positive real coordinate kernel, complex norm is its real part. -/
theorem norm_coordinateHatKernel (radius : ℕ) (q : UnitAddCircle) :
    ‖coordinateHatKernel radius q‖ = (coordinateHatKernel radius q).re := by
  have hreal : coordinateHatKernel radius q =
      ((coordinateHatKernel radius q).re : ℂ) := by
    apply Complex.ext
    · exact (Complex.ofReal_re _).symm
    · rw [coordinateHatKernel_im, Complex.ofReal_im]
  calc
    ‖coordinateHatKernel radius q‖ =
        ‖((coordinateHatKernel radius q).re : ℂ)‖ := congrArg norm hreal
    _ = |(coordinateHatKernel radius q).re| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (coordinateHatKernel radius q).re :=
      abs_of_nonneg (coordinateHatKernel_re_nonneg radius q)

/-- **Exact one-dimensional normalization.**  Every coordinate Fejer kernel has Haar `L1`
mass one, including at radius zero. -/
theorem integral_norm_coordinateHatKernel (radius : ℕ) :
    ∫ q : UnitAddCircle, ‖coordinateHatKernel radius q‖ = 1 := by
  have hkernelIntegrable : Integrable
      (fun q : UnitAddCircle ↦ coordinateHatKernel radius q) :=
    continuousMap_integrable_on_compact (coordinateHatKernel radius)
  have hcoefficient := fourierCoeff_coordinateHatKernel radius 0
  rw [fourierCoeff] at hcoefficient
  simp only [neg_zero, fourier_zero, one_smul, coordinateHatWeight_zero,
    Complex.ofReal_one] at hcoefficient
  calc
    ∫ q : UnitAddCircle, ‖coordinateHatKernel radius q‖ =
        ∫ q : UnitAddCircle, (coordinateHatKernel radius q).re := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact norm_coordinateHatKernel radius q
    _ = (∫ q : UnitAddCircle, coordinateHatKernel radius q).re :=
      integral_re hkernelIntegrable
    _ = 1 := by
      simpa using congrArg Complex.re hcoefficient

/-- A coordinate de la Vallée Poussin factor has `L1` norm at most `2 + 1 = 3`, uniformly in
the radius. -/
theorem integral_norm_coordinateValleePoussinKernel_le (radius : ℕ) :
    ∫ q : UnitAddCircle, ‖coordinateValleePoussinKernel radius q‖ ≤ 3 := by
  have hkernelIntegrable : Integrable
      (fun q : UnitAddCircle ↦ ‖coordinateValleePoussinKernel radius q‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : UnitAddCircle ↦ ‖coordinateValleePoussinKernel radius q‖
        continuous_toFun := by fun_prop }
  have hmajorantIntegrable : Integrable
      (fun q : UnitAddCircle ↦
        2 * ‖coordinateHatKernel (valleePoussinOuterRadius radius) q‖ +
          ‖coordinateHatKernel radius q‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : UnitAddCircle ↦
          2 * ‖coordinateHatKernel (valleePoussinOuterRadius radius) q‖ +
            ‖coordinateHatKernel radius q‖
        continuous_toFun := by fun_prop }
  calc
    ∫ q : UnitAddCircle, ‖coordinateValleePoussinKernel radius q‖ ≤
        ∫ q : UnitAddCircle,
          2 * ‖coordinateHatKernel (valleePoussinOuterRadius radius) q‖ +
            ‖coordinateHatKernel radius q‖ := by
      apply integral_mono hkernelIntegrable hmajorantIntegrable
      intro q
      unfold coordinateValleePoussinKernel
      refine (norm_sub_le _ _).trans_eq ?_
      simp [ContinuousMap.smul_apply]
    _ = 2 * (∫ q : UnitAddCircle,
          ‖coordinateHatKernel (valleePoussinOuterRadius radius) q‖) +
        ∫ q : UnitAddCircle, ‖coordinateHatKernel radius q‖ := by
      rw [integral_add, integral_const_mul]
      · exact continuousMap_integrable_on_compact
          { toFun := fun q : UnitAddCircle ↦
              2 * ‖coordinateHatKernel (valleePoussinOuterRadius radius) q‖
            continuous_toFun := by fun_prop }
      · exact continuousMap_integrable_on_compact
          { toFun := fun q : UnitAddCircle ↦ ‖coordinateHatKernel radius q‖
            continuous_toFun := by fun_prop }
    _ = 3 := by
      rw [integral_norm_coordinateHatKernel, integral_norm_coordinateHatKernel]
      norm_num

/-- The norm of the physical tensor kernel factors into the three coordinate norms. -/
theorem norm_tensorValleePoussinKernel (radius : ℕ) (q : SpatialTorus) :
    ‖tensorValleePoussinKernel radius q‖ =
      ∏ coordinate : Fin 3,
        ‖coordinateValleePoussinKernel radius (q coordinate)‖ := by
  simp only [tensorValleePoussinKernel, ContinuousMap.coe_mk]
  exact norm_prod _ _

/-- **Radius-uniform physical `L1` bound.**  The tensor product costs at most
`3 ^ 3 = 27`, independently of the inner or outer integer radius. -/
theorem integral_norm_tensorValleePoussinKernel_le (radius : ℕ) :
    ∫ q : SpatialTorus, ‖tensorValleePoussinKernel radius q‖ ≤ 27 := by
  simp_rw [norm_tensorValleePoussinKernel]
  calc
    ∫ q : (Fin 3 → UnitAddCircle),
          ∏ coordinate : Fin 3,
            ‖coordinateValleePoussinKernel radius (q coordinate)‖ =
        ∏ coordinate : Fin 3,
          ∫ q : UnitAddCircle,
            ‖coordinateValleePoussinKernel radius q‖ :=
      MeasureTheory.integral_fintype_prod_volume_eq_prod
        (E := fun _ : Fin 3 ↦ UnitAddCircle)
        (fun _coordinate : Fin 3 ↦ fun q : UnitAddCircle ↦
          ‖coordinateValleePoussinKernel radius q‖)
    _ ≤ ∏ _coordinate : Fin 3, (3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro coordinate _hcoordinate
        exact integral_nonneg fun q ↦ norm_nonneg _
      · intro coordinate _hcoordinate
        exact integral_norm_coordinateValleePoussinKernel_le radius
    _ = 27 := by norm_num [Fin.prod_univ_three]

/-- The tensor low-pass retains Haar mass one even though it need not be pointwise positive. -/
theorem integral_tensorValleePoussinKernel (radius : ℕ) :
    ∫ q : SpatialTorus, tensorValleePoussinKernel radius q = 1 := by
  have hcoefficient := mFourierCoeff_tensorValleePoussinKernel radius 0
  rw [UnitAddTorus.mFourierCoeff] at hcoefficient
  have hzero : (0 : SpatialFrequency) ∈ frequencyCube (radius + 1) := by
    rw [mem_frequencyCube_iff]
    intro coordinate
    simp only [Pi.zero_apply]
    have hnonneg : (0 : ℤ) ≤ ((radius + 1 : ℕ) : ℤ) :=
      Int.natCast_nonneg (radius + 1)
    exact ⟨neg_nonpos.mpr hnonneg, hnonneg⟩
  rw [tensorValleePoussinWeight_eq_one radius hzero] at hcoefficient
  simpa [UnitAddTorus.mFourier_zero] using hcoefficient

/-- Physical convolution by the tensor de la Vallée Poussin low-pass. -/
def tensorValleePoussinConvolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) : E :=
  torusKernelConvolution (tensorValleePoussinKernel radius) field q

/-- **Radius-uniform pointwise physical bound.**  Every finite scale has the same explicit
upper-bound constant `27`. -/
theorem norm_tensorValleePoussinConvolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) :
    ‖tensorValleePoussinConvolution radius field q‖ ≤ 27 * ‖field‖ := by
  refine (norm_torusKernelConvolution_le
    (tensorValleePoussinKernel radius) field q).trans ?_
  exact mul_le_mul_of_nonneg_right
    (integral_norm_tensorValleePoussinKernel_le radius) (norm_nonneg field)

/-! ## Adjacent bands -/

/-- The multiplier of the adjacent radius band `V_(radius+1) - V_radius`. -/
def adjacentValleePoussinWeight
    (radius : ℕ) (frequency : SpatialFrequency) : ℝ :=
  tensorValleePoussinWeight (radius + 1) frequency -
    tensorValleePoussinWeight radius frequency

/-- The physical adjacent band kernel. -/
def adjacentValleePoussinKernel (radius : ℕ) : C(SpatialTorus, ℂ) :=
  tensorValleePoussinKernel (radius + 1) - tensorValleePoussinKernel radius

/-- The next low-pass has explicit outer radius `2 * radius + 3`. -/
theorem valleePoussinOuterRadius_succ (radius : ℕ) :
    valleePoussinOuterRadius (radius + 1) = 2 * radius + 3 := by
  unfold valleePoussinOuterRadius
  omega

/-- The adjacent multiplier cancels every frequency in the smaller plateau cube. -/
theorem adjacentValleePoussinWeight_eq_zero_of_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1)) :
    adjacentValleePoussinWeight radius frequency = 0 := by
  have hnext : frequency ∈ frequencyCube ((radius + 1) + 1) :=
    frequencyCube_mono (Nat.le_succ (radius + 1)) hfrequency
  rw [adjacentValleePoussinWeight,
    tensorValleePoussinWeight_eq_one (radius + 1) hnext,
    tensorValleePoussinWeight_eq_one radius hfrequency,
    sub_self]

/-- The adjacent multiplier is supported in the next low-pass outer cube, whose radius is
`2 * radius + 3`. -/
theorem adjacentValleePoussinWeight_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉
      frequencyCube (valleePoussinOuterRadius (radius + 1))) :
    adjacentValleePoussinWeight radius frequency = 0 := by
  have houterMono :
      valleePoussinOuterRadius radius ≤
        valleePoussinOuterRadius (radius + 1) := by
    unfold valleePoussinOuterRadius
    omega
  have hsmaller : frequency ∉ frequencyCube (valleePoussinOuterRadius radius) := by
    intro hmem
    exact hfrequency (frequencyCube_mono houterMono hmem)
  rw [adjacentValleePoussinWeight,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer (radius + 1) hfrequency,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer radius hsmaller,
    sub_zero]

/-- The physical adjacent kernel has exactly the adjacent multiplier coefficient. -/
theorem mFourierCoeff_adjacentValleePoussinKernel
    (radius : ℕ) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ adjacentValleePoussinKernel radius q) frequency =
      (adjacentValleePoussinWeight radius frequency : ℂ) := by
  rw [UnitAddTorus.mFourierCoeff]
  simp only [adjacentValleePoussinKernel, ContinuousMap.sub_apply, smul_sub]
  rw [integral_sub]
  · change UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorValleePoussinKernel (radius + 1) q) frequency -
      UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorValleePoussinKernel radius q) frequency = _
    rw [mFourierCoeff_tensorValleePoussinKernel,
      mFourierCoeff_tensorValleePoussinKernel]
    simp [adjacentValleePoussinWeight]
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-frequency) q •
            tensorValleePoussinKernel (radius + 1) q
        continuous_toFun := by fun_prop }
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-frequency) q •
            tensorValleePoussinKernel radius q
        continuous_toFun := by fun_prop }

/-- Exact low-frequency cancellation of the adjacent physical band. -/
theorem mFourierCoeff_adjacentValleePoussinKernel_eq_zero_of_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (radius + 1)) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ adjacentValleePoussinKernel radius q) frequency = 0 := by
  rw [mFourierCoeff_adjacentValleePoussinKernel,
    adjacentValleePoussinWeight_eq_zero_of_mem_inner radius hfrequency]
  norm_num

/-- Exact outer support of the adjacent physical band. -/
theorem mFourierCoeff_adjacentValleePoussinKernel_eq_zero_of_not_mem_outer
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉
      frequencyCube (valleePoussinOuterRadius (radius + 1))) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ adjacentValleePoussinKernel radius q) frequency = 0 := by
  rw [mFourierCoeff_adjacentValleePoussinKernel,
    adjacentValleePoussinWeight_eq_zero_of_not_mem_outer radius hfrequency]
  norm_num

/-- Physical convolution by the adjacent band kernel. -/
def adjacentValleePoussinConvolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) : E :=
  torusKernelConvolution (adjacentValleePoussinKernel radius) field q

/-- Adjacent band convolution is exactly the difference of the two neighboring low-passes. -/
theorem adjacentValleePoussinConvolution_eq_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) :
    adjacentValleePoussinConvolution radius field q =
      tensorValleePoussinConvolution (radius + 1) field q -
        tensorValleePoussinConvolution radius field q := by
  unfold adjacentValleePoussinConvolution adjacentValleePoussinKernel
    torusKernelConvolution
  simp only [ContinuousMap.sub_apply, sub_smul]
  rw [integral_sub]
  · rfl
  · exact continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          tensorValleePoussinKernel (radius + 1) y • field (q - y)
        continuous_toFun := by fun_prop }
  · exact continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          tensorValleePoussinKernel radius y • field (q - y)
        continuous_toFun := by fun_prop }

/-- **Uniform pointwise adjacent-band bound.**  The honest triangle constant is
`27 + 27 = 54`, for every radius including zero. -/
theorem norm_adjacentValleePoussinConvolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) :
    ‖adjacentValleePoussinConvolution radius field q‖ ≤ 54 * ‖field‖ := by
  rw [adjacentValleePoussinConvolution_eq_sub]
  calc
    ‖tensorValleePoussinConvolution (radius + 1) field q -
        tensorValleePoussinConvolution radius field q‖ ≤
      ‖tensorValleePoussinConvolution (radius + 1) field q‖ +
        ‖tensorValleePoussinConvolution radius field q‖ := norm_sub_le _ _
    _ ≤ 27 * ‖field‖ + 27 * ‖field‖ :=
      add_le_add
        (norm_tensorValleePoussinConvolution_le (radius + 1) field q)
        (norm_tensorValleePoussinConvolution_le radius field q)
    _ = 54 * ‖field‖ := by ring

section Audit

#print axioms tensorValleePoussinWeight_eq_one
#print axioms tensorValleePoussinWeight_eq_zero_of_not_mem_outer
#print axioms mFourierCoeff_tensorValleePoussinKernel
#print axioms integral_norm_tensorValleePoussinKernel_le
#print axioms norm_tensorValleePoussinConvolution_le
#print axioms mFourierCoeff_adjacentValleePoussinKernel
#print axioms norm_adjacentValleePoussinConvolution_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
