import ElementaryHolonics.Millennium.NavierStokesFejerKernelConvolution

/-!
# The ordered-difference bridge for the tensor Fejer kernel

**[proved-derived]** Radius `N` means the positive integer population `{0, ..., N}`.  For an
integer difference `k` with `|k| <= N`, exactly `N + 1 - |k|` ordered pairs in that population
have second coordinate minus first coordinate equal to `k`.  This finite counting receipt
identifies the normalized rectangular Dirichlet norm-square with the closed tensor-hat multiplier
from `NavierStokesFejerMultiplier`.

The identification transports pointwise nonnegativity, exact Haar `L1` mass one, and the
scale-uniform pointwise convolution estimate to the existing `tensorHatKernel`.  No limiting
Fourier series or unbounded aperture is used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesFejerDifferenceBridge

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFejerMultiplier
open Soma.Holonics.Millennium.NavierStokesFejerKernelConvolution

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## One-dimensional ordered-difference fibres -/

/-- Pairs in `{0, ..., radius}` separated forward by the natural displacement `distance`. -/
def forwardDifferencePairs (radius distance : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)).filter
    (fun pair ↦ pair.2 = pair.1 + distance)

/-- Pairs in `{0, ..., radius}` separated backward by the natural displacement `distance`. -/
def backwardDifferencePairs (radius distance : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)).filter
    (fun pair ↦ pair.1 = pair.2 + distance)

/-- A forward displacement `distance <= radius` has exactly `radius + 1 - distance`
realizations. -/
theorem card_forwardDifferencePairs
    (radius distance : ℕ) :
    (forwardDifferencePairs radius distance).card = radius + 1 - distance := by
  have hcard :
      (Finset.range (radius + 1 - distance)).card =
        (forwardDifferencePairs radius distance).card := by
    apply Finset.card_bij (fun first _hfirst ↦ (first, first + distance))
    · intro first hfirst
      rw [Finset.mem_range] at hfirst
      simp only [forwardDifferencePairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      have hsum : first + distance < radius + 1 :=
        Nat.lt_sub_iff_add_lt.mp hfirst
      exact ⟨⟨lt_of_le_of_lt (Nat.le_add_right first distance) hsum, hsum⟩, trivial⟩
    · intro first₁ hfirst₁ first₂ hfirst₂ hpairs
      exact congrArg Prod.fst hpairs
    · intro pair hpair
      simp only [forwardDifferencePairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hpair
      refine ⟨pair.1, ?_, ?_⟩
      · rw [Finset.mem_range]
        apply Nat.lt_sub_iff_add_lt.mpr
        simpa only [hpair.2] using hpair.1.2
      apply Prod.ext
      · rfl
      · exact hpair.2.symm
  simpa using hcard.symm

/-- The backward fibre has the same exact cardinality. -/
theorem card_backwardDifferencePairs
    (radius distance : ℕ) :
    (backwardDifferencePairs radius distance).card = radius + 1 - distance := by
  have hcard :
      (Finset.range (radius + 1 - distance)).card =
        (backwardDifferencePairs radius distance).card := by
    apply Finset.card_bij (fun second _hsecond ↦ (second + distance, second))
    · intro second hsecond
      rw [Finset.mem_range] at hsecond
      simp only [backwardDifferencePairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      have hsum : second + distance < radius + 1 :=
        Nat.lt_sub_iff_add_lt.mp hsecond
      exact ⟨⟨hsum, lt_of_le_of_lt (Nat.le_add_right second distance) hsum⟩, trivial⟩
    · intro second₁ hsecond₁ second₂ hsecond₂ hpairs
      exact congrArg Prod.snd hpairs
    · intro pair hpair
      simp only [backwardDifferencePairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hpair
      refine ⟨pair.2, ?_, ?_⟩
      · rw [Finset.mem_range]
        apply Nat.lt_sub_iff_add_lt.mpr
        simpa only [hpair.2] using hpair.1.1
      apply Prod.ext
      · exact hpair.2.symm
      · rfl
  simpa using hcard.symm

/-- The ordered fibre of an integer difference in the radius-`N` positive population. -/
def coordinateDifferencePairs (radius : ℕ) (frequency : ℤ) : Finset (ℕ × ℕ) :=
  (Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)).filter
    (fun pair ↦ (pair.2 : ℤ) - (pair.1 : ℤ) = frequency)

/-- **Exact one-dimensional multiplicity.**  With the inclusive radius convention, an admitted
difference has `radius + 1 - |frequency|` ordered realizations. -/
theorem card_coordinateDifferencePairs
    (radius : ℕ) (frequency : ℤ) :
    (coordinateDifferencePairs radius frequency).card =
      radius + 1 - frequency.natAbs := by
  by_cases hnonnegative : 0 ≤ frequency
  · have habsCast : (frequency.natAbs : ℤ) = frequency :=
      Int.natAbs_of_nonneg hnonnegative
    have hsets : coordinateDifferencePairs radius frequency =
        forwardDifferencePairs radius frequency.natAbs := by
      ext pair
      simp only [coordinateDifferencePairs, forwardDifferencePairs, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      omega
    rw [hsets, card_forwardDifferencePairs]
  · have hnegative : frequency < 0 := lt_of_not_ge hnonnegative
    have habsCast : (frequency.natAbs : ℤ) = -frequency := by
      rw [Int.natCast_natAbs, abs_of_neg hnegative]
    have hsets : coordinateDifferencePairs radius frequency =
        backwardDifferencePairs radius frequency.natAbs := by
      ext pair
      simp only [coordinateDifferencePairs, backwardDifferencePairs, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      omega
    rw [hsets, card_backwardDifferencePairs]

/-! ## The one-dimensional Fejer square -/

/-- The inclusive one-dimensional frequency interval `{-radius, ..., radius}`. -/
def coordinateFrequencyInterval (radius : ℕ) : Finset ℤ :=
  Finset.Icc (-(radius : ℤ)) (radius : ℤ)

/-- Membership in the coordinate interval is the explicit two-sided radius bound. -/
theorem mem_coordinateFrequencyInterval_iff (radius : ℕ) (frequency : ℤ) :
    frequency ∈ coordinateFrequencyInterval radius ↔
      -(radius : ℤ) ≤ frequency ∧ frequency ≤ (radius : ℤ) := by
  simp [coordinateFrequencyInterval]

/-- The closed coordinate hat is exactly normalized ordered-difference multiplicity. -/
theorem coordinateHatWeight_eq_card_difference_div
    (radius : ℕ) {frequency : ℤ}
    (hfrequency : frequency ∈ coordinateFrequencyInterval radius) :
    coordinateHatWeight radius frequency =
      ((coordinateDifferencePairs radius frequency).card : ℝ) / (radius + 1 : ℝ) := by
  have habsInt : (frequency.natAbs : ℤ) ≤ (radius : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ((mem_coordinateFrequencyInterval_iff radius frequency).mp hfrequency)
  have habs : frequency.natAbs ≤ radius := by exact_mod_cast habsInt
  rw [card_coordinateDifferencePairs]
  simp [coordinateHatWeight, habs]

/-- The multiplicity formula also describes the zero extension outside the radius interval. -/
theorem coordinateHatWeight_eq_card_difference_div_all
    (radius : ℕ) (frequency : ℤ) :
    coordinateHatWeight radius frequency =
      ((coordinateDifferencePairs radius frequency).card : ℝ) / (radius + 1 : ℝ) := by
  by_cases habs : frequency.natAbs ≤ radius
  · apply coordinateHatWeight_eq_card_difference_div radius
    rw [mem_coordinateFrequencyInterval_iff]
    have habsInt : (frequency.natAbs : ℤ) ≤ (radius : ℤ) := by exact_mod_cast habs
    rw [Int.natCast_natAbs] at habsInt
    exact abs_le.mp habsInt
  · rw [card_coordinateDifferencePairs]
    have hzero : radius + 1 - frequency.natAbs = 0 := by omega
    simp [coordinateHatWeight, habs, hzero]

/-- The one-dimensional positive Dirichlet population `{0, ..., radius}`. -/
def coordinateDirichletSum (radius : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ index ∈ Finset.range (radius + 1), fourier (index : ℤ)

/-- The one-dimensional normalized Dirichlet norm-square. -/
def averagedCoordinateFejerKernel (radius : ℕ) : C(UnitAddCircle, ℂ) where
  toFun q := (((radius + 1 : ℕ) : ℝ)⁻¹ *
    Complex.normSq (coordinateDirichletSum radius q) : ℝ)
  continuous_toFun := by fun_prop

/-- The one-dimensional kernel synthesized from the existing closed coordinate hat. -/
def coordinateHatKernel (radius : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ frequency ∈ coordinateFrequencyInterval radius,
    (coordinateHatWeight radius frequency : ℂ) • fourier frequency

/-- Every ordered difference of the positive population lies in the inclusive radius interval. -/
theorem difference_mem_coordinateFrequencyInterval
    (radius : ℕ) {pair : ℕ × ℕ}
    (hpair : pair ∈ Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)) :
    (pair.2 : ℤ) - (pair.1 : ℤ) ∈ coordinateFrequencyInterval radius := by
  simp only [Finset.mem_product, Finset.mem_range] at hpair
  rw [mem_coordinateFrequencyInterval_iff]
  constructor <;> omega

/-- Summing a character over one ordered-difference fibre gives its multiplicity times the
addressed character. -/
theorem sum_character_coordinateDifferencePairs
    (radius : ℕ) (frequency : ℤ) (q : UnitAddCircle) :
    ∑ pair ∈ coordinateDifferencePairs radius frequency,
        fourier ((pair.2 : ℤ) - (pair.1 : ℤ)) q =
      (coordinateDifferencePairs radius frequency).card * fourier frequency q := by
  calc
    ∑ pair ∈ coordinateDifferencePairs radius frequency,
        fourier ((pair.2 : ℤ) - (pair.1 : ℤ)) q =
        ∑ _pair ∈ coordinateDifferencePairs radius frequency,
          fourier frequency q := by
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [(Finset.mem_filter.mp hpair).2]
    _ = (coordinateDifferencePairs radius frequency).card * fourier frequency q := by
      simp

/-- Expansion of the one-dimensional normalized square into its ordered-difference population. -/
theorem averagedCoordinateFejerKernel_eq_difference_sum
    (radius : ℕ) (q : UnitAddCircle) :
    averagedCoordinateFejerKernel radius q =
      ((radius + 1 : ℕ) : ℂ)⁻¹ *
        ∑ pair ∈
            (Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)),
          fourier ((pair.2 : ℤ) - (pair.1 : ℤ)) q := by
  rw [averagedCoordinateFejerKernel]
  change ((((radius + 1 : ℕ) : ℝ)⁻¹ *
      Complex.normSq (coordinateDirichletSum radius q) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  simp only [coordinateDirichletSum, ContinuousMap.sum_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _hfirst
  apply Finset.sum_congr rfl
  intro second _hsecond
  congr 1
  rw [← fourier_neg, ← fourier_add]
  congr 2
  all_goals omega

/-- **Exact one-dimensional factorization.**  The existing coordinate hat kernel is the
normalized nonnegative Dirichlet square. -/
theorem coordinateHatKernel_eq_averagedCoordinateFejerKernel (radius : ℕ) :
    coordinateHatKernel radius = averagedCoordinateFejerKernel radius := by
  ext q
  rw [averagedCoordinateFejerKernel_eq_difference_sum]
  unfold coordinateHatKernel
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.range (radius + 1) ×ˢ Finset.range (radius + 1))
    (t := coordinateFrequencyInterval radius)
    (g := fun pair : ℕ × ℕ ↦ (pair.2 : ℤ) - (pair.1 : ℤ))
    (f := fun pair : ℕ × ℕ ↦
      fourier ((pair.2 : ℤ) - (pair.1 : ℤ)) q)
    (fun pair hpair ↦ difference_mem_coordinateFrequencyInterval radius hpair)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [show (Finset.range (radius + 1) ×ˢ Finset.range (radius + 1)).filter
      (fun pair ↦ (pair.2 : ℤ) - (pair.1 : ℤ) = frequency) =
        coordinateDifferencePairs radius frequency by rfl]
  rw [sum_character_coordinateDifferencePairs]
  rw [coordinateHatWeight_eq_card_difference_div radius hfrequency]
  push_cast
  field_simp

/-! ## Tensor lift and identification with the existing multiplier -/

/-- The existing three-dimensional tensor-hat kernel factors into its three coordinate kernels. -/
theorem tensorHatKernel_apply_eq_prod_coordinateHatKernel
    (radius : ℕ) (q : SpatialTorus) :
    tensorHatKernel radius q =
      ∏ coordinate : Fin 3, coordinateHatKernel radius (q coordinate) := by
  classical
  simp only [tensorHatKernel, tensorHatSynthesis, finiteFourierSynthesis,
    ContinuousMap.coe_mk, Pi.Icc_eq, frequencyCube, coordinateHatKernel,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    tensorHatWeight, UnitAddTorus.mFourier]
  rw [← Finset.sum_prod_piFinset]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  simp only [mul_one]
  push_cast
  rw [mul_comm, ← Finset.prod_mul_distrib]

/-- The nonnegative integer interval is the cast image of the inclusive natural range. -/
theorem sum_fourier_Icc_zero_natCast_eq_range
    (radius : ℕ) (q : UnitAddCircle) :
    ∑ frequency ∈ Finset.Icc (0 : ℤ) (radius : ℤ), fourier frequency q =
      ∑ index ∈ Finset.range (radius + 1), fourier (index : ℤ) q := by
  symm
  apply Finset.sum_bij
    (s := Finset.range (radius + 1))
    (t := Finset.Icc (0 : ℤ) (radius : ℤ))
    (f := fun index : ℕ ↦ fourier (index : ℤ) q)
    (g := fun frequency : ℤ ↦ fourier frequency q)
    (fun index _hindex ↦ (index : ℤ))
  · intro index hindex
    simp only [Finset.mem_range] at hindex
    simp only [Finset.mem_Icc]
    omega
  · intro index₁ _hindex₁ index₂ _hindex₂ heq
    exact_mod_cast heq
  · intro frequency hfrequency
    simp only [Finset.mem_Icc] at hfrequency
    have hcast : (frequency.toNat : ℤ) = frequency :=
      Int.toNat_of_nonneg hfrequency.1
    have htoNat : frequency.toNat ≤ radius := by
      omega
    refine ⟨frequency.toNat, Finset.mem_range.mpr (Nat.lt_succ_of_le htoNat), ?_⟩
    exact Int.toNat_of_nonneg hfrequency.1
  · intro index _hindex
    rfl

/-- The positive rectangular Dirichlet population factors into its three coordinate populations. -/
theorem rectangularDirichletSum_apply_eq_prod_coordinateDirichletSum
    (radius : ℕ) (q : SpatialTorus) :
    rectangularDirichletSum radius q =
      ∏ coordinate : Fin 3, coordinateDirichletSum radius (q coordinate) := by
  classical
  simp only [rectangularDirichletSum, positiveFrequencyCube, ContinuousMap.sum_apply,
    Pi.Icc_eq, UnitAddTorus.mFourier, coordinateDirichletSum]
  change (∑ frequency ∈ Fintype.piFinset
      (fun _ : Fin 3 ↦ Finset.Icc (0 : ℤ) (radius : ℤ)),
        ∏ coordinate : Fin 3, fourier (frequency coordinate) (q coordinate)) = _
  calc
    ∑ frequency ∈ Fintype.piFinset
        (fun _ : Fin 3 ↦ Finset.Icc (0 : ℤ) (radius : ℤ)),
          ∏ coordinate : Fin 3, fourier (frequency coordinate) (q coordinate) =
        ∏ coordinate : Fin 3,
          ∑ frequency ∈ Finset.Icc (0 : ℤ) (radius : ℤ),
            fourier frequency (q coordinate) :=
      Finset.sum_prod_piFinset
        (R := ℂ) (ι := Fin 3)
        (Finset.Icc (0 : ℤ) (radius : ℤ))
        (fun coordinate frequency ↦ fourier frequency (q coordinate))
    _ = ∏ coordinate : Fin 3,
          ∑ index ∈ Finset.range (radius + 1),
            fourier (index : ℤ) (q coordinate) := by
      apply Finset.prod_congr rfl
      intro coordinate _hcoordinate
      exact sum_fourier_Icc_zero_natCast_eq_range radius (q coordinate)

/-- The normalized rectangular norm-square is the product of its normalized coordinate
norm-squares. -/
theorem averagedTensorFejerKernel_apply_eq_prod_averagedCoordinateFejerKernel
    (radius : ℕ) (q : SpatialTorus) :
    averagedTensorFejerKernel radius q =
      ∏ coordinate : Fin 3, averagedCoordinateFejerKernel radius (q coordinate) := by
  rw [averagedTensorFejerKernel_apply,
    rectangularDirichletSum_apply_eq_prod_coordinateDirichletSum,
    card_positiveFrequencyCube]
  simp only [averagedCoordinateFejerKernel, ContinuousMap.coe_mk]
  simp only [Fin.prod_univ_three, Complex.normSq_mul]
  push_cast
  have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exact bridge.**  The normalized Dirichlet norm-square is pointwise identical to the
previously synthesized closed tensor-hat multiplier. -/
theorem tensorHatKernel_eq_averagedTensorFejerKernel (radius : ℕ) :
    tensorHatKernel radius = averagedTensorFejerKernel radius := by
  ext q
  rw [tensorHatKernel_apply_eq_prod_coordinateHatKernel,
    averagedTensorFejerKernel_apply_eq_prod_averagedCoordinateFejerKernel]
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  exact congrArg (fun kernel : C(UnitAddCircle, ℂ) ↦ kernel (q coordinate))
    (coordinateHatKernel_eq_averagedCoordinateFejerKernel radius)

/-! ## Three-dimensional ordered-difference multiplicity -/

/-- Ordered pairs of positive-cube frequencies with the addressed vector difference. -/
def orderedDifferencePairs
    (radius : ℕ) (frequency : SpatialFrequency) :
    Finset (SpatialFrequency × SpatialFrequency) :=
  (positiveFrequencyCube radius ×ˢ positiveFrequencyCube radius).filter
    (fun pair ↦ pair.2 - pair.1 = frequency)

/-- The averaged tensor kernel expands into the normalized finite population of ordered
frequency differences. -/
theorem averagedTensorFejerKernel_eq_orderedDifferenceSum
    (radius : ℕ) (q : SpatialTorus) :
    averagedTensorFejerKernel radius q =
      ((positiveFrequencyCube radius).card : ℂ)⁻¹ *
        ∑ pair ∈
            (positiveFrequencyCube radius ×ˢ positiveFrequencyCube radius),
          UnitAddTorus.mFourier (pair.2 - pair.1) q := by
  rw [averagedTensorFejerKernel_apply]
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  simp only [rectangularDirichletSum, ContinuousMap.sum_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _hfirst
  apply Finset.sum_congr rfl
  intro second _hsecond
  congr 1
  rw [← UnitAddTorus.mFourier_neg, ← UnitAddTorus.mFourier_add]
  congr 2
  module

/-- The Fourier coefficient of the averaged square is its normalized ordered-difference
multiplicity. -/
theorem mFourierCoeff_averagedTensorFejerKernel
    (radius : ℕ) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ averagedTensorFejerKernel radius q) frequency =
      ((orderedDifferencePairs radius frequency).card : ℂ) /
        (positiveFrequencyCube radius).card := by
  rw [UnitAddTorus.mFourierCoeff]
  simp_rw [averagedTensorFejerKernel_eq_orderedDifferenceSum, smul_eq_mul]
  have hreorder : ∀ q : SpatialTorus,
      UnitAddTorus.mFourier (-frequency) q *
          (((positiveFrequencyCube radius).card : ℂ)⁻¹ *
            ∑ pair ∈
                (positiveFrequencyCube radius ×ˢ positiveFrequencyCube radius),
              UnitAddTorus.mFourier (pair.2 - pair.1) q) =
        ((positiveFrequencyCube radius).card : ℂ)⁻¹ *
          ∑ pair ∈
              (positiveFrequencyCube radius ×ˢ positiveFrequencyCube radius),
            UnitAddTorus.mFourier (-frequency) q *
              UnitAddTorus.mFourier (pair.2 - pair.1) q := by
    intro q
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pair _hpair
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hreorder), integral_const_mul]
  have hintegrable : ∀ pair ∈
      (positiveFrequencyCube radius ×ˢ positiveFrequencyCube radius),
      Integrable (fun q : SpatialTorus ↦
        UnitAddTorus.mFourier (-frequency) q *
          UnitAddTorus.mFourier (pair.2 - pair.1) q) := by
    intro pair _hpair
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-frequency) q *
            UnitAddTorus.mFourier (pair.2 - pair.1) q
        continuous_toFun := by fun_prop }
  rw [integral_finset_sum _ hintegrable]
  simp_rw [integral_mFourier_neg_mul_mFourier]
  simp [orderedDifferencePairs, Finset.sum_boole, div_eq_mul_inv, mul_comm, eq_comm]

/-- The normalized three-dimensional multiplicity is exactly the existing tensor-hat weight on
the admitted cube. -/
theorem card_orderedDifferencePairs_div_card_eq_tensorHatWeight
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) :
    ((orderedDifferencePairs radius frequency).card : ℂ) /
        (positiveFrequencyCube radius).card =
      (tensorHatWeight radius frequency : ℂ) := by
  calc
    ((orderedDifferencePairs radius frequency).card : ℂ) /
          (positiveFrequencyCube radius).card =
        UnitAddTorus.mFourierCoeff
          (fun q : SpatialTorus ↦ averagedTensorFejerKernel radius q) frequency :=
      (mFourierCoeff_averagedTensorFejerKernel radius frequency).symm
    _ = UnitAddTorus.mFourierCoeff
          (fun q : SpatialTorus ↦ tensorHatKernel radius q) frequency := by
      rw [tensorHatKernel_eq_averagedTensorFejerKernel]
    _ = (tensorHatWeight radius frequency : ℂ) := by
      simpa [hfrequency] using mFourierCoeff_tensorHatKernel radius frequency

/-- **Exact three-dimensional multiplicity.**  Inside the radius-`N` cube, independent
coordinate fibres multiply, giving the product of the three inclusive counts
`N + 1 - |k_i|`. -/
theorem card_orderedDifferencePairs
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) :
    (orderedDifferencePairs radius frequency).card =
      ∏ coordinate : Fin 3, (radius + 1 - (frequency coordinate).natAbs) := by
  have hcoordinate : ∀ coordinate : Fin 3,
      (frequency coordinate).natAbs ≤ radius := by
    intro coordinate
    have hbounds := (mem_frequencyCube_iff radius frequency).mp hfrequency coordinate
    have habsInt : ((frequency coordinate).natAbs : ℤ) ≤ (radius : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr hbounds
    exact_mod_cast habsInt
  have hnormalized :=
    card_orderedDifferencePairs_div_card_eq_tensorHatWeight radius hfrequency
  have hcast :
      ((((orderedDifferencePairs radius frequency).card : ℝ) /
          ((positiveFrequencyCube radius).card : ℝ) : ℝ) : ℂ) =
        (tensorHatWeight radius frequency : ℂ) := by
    push_cast
    exact hnormalized
  have hreal := Complex.ofReal_injective hcast
  rw [card_positiveFrequencyCube] at hreal
  simp only [tensorHatWeight] at hreal
  simp_rw [coordinateHatWeight, if_pos (hcoordinate _)] at hreal
  simp only [Fin.prod_univ_three] at hreal
  push_cast at hreal
  have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
  field_simp at hreal
  have hnat :
      (orderedDifferencePairs radius frequency).card =
        (radius + 1 - (frequency 0).natAbs) *
          (radius + 1 - (frequency 1).natAbs) *
            (radius + 1 - (frequency 2).natAbs) := by
    exact_mod_cast hreal
  simpa only [Fin.prod_univ_three] using hnat

/-! ## Physical transport to the existing closed multiplier -/

/-- The existing tensor-hat kernel is explicitly the same normalized rectangular norm-square. -/
theorem tensorHatKernel_apply_eq_normalized_normSq
    (radius : ℕ) (q : SpatialTorus) :
    tensorHatKernel radius q =
      (((positiveFrequencyCube radius).card : ℝ)⁻¹ *
        Complex.normSq (rectangularDirichletSum radius q) : ℝ) := by
  rw [tensorHatKernel_eq_averagedTensorFejerKernel,
    averagedTensorFejerKernel_apply]

/-- The existing closed multiplier is real-valued. -/
@[simp]
theorem tensorHatKernel_im (radius : ℕ) (q : SpatialTorus) :
    (tensorHatKernel radius q).im = 0 := by
  rw [tensorHatKernel_eq_averagedTensorFejerKernel]
  exact averagedTensorFejerKernel_im radius q

/-- **Physical nonnegativity of the existing closed multiplier.** -/
theorem tensorHatKernel_re_nonneg (radius : ℕ) (q : SpatialTorus) :
    0 ≤ (tensorHatKernel radius q).re := by
  rw [tensorHatKernel_eq_averagedTensorFejerKernel]
  exact averagedTensorFejerKernel_re_nonneg radius q

/-- **Exact physical `L1` mass of the existing closed multiplier.** -/
theorem integral_norm_tensorHatKernel (radius : ℕ) :
    ∫ q : SpatialTorus, ‖tensorHatKernel radius q‖ = 1 := by
  simp_rw [tensorHatKernel_eq_averagedTensorFejerKernel]
  exact integral_norm_averagedTensorFejerKernel radius

/-- **Scale-uniform physical contraction for the existing closed multiplier.**  The pointwise
uniform bound has radius-independent constant one.  The integral is stated directly so the
normalized averaged-square convolution remains the sole named owner of this operation. -/
theorem norm_tensorHatKernel_convolution_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (radius : ℕ) (field : C(SpatialTorus, E)) (q : SpatialTorus) :
    ‖∫ y : SpatialTorus, tensorHatKernel radius y • field (q - y)‖ ≤ ‖field‖ := by
  simpa only [tensorHatKernel_eq_averagedTensorFejerKernel,
    averagedTensorFejerConvolution, torusKernelConvolution] using
    norm_averagedTensorFejerConvolution_le radius field q

section Audit

#print axioms card_coordinateDifferencePairs
#print axioms coordinateHatKernel_eq_averagedCoordinateFejerKernel
#print axioms tensorHatKernel_eq_averagedTensorFejerKernel
#print axioms card_orderedDifferencePairs
#print axioms tensorHatKernel_re_nonneg
#print axioms integral_norm_tensorHatKernel
#print axioms norm_tensorHatKernel_convolution_le

end Audit


end Soma.Holonics.Millennium.NavierStokesFejerDifferenceBridge
