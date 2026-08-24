import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors

/-!
# A finite tensor Fejer multiplier on the periodic three-torus

**[proved-derived]** This owner replaces the unit weights of the sharp frequency cube by the
explicit tensor hat

`prod i, (radius + 1 - |k i|) / (radius + 1)`

on the same finite integer carrier.  The multiplier is therefore `1` at the zero mode, decreases
linearly in every coordinate, and reaches `1 / (radius + 1)` at the center of a coordinate face;
products can be smaller elsewhere on that face.  Genuine torus Haar orthogonality gives its exact
coefficient action.  The pointwise synthesis map has norm at most one from the coefficient `l1`
receiver, uniformly in the radius.  Its scalar kernel has mean one and cancels every character
outside the admitted cube.

**[open]** The coefficient-`l1` contraction below is not a physical-space kernel `L1` theorem.
Although this tensor hat is the finite Fejer multiplier, a proof here that its torus kernel is
pointwise nonnegative (equivalently, a normalized square of rectangular Dirichlet sums) would be
needed before claiming the scale-uniform convolution `L-infinity` bound used by the continuation
line.  No such claim is made in this file.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesFejerMultiplier

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors

/- Keep the probability-Haar chart used by the existing torus Fourier owners. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Explicit tensor hat -/

/-- The one-coordinate Fejer hat.  The Boolean branch makes its finite support explicit instead
of using truncated subtraction as an implicit aperture. -/
def coordinateHatWeight (radius : ℕ) (frequency : ℤ) : ℝ :=
  if frequency.natAbs ≤ radius then
    ((radius + 1 - frequency.natAbs : ℕ) : ℝ) / (radius + 1 : ℝ)
  else
    0

/-- Every coordinate hat is nonnegative. -/
theorem coordinateHatWeight_nonneg (radius : ℕ) (frequency : ℤ) :
    0 ≤ coordinateHatWeight radius frequency := by
  unfold coordinateHatWeight
  split_ifs
  · positivity
  · exact le_rfl

/-- No coordinate hat amplifies a coefficient. -/
theorem coordinateHatWeight_le_one (radius : ℕ) (frequency : ℤ) :
    coordinateHatWeight radius frequency ≤ 1 := by
  unfold coordinateHatWeight
  split_ifs with h
  · apply (div_le_one (by positivity)).2
    exact_mod_cast Nat.sub_le (radius + 1) frequency.natAbs
  · norm_num

/-- The coordinate hat preserves the zero frequency exactly. -/
@[simp]
theorem coordinateHatWeight_zero (radius : ℕ) :
    coordinateHatWeight radius 0 = 1 := by
  have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
  simp [coordinateHatWeight, Nat.cast_add, hdenominator]

/-- The coordinate face receives the explicit tapered weight `1 / (radius + 1)`. -/
theorem coordinateHatWeight_natCast_radius (radius : ℕ) :
    coordinateHatWeight radius (radius : ℤ) = 1 / (radius + 1 : ℝ) := by
  simp [coordinateHatWeight]

/-- The three-dimensional tensor Fejer hat on the actual integer character lattice. -/
def tensorHatWeight (radius : ℕ) (frequency : SpatialFrequency) : ℝ :=
  ∏ coordinate : Fin 3, coordinateHatWeight radius (frequency coordinate)

/-- Tensor weights are nonnegative. -/
theorem tensorHatWeight_nonneg (radius : ℕ) (frequency : SpatialFrequency) :
    0 ≤ tensorHatWeight radius frequency := by
  exact Finset.prod_nonneg fun coordinate _ ↦
    coordinateHatWeight_nonneg radius (frequency coordinate)

/-- Tensor weights are bounded by one independently of the aperture. -/
theorem tensorHatWeight_le_one (radius : ℕ) (frequency : SpatialFrequency) :
    tensorHatWeight radius frequency ≤ 1 := by
  apply Finset.prod_le_one
  · intro coordinate _
    exact coordinateHatWeight_nonneg radius (frequency coordinate)
  · intro coordinate _
    exact coordinateHatWeight_le_one radius (frequency coordinate)

/-- The tensor hat preserves the zero mode. -/
@[simp]
theorem tensorHatWeight_zero (radius : ℕ) :
    tensorHatWeight radius 0 = 1 := by
  simp [tensorHatWeight]

/-! ## Exact finite synthesis and coefficient action -/

/-- Finite synthesis after applying the tensor Fejer hat to every admitted coefficient. -/
def tensorHatSynthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (radius : ℕ) : C(SpatialTorus, E) :=
  finiteFourierSynthesis
    (fun frequency ↦ (tensorHatWeight radius frequency : ℂ) • coeff frequency)
    (frequencyCube radius)

/-- **Exact multiplier receipt.**  Every admitted torus coefficient is multiplied by the explicit
tensor hat, while every coefficient outside the declared finite carrier is zero. -/
theorem mFourierCoeff_tensorHatSynthesis
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (coeff : SpatialFrequency → E) (radius : ℕ) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorHatSynthesis coeff radius q) frequency =
      if frequency ∈ frequencyCube radius then
        (tensorHatWeight radius frequency : ℂ) • coeff frequency
      else 0 := by
  exact mFourierCoeff_finiteFourierSynthesis _ _ _

/-- Exact finite synthesis in pointwise form. -/
theorem tensorHatSynthesis_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (radius : ℕ) (q : SpatialTorus) :
    tensorHatSynthesis coeff radius q =
      ∑ frequency ∈ frequencyCube radius,
        UnitAddTorus.mFourier frequency q •
          ((tensorHatWeight radius frequency : ℂ) • coeff frequency) := rfl

/-- Pointwise synthesis is bounded by the explicitly weighted coefficient population. -/
theorem norm_tensorHatSynthesis_le_weighted_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (radius : ℕ) (q : SpatialTorus) :
    ‖tensorHatSynthesis coeff radius q‖ ≤
      ∑ frequency ∈ frequencyCube radius,
        tensorHatWeight radius frequency * ‖coeff frequency‖ := by
  refine (norm_finiteFourierSynthesis_le_sum_norm
    (fun frequency ↦ (tensorHatWeight radius frequency : ℂ) • coeff frequency)
    (frequencyCube radius) q).trans_eq ?_
  apply Finset.sum_congr rfl
  intro frequency _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tensorHatWeight_nonneg radius frequency)]

/-- **Scale-uniform coefficient-side contraction.**  Replacing the sharp unit multiplier by the
tensor hat never enlarges the pointwise coefficient `l1` bound; the constant is exactly one and
does not depend on `radius`. -/
theorem norm_tensorHatSynthesis_le_sum_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (radius : ℕ) (q : SpatialTorus) :
    ‖tensorHatSynthesis coeff radius q‖ ≤
      ∑ frequency ∈ frequencyCube radius, ‖coeff frequency‖ := by
  refine (norm_tensorHatSynthesis_le_weighted_sum coeff radius q).trans ?_
  apply Finset.sum_le_sum
  intro frequency _
  exact mul_le_of_le_one_left (norm_nonneg _) (tensorHatWeight_le_one radius frequency)

/-! ## Normalization and cancellation of the scalar kernel -/

/-- The scalar trigonometric kernel carrying the tensor hat multiplier. -/
def tensorHatKernel (radius : ℕ) : C(SpatialTorus, ℂ) :=
  tensorHatSynthesis (fun _ ↦ (1 : ℂ)) radius

/-- Every kernel coefficient is exactly the declared tensor hat. -/
theorem mFourierCoeff_tensorHatKernel (radius : ℕ) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorHatKernel radius q) frequency =
      if frequency ∈ frequencyCube radius then
        (tensorHatWeight radius frequency : ℂ)
      else 0 := by
  simpa [tensorHatKernel] using
    mFourierCoeff_tensorHatSynthesis (fun _ : SpatialFrequency ↦ (1 : ℂ)) radius frequency

/-- **Normalization receipt.**  The zero coefficient, hence the probability-Haar mean, is one at
every aperture. -/
theorem integral_tensorHatKernel (radius : ℕ) :
    ∫ q : SpatialTorus, tensorHatKernel radius q = 1 := by
  have h := mFourierCoeff_tensorHatKernel radius (0 : SpatialFrequency)
  rw [UnitAddTorus.mFourierCoeff] at h
  simpa [UnitAddTorus.mFourier_zero, mem_frequencyCube_iff] using h

/-- **Cancellation receipt.**  Every character outside the finite cube pairs to zero with the
kernel. -/
theorem mFourierCoeff_tensorHatKernel_eq_zero_of_not_mem_frequencyCube
    (radius : ℕ) (frequency : SpatialFrequency)
    (hfrequency : frequency ∉ frequencyCube radius) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorHatKernel radius q) frequency = 0 := by
  simp [mFourierCoeff_tensorHatKernel, hfrequency]

/-- The smoothing preserves the mean coefficient of every finite coefficient population. -/
theorem mFourierCoeff_tensorHatSynthesis_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (coeff : SpatialFrequency → E) (radius : ℕ) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ tensorHatSynthesis coeff radius q) 0 = coeff 0 := by
  simp [mFourierCoeff_tensorHatSynthesis, mem_frequencyCube_iff]

section Audit

#print axioms mFourierCoeff_tensorHatSynthesis
#print axioms norm_tensorHatSynthesis_le_sum_norm
#print axioms integral_tensorHatKernel
#print axioms mFourierCoeff_tensorHatKernel_eq_zero_of_not_mem_frequencyCube
#print axioms mFourierCoeff_tensorHatSynthesis_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesFejerMultiplier
