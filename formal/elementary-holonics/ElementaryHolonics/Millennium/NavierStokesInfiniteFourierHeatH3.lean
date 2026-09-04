import ElementaryHolonics.Millennium.NavierStokesInfiniteFourierHeat

/-!
# The positive-time `H³` heat squeeze and its vector Fourier constraints

The predecessor constructed the infinite diagonal heat semigroup on Mathlib's genuine
`L²(T³) ≃ ℓ²(ℤ³, ℂ)` Fourier Hilbert representation and proved one-order smoothing.  This
owner splits a positive elapsed time into three equal diagonal passages.  Cubing the predecessor's
one-order pointwise estimate returns an explicit third-order Sobolev estimate with squared-norm
constant

`(1 + (2 * (nu * (t / 3)))⁻¹) ^ 3`,

which has the required `t⁻³` positive-time singularity for the squared `H³` receiver (equivalently
`t⁻³⁄²` after taking square roots).

The same diagonal action is then applied to three scalar Hilbert coefficient carriers.  Their
modewise assembly preserves the zero mode and every Fourier divergence constraint.  No strong
continuity, generator-domain identity, heat PDE, nonlinear fixed point, or Navier--Stokes local
existence theorem is asserted.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal lp

namespace Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat

/-- [definition] The explicit squared `L² → H³` heat-squeeze constant. -/
def heatH3SquaredConstant (nu t : ℝ) : ℝ :=
  (1 + (2 * (nu * (t / 3)))⁻¹) ^ 3

/-- [proved-derived] One full heat multiplier is exactly three equal-time multipliers in
series. -/
theorem heatStokesMultiplier_eq_cube_third_time
    (nu t : ℝ) (k : SpatialFrequency) :
    heatStokesMultiplier nu t k =
      (heatStokesMultiplier nu (t / 3) k) ^ 3 := by
  rw [heatStokesMultiplier, heatStokesMultiplier, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- [proved-derived] The order-three weighted multiplier is the cube of the order-one weighted
multiplier at one third of the elapsed time. -/
theorem periodicSobolevWeight_three_mul_heat_sq_eq_cube
    (nu t : ℝ) (k : SpatialFrequency) :
    periodicSobolevWeight 3 k * (heatStokesMultiplier nu t k) ^ 2 =
      (periodicSobolevWeight 1 k *
        (heatStokesMultiplier nu (t / 3) k) ^ 2) ^ 3 := by
  rw [heatStokesMultiplier_eq_cube_third_time]
  simp only [periodicSobolevWeight, pow_one]
  ring

/-- [proved-derived] Explicit pointwise third-order heat squeeze. -/
theorem periodicSobolevWeight_three_mul_heat_sq_le
    {nu t : ℝ} (hviscous : 0 < nu * t) (k : SpatialFrequency) :
    periodicSobolevWeight 3 k * (heatStokesMultiplier nu t k) ^ 2 ≤
      heatH3SquaredConstant nu t := by
  have hthird : 0 < nu * (t / 3) := by
    nlinarith
  have hone := periodicSobolevWeight_one_mul_heat_sq_le hthird k
  have hcubed := pow_le_pow_left₀
    (mul_nonneg (periodicSobolevWeight_nonneg 1 k)
      (sq_nonneg (heatStokesMultiplier nu (t / 3) k))) hone 3
  rw [periodicSobolevWeight_three_mul_heat_sq_eq_cube]
  exact hcubed

/-- [proved-derived] Positive viscous time sends every Fourier `ℓ²` population into the honest
third-order periodic Sobolev coefficient carrier. -/
theorem infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) :
    HasPeriodicSobolevCoefficients 3
      (infiniteHeatCoefficientEvolution nu t coeff) := by
  let C := heatH3SquaredConstant (nu : ℝ) (t : ℝ)
  have hsource : Summable (fun k ↦ C * ‖coeff k‖ ^ 2) := by
    have hcoeff := (lp.memℓp coeff).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hcoeffSq : Summable (fun k ↦ ‖coeff k‖ ^ 2) := by simpa using hcoeff
    exact hcoeffSq.mul_left C
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hsource
  · exact mul_nonneg (periodicSobolevWeight_nonneg 3 k) (sq_nonneg _)
  · have hmode := periodicSobolevWeight_three_mul_heat_sq_le hviscous k
    calc
      periodicSobolevWeight 3 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 =
          (periodicSobolevWeight 3 k *
            (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
              ‖coeff k‖ ^ 2 := by
            have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
              (Real.exp_pos _).le
            simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg hm0]
            ring
      _ ≤ C * ‖coeff k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)

/-- [proved-derived] Complete `H³` squared-coefficient estimate with the correct positive-time
singularity. -/
theorem tsum_periodicSobolevWeight_three_infiniteHeat_le
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) :
    (∑' k, periodicSobolevWeight 3 k *
        ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2) ≤
      heatH3SquaredConstant (nu : ℝ) (t : ℝ) * ‖coeff‖ ^ 2 := by
  let C := heatH3SquaredConstant (nu : ℝ) (t : ℝ)
  have hsmooth :=
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three nu t hviscous coeff
  have hcoeff := (lp.memℓp coeff).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hcoeffSq : Summable (fun k ↦ ‖coeff k‖ ^ 2) := by simpa using hcoeff
  have hsource : Summable (fun k ↦ C * ‖coeff k‖ ^ 2) := hcoeffSq.mul_left C
  have hpoint : ∀ k,
      periodicSobolevWeight 3 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 ≤
        C * ‖coeff k‖ ^ 2 := by
    intro k
    have hmode := periodicSobolevWeight_three_mul_heat_sq_le hviscous k
    calc
      periodicSobolevWeight 3 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 =
          (periodicSobolevWeight 3 k *
            (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
              ‖coeff k‖ ^ 2 := by
            have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
              (Real.exp_pos _).le
            simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg hm0]
            ring
      _ ≤ C * ‖coeff k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)
  have hnormSq : (∑' k, ‖coeff k‖ ^ 2) = ‖coeff‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) coeff
    simpa using h.symm
  calc
    (∑' k, periodicSobolevWeight 3 k *
        ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2) ≤
        ∑' k, C * ‖coeff k‖ ^ 2 :=
      hsmooth.tsum_le_tsum hpoint hsource
    _ = C * (∑' k, ‖coeff k‖ ^ 2) := hcoeffSq.tsum_mul_left C
    _ = C * ‖coeff‖ ^ 2 := by rw [hnormSq]

/-- [definition] The positive-time heat return packaged in the third-order Sobolev coefficient
carrier. -/
def infiniteHeatIntoPeriodicSobolevThree
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) : PeriodicSobolevCoefficients 3 :=
  ⟨infiniteHeatCoefficientEvolution nu t coeff,
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three nu t hviscous coeff⟩

/-! ## Componentwise vector carrier -/

/-- [definition] Three scalar Fourier Hilbert carriers assembled without discarding any mode or
component. -/
abbrev PeriodicVectorFourierL2 := Fin 3 → PeriodicFourierL2

/-- [definition] The complex three-vector carried by one addressed frequency. -/
def vectorCoefficientAt
    (state : PeriodicVectorFourierL2) (k : SpatialFrequency) : ComplexVector :=
  fun component ↦ state component k

/-- [definition] Componentwise infinite diagonal heat action. -/
def infiniteVectorHeatCoefficientEvolution
    (nu t : ℝ≥0) (state : PeriodicVectorFourierL2) : PeriodicVectorFourierL2 :=
  fun component ↦ infiniteHeatCoefficientEvolution nu t (state component)

/-- [proved-derived] At each frequency, the complete vector coefficient is scaled by the same
diagonal heat multiplier. -/
theorem vectorCoefficientAt_infiniteVectorHeatCoefficientEvolution
    (nu t : ℝ≥0) (state : PeriodicVectorFourierL2) (k : SpatialFrequency) :
    vectorCoefficientAt (infiniteVectorHeatCoefficientEvolution nu t state) k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) •
        vectorCoefficientAt state k := by
  funext component
  rfl

/-- [proved-derived] The infinite heat passage preserves the complete zero-frequency vector. -/
theorem vectorCoefficientAt_zero_infiniteVectorHeatCoefficientEvolution
    (nu t : ℝ≥0) (state : PeriodicVectorFourierL2) :
    vectorCoefficientAt (infiniteVectorHeatCoefficientEvolution nu t state) 0 =
      vectorCoefficientAt state 0 := by
  rw [vectorCoefficientAt_infiniteVectorHeatCoefficientEvolution]
  simp

/-- [definition] Exact Fourier incompressibility on every mode of the complete vector carrier. -/
def IsModewiseDivergenceFree (state : PeriodicVectorFourierL2) : Prop :=
  ∀ k, complexDot (complexFrequencyVector k) (vectorCoefficientAt state k) = 0

/-- [proved-derived] The scalar diagonal heat action preserves every vector Fourier divergence
constraint. -/
theorem infiniteVectorHeatCoefficientEvolution_preserves_divergenceFree
    {state : PeriodicVectorFourierL2} (hstate : IsModewiseDivergenceFree state)
    (nu t : ℝ≥0) :
    IsModewiseDivergenceFree (infiniteVectorHeatCoefficientEvolution nu t state) := by
  intro k
  rw [vectorCoefficientAt_infiniteVectorHeatCoefficientEvolution]
  simp only [complexDot, dotProduct_smul, smul_eq_mul]
  change (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
      complexDot (complexFrequencyVector k) (vectorCoefficientAt state k) = 0
  rw [hstate k, mul_zero]

/-- [proved-derived] The componentwise vector action retains the exact infinite semigroup law. -/
theorem infiniteVectorHeatCoefficientEvolution_add
    (nu s t : ℝ≥0) (state : PeriodicVectorFourierL2) :
    infiniteVectorHeatCoefficientEvolution nu (s + t) state =
      infiniteVectorHeatCoefficientEvolution nu s
        (infiniteVectorHeatCoefficientEvolution nu t state) := by
  funext component
  exact infiniteHeatCoefficientEvolution_add nu s t (state component)

/-- [proved-derived] Every component of the positive-time vector return lies in the third-order
periodic Sobolev carrier. -/
theorem infiniteVectorHeatCoefficientEvolution_hasPeriodicSobolev_three
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicVectorFourierL2) :
    ∀ component,
      HasPeriodicSobolevCoefficients 3
        (infiniteVectorHeatCoefficientEvolution nu t state component) := by
  intro component
  exact infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three
    nu t hviscous (state component)

#print axioms heatStokesMultiplier_eq_cube_third_time
#print axioms periodicSobolevWeight_three_mul_heat_sq_le
#print axioms infiniteHeatCoefficientEvolution_hasPeriodicSobolev_three
#print axioms tsum_periodicSobolevWeight_three_infiniteHeat_le
#print axioms vectorCoefficientAt_zero_infiniteVectorHeatCoefficientEvolution
#print axioms infiniteVectorHeatCoefficientEvolution_preserves_divergenceFree
#print axioms infiniteVectorHeatCoefficientEvolution_add

end Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
