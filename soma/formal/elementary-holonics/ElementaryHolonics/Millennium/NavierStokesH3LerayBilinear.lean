import ElementaryHolonics.Millennium.NavierStokesH3DivergenceBilinear
import Mathlib.Algebra.Order.Chebyshev

/-!
# Leray projection on the periodic `H²` Fourier carrier

This owner applies the predecessor's exact modewise Leray face to a complete vector `H²`
population.  A uniform finite-dimensional estimate is proved directly from the three integer
frequency coordinates: every projected output coordinate has squared norm at most twelve times
the sum of the three input squared norms.  Consequently modewise Leray projection preserves the
weighted `H²` carrier and annihilates the exact Fourier divergence.

The construction is then composed with the already-founded divergence-form
`H³ × H³ → H²` bilinear passage.  No heat/Duhamel or local-existence conclusion is introduced.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH3LerayBilinear

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear

/-! ## Uniform modewise projection bound -/

/-- [proved-derived] The product of any two absolute frequency coordinates is bounded by the
complete squared frequency. -/
theorem abs_frequency_coordinate_mul_abs_frequency_coordinate_le
    (k : SpatialFrequency) (first second : Fin 3) :
    |(k first : ℝ)| * |(k second : ℝ)| ≤ frequencySquared k := by
  have hfirst : (k first : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ first)
  have hsecond : (k second : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ second)
  nlinarith [sq_nonneg (|(k first : ℝ)| - |(k second : ℝ)|),
    sq_abs (k first : ℝ), sq_abs (k second : ℝ)]

/-- [proved-derived] The bilinear frequency dot receiver is bounded by the componentwise
weighted norm sum. -/
theorem norm_complexDot_frequency_le_sum
    (k : SpatialFrequency) (mode : ComplexVector) :
    ‖complexDot (complexFrequencyVector k) mode‖ ≤
      ∑ component : Fin 3, |(k component : ℝ)| * ‖mode component‖ := by
  unfold complexDot dotProduct complexFrequencyVector
  calc
    ‖∑ component : Fin 3, (k component : ℂ) * mode component‖ ≤
        ∑ component : Fin 3, ‖(k component : ℂ) * mode component‖ :=
      norm_sum_le _ _
    _ = ∑ component : Fin 3, |(k component : ℝ)| * ‖mode component‖ := by
      apply Finset.sum_congr rfl
      intro component _
      simp only [norm_mul, Complex.norm_intCast]

private theorem norm_leray_correction_coordinate_le_sum
    {k : SpatialFrequency} (hk : k ≠ 0) (mode : ComplexVector) (output : Fin 3) :
    ‖(complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
        (k output : ℂ)‖ ≤
      ∑ component : Fin 3, ‖mode component‖ := by
  have hsPos : 0 < frequencySquared k := frequencySquared_pos hk
  have hdot := norm_complexDot_frequency_le_sum k mode
  calc
    ‖(complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
        (k output : ℂ)‖ =
        (‖complexDot (complexFrequencyVector k) mode‖ / frequencySquared k) *
          |(k output : ℝ)| := by
      simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hsPos, Complex.norm_intCast]
    _ ≤ ((∑ component : Fin 3, |(k component : ℝ)| * ‖mode component‖) /
          frequencySquared k) * |(k output : ℝ)| :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hdot hsPos.le) (abs_nonneg _)
    _ = ∑ component : Fin 3,
        ((|(k component : ℝ)| * |(k output : ℝ)|) / frequencySquared k) *
          ‖mode component‖ := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ ≤ ∑ component : Fin 3, ‖mode component‖ := by
      apply Finset.sum_le_sum
      intro component _
      have hratio :
          (|(k component : ℝ)| * |(k output : ℝ)|) / frequencySquared k ≤ 1 :=
        (div_le_one hsPos).2
          (abs_frequency_coordinate_mul_abs_frequency_coordinate_le k component output)
      calc
        ((|(k component : ℝ)| * |(k output : ℝ)|) / frequencySquared k) *
            ‖mode component‖ ≤ 1 * ‖mode component‖ :=
          mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
        _ = ‖mode component‖ := one_mul _

/-- [proved-derived] With the component-sum receiver, the exact Leray projection has the uniform
finite-dimensional constant two. -/
theorem norm_lerayProjectMode_coordinate_le
    (k : SpatialFrequency) (mode : ComplexVector) (output : Fin 3) :
    ‖lerayProjectMode k mode output‖ ≤
      2 * ∑ component : Fin 3, ‖mode component‖ := by
  by_cases hk : k = 0
  · subst k
    rw [lerayProjectMode_zero]
    have hsingle : ‖mode output‖ ≤ ∑ component : Fin 3, ‖mode component‖ :=
      Finset.single_le_sum (fun component _ ↦ norm_nonneg (mode component))
        (Finset.mem_univ output)
    have hsum : 0 ≤ ∑ component : Fin 3, ‖mode component‖ :=
      Finset.sum_nonneg fun component _ ↦ norm_nonneg (mode component)
    nlinarith
  · rw [lerayProjectMode, if_neg hk]
    change ‖mode output -
        (complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
          (k output : ℂ)‖ ≤ _
    have hsingle : ‖mode output‖ ≤ ∑ component : Fin 3, ‖mode component‖ :=
      Finset.single_le_sum (fun component _ ↦ norm_nonneg (mode component))
        (Finset.mem_univ output)
    have hcorrection := norm_leray_correction_coordinate_le_sum hk mode output
    calc
      ‖mode output -
          (complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
            (k output : ℂ)‖ ≤
          ‖mode output‖ +
            ‖(complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
              (k output : ℂ)‖ := norm_sub_le _ _
      _ ≤ (∑ component : Fin 3, ‖mode component‖) +
          ∑ component : Fin 3, ‖mode component‖ :=
        add_le_add hsingle hcorrection
      _ = 2 * ∑ component : Fin 3, ‖mode component‖ := by ring

/-- [proved-derived] Squaring the coordinate estimate and using finite Cauchy--Schwarz gives the
explicit constant twelve against componentwise squared norms. -/
theorem norm_lerayProjectMode_coordinate_sq_le
    (k : SpatialFrequency) (mode : ComplexVector) (output : Fin 3) :
    ‖lerayProjectMode k mode output‖ ^ 2 ≤
      12 * ∑ component : Fin 3, ‖mode component‖ ^ 2 := by
  have hmode := norm_lerayProjectMode_coordinate_le k mode output
  have hsquare :
      ‖lerayProjectMode k mode output‖ ^ 2 ≤
        (2 * ∑ component : Fin 3, ‖mode component‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hmode 2
  have hcauchy :
      (∑ component : Fin 3, ‖mode component‖) ^ 2 ≤
        3 * ∑ component : Fin 3, ‖mode component‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 3))) (f := fun component ↦ ‖mode component‖))
  calc
    ‖lerayProjectMode k mode output‖ ^ 2 ≤
        (2 * ∑ component : Fin 3, ‖mode component‖) ^ 2 := hsquare
    _ = 4 * (∑ component : Fin 3, ‖mode component‖) ^ 2 := by ring
    _ ≤ 4 * (3 * ∑ component : Fin 3, ‖mode component‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ = 12 * ∑ component : Fin 3, ‖mode component‖ ^ 2 := by ring

/-! ## Projection of the complete weighted carrier -/

/-- [definition] Three complete scalar `H²` populations with their component addresses retained. -/
abbrev PeriodicVectorSobolevTwo := Fin 3 → PeriodicSobolevCoefficients 2

private theorem summable_vectorFourier_sq (state : PeriodicVectorSobolevTwo) :
    Summable fun k ↦ ∑ component : Fin 3, ‖(state component).1 k‖ ^ 2 := by
  have hcomponent (component : Fin 3) :
      Summable fun k ↦ ‖(state component).1 k‖ ^ 2 := by
    have h := (lp.memℓp (state component).1).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa using h
  simpa [Fin.sum_univ_succ, add_assoc] using
    (hcomponent 0).add ((hcomponent 1).add (hcomponent 2))

private theorem summable_vectorSobolevTwo_weighted (state : PeriodicVectorSobolevTwo) :
    Summable fun k ↦ ∑ component : Fin 3,
      periodicSobolevWeight 2 k * ‖(state component).1 k‖ ^ 2 := by
  simpa [Fin.sum_univ_succ, add_assoc] using
    (state 0).2.add ((state 1).2.add (state 2).2)

/-- [definition] One output coordinate of the exact modewise Leray projection in the underlying
complete Fourier `ℓ²` carrier. -/
def lerayProjectedPeriodicVectorFourierComponent
    (state : PeriodicVectorSobolevTwo) (output : Fin 3) : PeriodicFourierL2 :=
  ⟨fun k ↦ lerayProjectMode k (fun component ↦ (state component).1 k) output, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hsource := summable_vectorFourier_sq state
    have hbound := hsource.mul_left 12
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) hbound
    simpa only [Real.rpow_two] using
      norm_lerayProjectMode_coordinate_sq_le k
        (fun component ↦ (state component).1 k) output⟩

@[simp]
theorem lerayProjectedPeriodicVectorFourierComponent_apply
    (state : PeriodicVectorSobolevTwo) (output : Fin 3) (k : SpatialFrequency) :
    lerayProjectedPeriodicVectorFourierComponent state output k =
      lerayProjectMode k (fun component ↦ (state component).1 k) output :=
  rfl

/-- [proved-derived] The uniform mode estimate preserves the complete weighted `H²` membership. -/
theorem lerayProjectedPeriodicVectorFourierComponent_hasSobolevTwo
    (state : PeriodicVectorSobolevTwo) (output : Fin 3) :
    HasPeriodicSobolevCoefficients 2
      (lerayProjectedPeriodicVectorFourierComponent state output) := by
  unfold HasPeriodicSobolevCoefficients
  have hsource := summable_vectorSobolevTwo_weighted state
  have hbound := hsource.mul_left 12
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg 2 k) (sq_nonneg _))
    (fun k ↦ ?_) hbound
  rw [lerayProjectedPeriodicVectorFourierComponent_apply]
  have hmode := norm_lerayProjectMode_coordinate_sq_le k
    (fun component ↦ (state component).1 k) output
  calc
    periodicSobolevWeight 2 k *
        ‖lerayProjectMode k (fun component ↦ (state component).1 k) output‖ ^ 2 ≤
        periodicSobolevWeight 2 k *
          (12 * ∑ component : Fin 3, ‖(state component).1 k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmode (periodicSobolevWeight_nonneg 2 k)
    _ = 12 * ∑ component : Fin 3,
        periodicSobolevWeight 2 k * ‖(state component).1 k‖ ^ 2 := by
      rw [show periodicSobolevWeight 2 k *
          (12 * ∑ component : Fin 3, ‖(state component).1 k‖ ^ 2) =
          12 * (periodicSobolevWeight 2 k *
            ∑ component : Fin 3, ‖(state component).1 k‖ ^ 2) by ring]
      rw [Finset.mul_sum]

/-- [definition] Modewise Leray projection as an endomorphism of the honest vector `H²` carrier. -/
def lerayProjectPeriodicVectorSobolevTwo
    (state : PeriodicVectorSobolevTwo) : PeriodicVectorSobolevTwo :=
  fun output ↦
    ⟨lerayProjectedPeriodicVectorFourierComponent state output,
      lerayProjectedPeriodicVectorFourierComponent_hasSobolevTwo state output⟩

/-- [definition] Forget only the weighted witness while retaining every coefficient and component. -/
def periodicVectorSobolevTwoUnderlying
    (state : PeriodicVectorSobolevTwo) : PeriodicVectorFourierL2 :=
  fun component ↦ (state component).1

/-- [proved-derived] At every addressed mode, carrier projection is exactly the predecessor's
algebraic Leray face. -/
theorem vectorCoefficientAt_lerayProjectPeriodicVectorSobolevTwo
    (state : PeriodicVectorSobolevTwo) (k : SpatialFrequency) :
    vectorCoefficientAt
        (periodicVectorSobolevTwoUnderlying (lerayProjectPeriodicVectorSobolevTwo state)) k =
      lerayProjectMode k
        (vectorCoefficientAt (periodicVectorSobolevTwoUnderlying state) k) := by
  funext output
  rfl

/-- [proved-derived] The projected complete `H²` population is exactly modewise
divergence-free. -/
theorem lerayProjectPeriodicVectorSobolevTwo_divergenceFree
    (state : PeriodicVectorSobolevTwo) :
    IsModewiseDivergenceFree
      (periodicVectorSobolevTwoUnderlying (lerayProjectPeriodicVectorSobolevTwo state)) := by
  intro k
  rw [vectorCoefficientAt_lerayProjectPeriodicVectorSobolevTwo]
  exact complexDot_lerayProjectMode_eq_zero k _

/-! ## The projected `H³ × H³ → H²` bilinear passage -/

/-- [definition] Leray projection of the complete divergence-form quadratic population. -/
def lerayProjectedH3DivergenceConvolution
    (advecting transported : PeriodicVectorSobolevThree) :
    PeriodicVectorSobolevTwo :=
  lerayProjectPeriodicVectorSobolevTwo
    (h3DivergenceConvolution advecting transported)

/-- [proved-derived] The complete projected bilinear passage satisfies the exact Fourier
divergence constraint. -/
theorem lerayProjectedH3DivergenceConvolution_divergenceFree
    (advecting transported : PeriodicVectorSobolevThree) :
    IsModewiseDivergenceFree
      (periodicVectorSobolevTwoUnderlying
        (lerayProjectedH3DivergenceConvolution advecting transported)) :=
  lerayProjectPeriodicVectorSobolevTwo_divergenceFree _

/-- [proved-derived] Exact modewise coefficient law of the projected bilinear population. -/
theorem vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
    (advecting transported : PeriodicVectorSobolevThree) (k : SpatialFrequency) :
    vectorCoefficientAt
        (periodicVectorSobolevTwoUnderlying
          (lerayProjectedH3DivergenceConvolution advecting transported)) k =
      lerayProjectMode k
        (fun output ↦ (h3DivergenceConvolution advecting transported output).1 k) := by
  exact vectorCoefficientAt_lerayProjectPeriodicVectorSobolevTwo _ k

#print axioms norm_lerayProjectMode_coordinate_le
#print axioms norm_lerayProjectMode_coordinate_sq_le
#print axioms lerayProjectedPeriodicVectorFourierComponent_hasSobolevTwo
#print axioms lerayProjectPeriodicVectorSobolevTwo_divergenceFree
#print axioms lerayProjectedH3DivergenceConvolution_divergenceFree

end Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
