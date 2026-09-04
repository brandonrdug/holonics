import ElementaryHolonics.Millennium.NavierStokesDuhamelRestartTime
import ElementaryHolonics.Millennium.NavierStokesQuadraticContraction
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear

/-!
# The explicit native H³ restart aperture

**[proved-derived]** This owner binds the generic scalar time aperture to the actual constant of
the native periodic `H³ × H³ → H²` Leray passage.  For initial datum `u₀`, it declares

* the path-ball radius `R = 2 (1 + ‖u₀‖)`;
* the quadratic load `(23328 C_embed) R`; and
* the positive viscous time returned by `duhamelRestartTime` at that load.

At this exact time, the integrated Duhamel coefficient satisfies both inequalities required by
the Banach return: it maps the radius ball to itself and has strict contraction factor below one.
The final constructors accept only the actual path-map remainder estimates still owed by the
continuous Bochner owner; none of the scalar smallness conditions remain as premises.
-/

noncomputable section

open Function

namespace Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture

open Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesQuadraticContraction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The coefficient of the genuine native Leray bilinear passage. -/
def weightedLerayCoefficient : ℝ :=
  23328 * periodicH3EmbeddingConstant

theorem weightedLerayCoefficient_nonneg :
    0 ≤ weightedLerayCoefficient := by
  exact mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg

/-- A strictly positive path radius which also covers zero initial data without a separate case. -/
def weightedRestartRadius (initial : PeriodicVectorWeightedSobolev 3) : ℝ :=
  2 * (1 + ‖initial‖)

theorem weightedRestartRadius_pos
    (initial : PeriodicVectorWeightedSobolev 3) :
    0 < weightedRestartRadius initial := by
  unfold weightedRestartRadius
  positivity

/-- The exact radius-weighted quadratic load seen by the Duhamel difference map. -/
def weightedRestartLoad (initial : PeriodicVectorWeightedSobolev 3) : ℝ :=
  weightedLerayCoefficient * weightedRestartRadius initial

theorem weightedRestartLoad_nonneg
    (initial : PeriodicVectorWeightedSobolev 3) :
    0 ≤ weightedRestartLoad initial := by
  exact mul_nonneg weightedLerayCoefficient_nonneg
    (weightedRestartRadius_pos initial).le

/-- The common positive local time selected from viscosity and the actual initial-data load. -/
def weightedRestartTime (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev 3) : ℝ :=
  duhamelRestartTime nu (weightedRestartLoad initial)

theorem weightedRestartTime_pos
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev 3) :
    0 < weightedRestartTime nu initial :=
  duhamelRestartTime_pos hnu (weightedRestartLoad_nonneg initial)

/-- The integrated coefficient multiplying the quadratic radius and two-path separation. -/
def weightedDuhamelCoefficient (nu T : ℝ) : ℝ :=
  weightedLerayCoefficient *
    (T + 2 * Real.sqrt (T / (2 * nu)))

theorem weightedDuhamelCoefficient_nonneg
    {nu T : ℝ} (hT : 0 ≤ T) :
    0 ≤ weightedDuhamelCoefficient nu T := by
  unfold weightedDuhamelCoefficient
  exact mul_nonneg weightedLerayCoefficient_nonneg
    (add_nonneg hT (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- At the selected aperture, the actual two-path Duhamel factor is strictly contractive. -/
theorem two_weightedDuhamelCoefficient_mul_radius_lt_one
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev 3) :
    2 * weightedDuhamelCoefficient nu (weightedRestartTime nu initial) *
        weightedRestartRadius initial < 1 := by
  have h := two_load_mul_restartKernelBound_lt_one hnu
    (weightedRestartLoad_nonneg initial)
  unfold weightedDuhamelCoefficient weightedRestartTime
  unfold weightedRestartLoad at h ⊢
  nlinarith

/-- The same strict contraction inequality supplies the quadratic half-ball bound. -/
theorem weightedDuhamelCoefficient_mul_radius_sq_le_half
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev 3) :
    weightedDuhamelCoefficient nu (weightedRestartTime nu initial) *
        weightedRestartRadius initial ^ 2 ≤
      weightedRestartRadius initial / 2 := by
  let A := weightedDuhamelCoefficient nu (weightedRestartTime nu initial)
  let R := weightedRestartRadius initial
  have hR : 0 < R := weightedRestartRadius_pos initial
  have hcontract : 2 * A * R < 1 :=
    two_weightedDuhamelCoefficient_mul_radius_lt_one hnu initial
  have hhalf : 0 < R / 2 := by positivity
  have hscaled := mul_lt_mul_of_pos_right hcontract hhalf
  have hstrict : A * R ^ 2 < R / 2 := by
    nlinarith
  exact hstrict.le

/-! ## A common aperture from a uniform norm cap -/

/-- A path radius determined by a common cap rather than one particular initial occurrence. -/
def weightedRestartRadiusFromCap (cap : ℝ) : ℝ :=
  2 * (1 + cap)

theorem weightedRestartRadiusFromCap_pos
    {cap : ℝ} (hcap : 0 ≤ cap) :
    0 < weightedRestartRadiusFromCap cap := by
  unfold weightedRestartRadiusFromCap
  positivity

/-- The common quadratic load carried by every initial state below the declared cap. -/
def weightedRestartLoadFromCap (cap : ℝ) : ℝ :=
  weightedLerayCoefficient * weightedRestartRadiusFromCap cap

theorem weightedRestartLoadFromCap_nonneg
    {cap : ℝ} (hcap : 0 ≤ cap) :
    0 ≤ weightedRestartLoadFromCap cap :=
  mul_nonneg weightedLerayCoefficient_nonneg
    (weightedRestartRadiusFromCap_pos hcap).le

/-- One common positive time aperture for the complete family below a uniform norm cap. -/
def weightedRestartTimeFromCap (nu cap : ℝ) : ℝ :=
  duhamelRestartTime nu (weightedRestartLoadFromCap cap)

theorem weightedRestartTimeFromCap_pos
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap) :
    0 < weightedRestartTimeFromCap nu cap :=
  duhamelRestartTime_pos hnu (weightedRestartLoadFromCap_nonneg hcap)

/-- The common-cap aperture has the same strict two-path contraction return. -/
theorem two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap) :
    2 * weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) *
        weightedRestartRadiusFromCap cap < 1 := by
  have h := two_load_mul_restartKernelBound_lt_one hnu
    (weightedRestartLoadFromCap_nonneg hcap)
  unfold weightedDuhamelCoefficient weightedRestartTimeFromCap
  unfold weightedRestartLoadFromCap at h ⊢
  nlinarith

/-- Strict contraction also supplies the common-cap quadratic half-ball bound. -/
theorem weightedDuhamelCoefficient_mul_radiusFromCap_sq_le_half
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap) :
    weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) *
        weightedRestartRadiusFromCap cap ^ 2 ≤
      weightedRestartRadiusFromCap cap / 2 := by
  let A := weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap)
  let R := weightedRestartRadiusFromCap cap
  have hR : 0 < R := weightedRestartRadiusFromCap_pos hcap
  have hcontract : 2 * A * R < 1 :=
    two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one hnu hcap
  have hhalf : 0 < R / 2 := by positivity
  have hscaled := mul_lt_mul_of_pos_right hcontract hhalf
  have hstrict : A * R ^ 2 < R / 2 := by
    nlinarith
  exact hstrict.le

/-- Any linear path below the common norm cap occupies at most half the common path ball. -/
theorem linear_le_half_weightedRestartRadiusFromCap
    {X : Type*} [NormedAddCommGroup X]
    {cap : ℝ} (linear : X)
    (hlinear : ‖linear‖ ≤ cap) :
    ‖linear‖ ≤ weightedRestartRadiusFromCap cap / 2 := by
  unfold weightedRestartRadiusFromCap
  linarith

/-- Bind concrete path-map estimates to a uniform cap, eliminating every scalar smallness premise
for all restart faces in the capped family. -/
def quadraticContractionDataOfWeightedRestartCap
    {X : Type*} [NormedAddCommGroup X]
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (Phi : X → X) (linear : X)
    (hlinear : ‖linear‖ ≤ cap)
    (hremainder : ∀ u : X,
      ‖Phi u - linear‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) * ‖u‖ ^ 2)
    (hdifference : ∀ u v : X,
      ‖(Phi u - linear) - (Phi v - linear)‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) *
          (‖u‖ + ‖v‖) * ‖u - v‖) :
    QuadraticContractionData Phi linear
      (weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap))
      (weightedRestartRadiusFromCap cap) where
  coefficient_nonneg := weightedDuhamelCoefficient_nonneg
    (weightedRestartTimeFromCap_pos hnu hcap).le
  radius_nonneg := (weightedRestartRadiusFromCap_pos hcap).le
  linear_le_half :=
    linear_le_half_weightedRestartRadiusFromCap linear hlinear
  quadratic_le_half :=
    weightedDuhamelCoefficient_mul_radiusFromCap_sq_le_half hnu hcap
  contraction_lt_one :=
    two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one hnu hcap
  remainder_bound := hremainder
  remainder_difference_bound := hdifference

/-- The complete-space fixed point at the common aperture. -/
theorem exists_fixedPoint_of_weightedRestartCap_estimates
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (Phi : X → X) (linear : X)
    (hlinear : ‖linear‖ ≤ cap)
    (hremainder : ∀ u : X,
      ‖Phi u - linear‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) * ‖u‖ ^ 2)
    (hdifference : ∀ u v : X,
      ‖(Phi u - linear) - (Phi v - linear)‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap) *
          (‖u‖ + ‖v‖) * ‖u - v‖) :
    ∃ u : X, ‖u‖ ≤ weightedRestartRadiusFromCap cap ∧ IsFixedPt Phi u := by
  exact (quadraticContractionDataOfWeightedRestartCap hnu hcap Phi linear
    hlinear hremainder hdifference).exists_fixedPoint_mem_restartBall

/-- A linear heat path bounded by the initial norm occupies at most half the declared ball. -/
theorem linear_le_half_weightedRestartRadius
    {X : Type*} [NormedAddCommGroup X]
    (initial : PeriodicVectorWeightedSobolev 3) (linear : X)
    (hlinear : ‖linear‖ ≤ ‖initial‖) :
    ‖linear‖ ≤ weightedRestartRadius initial / 2 := by
  unfold weightedRestartRadius
  nlinarith [norm_nonneg initial]

/-- Bind exact path-map remainder estimates to all scalar fields of the generic quadratic
contraction record. -/
def quadraticContractionDataOfWeightedRestart
    {X : Type*} [NormedAddCommGroup X]
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev 3)
    (Phi : X → X) (linear : X)
    (hlinear : ‖linear‖ ≤ ‖initial‖)
    (hremainder : ∀ u : X,
      ‖Phi u - linear‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTime nu initial) * ‖u‖ ^ 2)
    (hdifference : ∀ u v : X,
      ‖(Phi u - linear) - (Phi v - linear)‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTime nu initial) *
          (‖u‖ + ‖v‖) * ‖u - v‖) :
    QuadraticContractionData Phi linear
      (weightedDuhamelCoefficient nu (weightedRestartTime nu initial))
      (weightedRestartRadius initial) where
  coefficient_nonneg := weightedDuhamelCoefficient_nonneg
    (weightedRestartTime_pos hnu initial).le
  radius_nonneg := (weightedRestartRadius_pos initial).le
  linear_le_half := linear_le_half_weightedRestartRadius initial linear hlinear
  quadratic_le_half :=
    weightedDuhamelCoefficient_mul_radius_sq_le_half hnu initial
  contraction_lt_one :=
    two_weightedDuhamelCoefficient_mul_radius_lt_one hnu initial
  remainder_bound := hremainder
  remainder_difference_bound := hdifference

/-- **Actual fixed-point return at the native restart aperture.**  Once the concrete mild map
supplies its already quantified one- and two-path Duhamel estimates, no additional smallness
premise is needed. -/
theorem exists_fixedPoint_of_weightedRestart_estimates
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev 3)
    (Phi : X → X) (linear : X)
    (hlinear : ‖linear‖ ≤ ‖initial‖)
    (hremainder : ∀ u : X,
      ‖Phi u - linear‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTime nu initial) * ‖u‖ ^ 2)
    (hdifference : ∀ u v : X,
      ‖(Phi u - linear) - (Phi v - linear)‖ ≤
        weightedDuhamelCoefficient nu (weightedRestartTime nu initial) *
          (‖u‖ + ‖v‖) * ‖u - v‖) :
    ∃ u : X, ‖u‖ ≤ weightedRestartRadius initial ∧ IsFixedPt Phi u := by
  exact (quadraticContractionDataOfWeightedRestart hnu initial Phi linear
    hlinear hremainder hdifference).exists_fixedPoint_mem_restartBall

section Audit

#print axioms two_weightedDuhamelCoefficient_mul_radius_lt_one
#print axioms weightedDuhamelCoefficient_mul_radius_sq_le_half
#print axioms two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one
#print axioms weightedDuhamelCoefficient_mul_radiusFromCap_sq_le_half
#print axioms quadraticContractionDataOfWeightedRestartCap
#print axioms exists_fixedPoint_of_weightedRestartCap_estimates
#print axioms quadraticContractionDataOfWeightedRestart
#print axioms exists_fixedPoint_of_weightedRestart_estimates

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
