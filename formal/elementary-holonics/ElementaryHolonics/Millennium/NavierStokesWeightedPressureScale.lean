import ElementaryHolonics.Millennium.NavierStokesWeightedPressureReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothPathTower

/-!
# Scale-indexed native pressure reconstruction

**[proved-derived]** The zero-gauge pressure multiplier is invariant under translation of the
native Sobolev scale.  Indeed, the adjacent weight ratio is always
`sqrt (1 + torusStokesEigenvalue k)`.  Consequently the already bounded native pressure passage
acts, without changing its operator constant, from vector `H^(m+2)` to scalar `H^(m+3)` for every
natural `m`.

This owner returns the exact unweighted pressure coefficient, Fourier-reality preservation,
high-to-low compatibility, and the corresponding unprojected quadratic and pressure paths of a
coherent smooth velocity tower.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedPressureScale

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The scale-invariant adjacent multiplier -/

/-- The square-root ratio of two adjacent native Sobolev weights is independent of the order. -/
theorem sqrt_periodicSobolevWeight_succ_mul_inv
    (order : ℕ) (k : SpatialFrequency) :
    Real.sqrt (periodicSobolevWeight (order + 1) k) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ =
      Real.sqrt (1 + torusStokesEigenvalue k) := by
  have ha : 0 ≤ 1 + torusStokesEigenvalue k := by
    linarith [torusStokesEigenvalue_nonneg k]
  have haPos : 0 < 1 + torusStokesEigenvalue k := by
    linarith [torusStokesEigenvalue_nonneg k]
  rw [periodicSobolevWeight, periodicSobolevWeight, pow_succ,
    Real.sqrt_mul (pow_nonneg ha order)]
  have hsqrtPos : 0 < Real.sqrt ((1 + torusStokesEigenvalue k) ^ order) :=
    Real.sqrt_pos.2 (pow_pos haPos order)
  field_simp

/-- The adjacent weight ratio is literally the same at every two translated orders. -/
theorem sqrt_periodicSobolevWeight_adjacent_ratio_eq
    (left right : ℕ) (k : SpatialFrequency) :
    Real.sqrt (periodicSobolevWeight (left + 1) k) *
        (Real.sqrt (periodicSobolevWeight left k))⁻¹ =
      Real.sqrt (periodicSobolevWeight (right + 1) k) *
        (Real.sqrt (periodicSobolevWeight right k))⁻¹ := by
  rw [sqrt_periodicSobolevWeight_succ_mul_inv,
    sqrt_periodicSobolevWeight_succ_mul_inv]

/-- The pressure multiplier written at the translated adjacent scale. -/
def nativePressureMultiplierAtOrder
    (m : ℕ) (component : Fin 3) (k : SpatialFrequency) : ℂ :=
  if k = 0 then 0
  else
    (Real.sqrt (periodicSobolevWeight (m + 3) k) : ℂ) *
      (Complex.I * (k component : ℂ) *
        ((((Real.sqrt (periodicSobolevWeight (m + 2) k))⁻¹ : ℝ) : ℂ)) /
        ((2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ)))

/-- Translation along the native scale changes neither the weighted pressure multiplier nor its
operator bound. -/
theorem nativePressureMultiplierAtOrder_eq_nativePressureMultiplier
    (m : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    nativePressureMultiplierAtOrder m component k =
      nativePressureMultiplier component k := by
  by_cases hk : k = 0
  · subst k
    simp [nativePressureMultiplierAtOrder, nativePressureMultiplier]
  · rw [nativePressureMultiplierAtOrder, nativePressureMultiplier,
      if_neg hk, if_neg hk]
    have hratio := sqrt_periodicSobolevWeight_adjacent_ratio_eq
      (m + 2) 2 k
    have hratioComplex := congrArg (fun x : ℝ ↦ (x : ℂ)) hratio
    norm_num only [Nat.reduceAdd] at hratioComplex
    let phase : ℂ := Complex.I * (k component : ℂ)
    let highRoot : ℂ := Real.sqrt (periodicSobolevWeight (m + 3) k)
    let highInv : ℂ :=
      (((Real.sqrt (periodicSobolevWeight (m + 2) k))⁻¹ : ℝ) : ℂ)
    let baseRoot : ℂ := Real.sqrt (periodicSobolevWeight 3 k)
    let baseInv : ℂ :=
      (((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ)
    have hnumerator :
        highRoot * (phase * highInv) = baseRoot * (phase * baseInv) := by
      calc
        highRoot * (phase * highInv) =
            (((Real.sqrt (periodicSobolevWeight (m + 3) k) *
                (Real.sqrt (periodicSobolevWeight (m + 2) k))⁻¹ : ℝ) : ℂ) *
              phase) := by
                dsimp [highRoot, highInv]
                push_cast
                ring
        _ = (((Real.sqrt (periodicSobolevWeight 3 k) *
                (Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ) *
              phase) := by rw [hratioComplex]
        _ = baseRoot * (phase * baseInv) := by
              dsimp [baseRoot, baseInv]
              push_cast
              ring
    let denom : ℂ := (2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ)
    have hdiv := congrArg (fun numerator : ℂ ↦ numerator / denom) hnumerator
    change highRoot * ((phase * highInv) / denom) =
      baseRoot * ((phase * baseInv) / denom)
    calc
      highRoot * ((phase * highInv) / denom) =
          (highRoot * (phase * highInv)) / denom := by ring
      _ = (baseRoot * (phase * baseInv)) / denom := hdiv
      _ = baseRoot * ((phase * baseInv) / denom) := by ring

/-! ## The bounded passage at every order -/

/-- The complete zero-gauge pressure passage from vector `H^(m+2)` to scalar `H^(m+3)`. -/
def nativePressureAtOrder (m : ℕ) :
    PeriodicVectorWeightedSobolev (m + 2) →L[ℂ]
      PeriodicWeightedSobolev (m + 3) :=
  nativePressureFromH2

@[simp]
theorem nativePressureAtOrder_apply
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 2))
    (k : SpatialFrequency) :
    nativePressureAtOrder m state k =
      ∑ component : Fin 3,
        nativePressureMultiplierAtOrder m component k * state component k := by
  change nativePressureFromH2 state k = _
  rw [nativePressureFromH2_apply]
  apply Finset.sum_congr rfl
  intro component _
  rw [nativePressureMultiplierAtOrder_eq_nativePressureMultiplier]

/-- The finite-component operator constant six is uniform over the complete Sobolev scale. -/
theorem norm_nativePressureAtOrder_le
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 2)) :
    ‖nativePressureAtOrder m state‖ ≤ 6 * ‖state‖ :=
  norm_nativePressureFromH2_le state

/-- The unweighted vector mode presented at scale order `m+2`. -/
def physicalModeAtOrder
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 2))
    (k : SpatialFrequency) : ComplexVector :=
  fun component ↦
    (weightedSobolevCoefficients (m + 2) (state component)).1 k

private theorem unweight_nativePressureMultiplierAtOrder_of_ne_zero
    (m : ℕ) (component : Fin 3) {k : SpatialFrequency} (hk : k ≠ 0) :
    (((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
        nativePressureMultiplierAtOrder m component k =
      Complex.I * (k component : ℂ) *
          ((((Real.sqrt (periodicSobolevWeight (m + 2) k))⁻¹ : ℝ) : ℂ)) /
        ((2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ)) := by
  rw [nativePressureMultiplierAtOrder, if_neg hk, ← mul_assoc]
  have hsqrt : Real.sqrt (periodicSobolevWeight (m + 3) k) ≠ 0 :=
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos (m + 3) k)).ne'
  have hcancel :
      (((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
          (Real.sqrt (periodicSobolevWeight (m + 3) k) : ℂ) = 1 := by
    norm_cast
    field_simp
  rw [hcancel, one_mul]

/-- Unweighting the scale-indexed bounded passage returns exactly the physical zero-gauge
pressure coefficient. -/
theorem weightedSobolevCoefficients_nativePressureAtOrder
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 2))
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (nativePressureAtOrder m state)).1 k =
      pressureCoefficientOfMode k (physicalModeAtOrder m state k) := by
  by_cases hk : k = 0
  · subst k
    simp [weightedSobolevCoefficients, weightedSobolevRawCoefficients,
      nativePressureAtOrder_apply, nativePressureMultiplierAtOrder,
      pressureCoefficientOfMode]
  · change
      (((Real.sqrt (periodicSobolevWeight (m + 3) k))⁻¹ : ℝ) : ℂ) *
          nativePressureAtOrder m state k =
        pressureCoefficientOfMode k (physicalModeAtOrder m state k)
    rw [nativePressureAtOrder_apply, Finset.mul_sum,
      pressureCoefficientOfMode, if_neg hk]
    simp only [physicalModeAtOrder, weightedSobolevCoefficients,
      weightedSobolevRawCoefficients, complexDot, dotProduct,
      complexFrequencyVector]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro component _
    rw [← mul_assoc,
      unweight_nativePressureMultiplierAtOrder_of_ne_zero m component hk]
    ring

/-- The scale-indexed pressure passage preserves the exact Fourier-reality incidence. -/
theorem isScalarWeightedFourierReal_nativePressureAtOrder
    (m : ℕ) {state : PeriodicVectorWeightedSobolev (m + 2)}
    (hstate : IsWeightedFourierReal (m + 2) state) :
    IsScalarWeightedFourierReal (m + 3) (nativePressureAtOrder m state) := by
  intro k
  rw [weightedSobolevCoefficients_nativePressureAtOrder,
    weightedSobolevCoefficients_nativePressureAtOrder]
  have hmode : physicalModeAtOrder m state (-k) =
      fun component ↦ conj (physicalModeAtOrder m state k component) := by
    funext component
    exact hstate component k
  rw [hmode]
  exact pressureCoefficientOfMode_neg_conj k _

/-! ## Exact compatibility under order restriction -/

private theorem periodicWeightedSobolev_eq_of_coefficients_eq
    {order : ℕ} {left right : PeriodicWeightedSobolev order}
    (hcoeff : ∀ k,
      (weightedSobolevCoefficients order left).1 k =
        (weightedSobolevCoefficients order right).1 k) :
    left = right := by
  calc
    left = coefficientWeightedRealization order
        (weightedSobolevCoefficients order left) :=
      (coefficientWeightedRealization_weightedSobolevCoefficients order left).symm
    _ = coefficientWeightedRealization order
        (weightedSobolevCoefficients order right) := by
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact hcoeff k
    _ = right :=
      coefficientWeightedRealization_weightedSobolevCoefficients order right

/-- Pressure formation commutes with every exact high-to-low restriction of its source.  Thus a
coherent source tower returns one coherent scalar pressure tower, not unrelated pressure faces. -/
theorem restrict_nativePressureAtOrder
    (low high : ℕ) (hlowhigh : low ≤ high)
    (state : PeriodicVectorWeightedSobolev (high + 2)) :
    periodicWeightedSobolevRestrictCLM
        (low + 3) (high + 3) (by omega)
        (nativePressureAtOrder high state) =
      nativePressureAtOrder low
        (periodicVectorWeightedSobolevRestrictCLM
          (low + 2) (high + 2) (by omega) state) := by
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (low + 3)
      (periodicWeightedSobolevRestrict
        (low + 3) (high + 3) (by omega)
        (nativePressureAtOrder high state))).1 k =
      (weightedSobolevCoefficients (low + 3)
        (nativePressureAtOrder low
          (fun component ↦ periodicWeightedSobolevRestrict
            (low + 2) (high + 2) (by omega) (state component)))).1 k
  rw [weightedSobolevCoefficients_restrict_apply,
    weightedSobolevCoefficients_nativePressureAtOrder,
    weightedSobolevCoefficients_nativePressureAtOrder]
  congr 1
  funext component
  exact (weightedSobolevCoefficients_restrict_apply
    (low + 2) (high + 2) (by omega) (state component) k).symm

/-- At order zero the scale-indexed passage is literally the established `H² → H³` owner. -/
@[simp]
theorem nativePressureAtOrder_zero :
    nativePressureAtOrder 0 = nativePressureFromH2 :=
  rfl

section Audit

#print axioms sqrt_periodicSobolevWeight_succ_mul_inv
#print axioms nativePressureMultiplierAtOrder_eq_nativePressureMultiplier
#print axioms nativePressureAtOrder
#print axioms norm_nativePressureAtOrder_le
#print axioms weightedSobolevCoefficients_nativePressureAtOrder
#print axioms isScalarWeightedFourierReal_nativePressureAtOrder
#print axioms restrict_nativePressureAtOrder

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPressureScale
