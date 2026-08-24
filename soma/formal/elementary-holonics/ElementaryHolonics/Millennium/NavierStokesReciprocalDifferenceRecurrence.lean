import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

/-!
# Reciprocal finite-difference recurrence through order six

**[proved-derived]** The annular Hodge multiplier is a quadratic numerator times the reciprocal of
the genuine quadratic frequency denominator.  This owner isolates the reusable algebraic return:
through total order six, the forward difference of a product is the shifted binomial Leibniz sum.
If the product is locally one, the highest reciprocal difference is forced by the lower reciprocal
differences and the positive-order denominator differences.  For a quadratic denominator the
order-six return has only its first- and second-difference faces.

The theorem is local to the seven-point addressed window.  It does not assume that the totalized
Hodge reciprocal is globally inverse at the zero frequency.
-/

noncomputable section

open scoped BigOperators fwdDiff

namespace Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

/-! ## Shifted Leibniz calculus on one addressed path -/

/-- The exact shifted binomial product formula for every order needed by the order-six Hodge
stencil.  The right factor is evaluated after the number of steps carried by the left factor. -/
theorem fwdDiff_iter_mul_eq_sum_choose_through_six
    (left right : ℕ → ℂ) (order : ℕ) (horder : order ≤ 6) (start : ℕ) :
    (fwdDiff 1)^[order] (fun index ↦ left index * right index) start =
      ∑ derivative ∈ Finset.range (order + 1),
        (order.choose derivative : ℂ) *
          (fwdDiff 1)^[derivative] left start *
          (fwdDiff 1)^[order - derivative] right (start + derivative) := by
  interval_cases order <;>
    norm_num [Finset.sum_range_succ, Nat.choose, fwdDiff, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] <;> ring

/-- If two path sections multiply to one on the complete addressed window, every positive
difference of their product vanishes on that window. -/
theorem fwdDiff_iter_mul_eq_zero_of_local_inverse_through_six
    (left right : ℕ → ℂ) (order : ℕ)
    (hpositive : 1 ≤ order) (horder : order ≤ 6) (start : ℕ)
    (hinverse : ∀ offset ≤ order,
      left (start + offset) * right (start + offset) = 1) :
    (fwdDiff 1)^[order] (fun index ↦ left index * right index) start = 0 := by
  have hbase : left start * right start = 1 := by
    simpa using hinverse 0 (Nat.zero_le order)
  interval_cases order <;>
    simp_all [fwdDiff, Nat.add_comm, Nat.add_left_comm]

/-- The local reciprocal recurrence.  It solves the order-`n` reciprocal difference from the
positive-order differences of the denominator, retaining their shifted chronology. -/
theorem reciprocalDifference_recurrence_through_six
    (denominator reciprocal : ℕ → ℂ) (order : ℕ)
    (hpositive : 1 ≤ order) (horder : order ≤ 6) (start : ℕ)
    (hinverse : ∀ offset ≤ order,
      denominator (start + offset) * reciprocal (start + offset) = 1) :
    denominator start * (fwdDiff 1)^[order] reciprocal start =
      -∑ derivative ∈ Finset.range order,
        (order.choose (derivative + 1) : ℂ) *
          (fwdDiff 1)^[derivative + 1] denominator start *
          (fwdDiff 1)^[order - (derivative + 1)] reciprocal
            (start + (derivative + 1)) := by
  have hproduct := fwdDiff_iter_mul_eq_sum_choose_through_six
    denominator reciprocal order horder start
  have hzero := fwdDiff_iter_mul_eq_zero_of_local_inverse_through_six
    denominator reciprocal order hpositive horder start hinverse
  rw [hproduct] at hzero
  interval_cases order <;>
    norm_num [Finset.sum_range_succ, Nat.choose] at hzero ⊢ <;>
    linear_combination hzero

/-! ## Quadratic denominators leave only two order-six faces -/

/-- Once a path has zero third difference, all of its fourth through sixth differences vanish as
well. -/
theorem higher_differences_eq_zero_of_third
    (denominator : ℕ → ℂ)
    (hthird : (fwdDiff 1)^[3] denominator = 0) :
    (fwdDiff 1)^[4] denominator = 0 ∧
      (fwdDiff 1)^[5] denominator = 0 ∧
      (fwdDiff 1)^[6] denominator = 0 := by
  have h4 : (fwdDiff 1)^[4] denominator = 0 := by
    rw [show 4 = 1 + 3 by norm_num, Function.iterate_add_apply, hthird]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  have h5 : (fwdDiff 1)^[5] denominator = 0 := by
    rw [show 5 = 1 + 4 by norm_num, Function.iterate_add_apply, h4]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  have h6 : (fwdDiff 1)^[6] denominator = 0 := by
    rw [show 6 = 1 + 5 by norm_num, Function.iterate_add_apply, h5]
    exact fwdDiff_const (1 : ℕ) (0 : ℂ)
  exact ⟨h4, h5, h6⟩

/-- For a locally invertible quadratic denominator, the sixth reciprocal difference is forced by
exactly two surviving faces: first denominator difference against fifth reciprocal difference, and
second denominator difference against fourth reciprocal difference. -/
theorem quadraticReciprocal_sixthDifference_recurrence
    (denominator reciprocal : ℕ → ℂ) (start : ℕ)
    (hinverse : ∀ offset ≤ 6,
      denominator (start + offset) * reciprocal (start + offset) = 1)
    (hthird : (fwdDiff 1)^[3] denominator = 0) :
    denominator start * (fwdDiff 1)^[6] reciprocal start =
      -(6 * fwdDiff 1 denominator start *
          (fwdDiff 1)^[5] reciprocal (start + 1) +
        15 * (fwdDiff 1)^[2] denominator start *
          (fwdDiff 1)^[4] reciprocal (start + 2)) := by
  have hrecurrence := reciprocalDifference_recurrence_through_six
    denominator reciprocal 6 (by norm_num) (by norm_num) start hinverse
  obtain ⟨h4, h5, h6⟩ := higher_differences_eq_zero_of_third denominator hthird
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, Function.iterate_zero_apply,
    Function.iterate_one, add_zero, zero_add] at hrecurrence
  rw [hthird, h4, h5, h6] at hrecurrence
  simpa only [Pi.zero_apply, mul_zero, zero_mul, add_zero] using hrecurrence

/-! ## The actual annular Hodge denominator on one coordinate path -/

/-- The genuine quadratic frequency denominator along an addressed coordinate ray. -/
def hodgeDenominatorPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ) : ℂ :=
  (frequencySquared (frequency + offset • coordinateStep axis) : ℝ)

/-- The actual totalized Hodge reciprocal along the same addressed ray. -/
def hodgeReciprocalPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ) : ℂ :=
  hodgeReciprocal (frequency + offset • coordinateStep axis)

/-- The coordinate restriction of the genuine frequency denominator is exactly quadratic. -/
theorem hodgeDenominatorPath_thirdDifference_eq_zero
    (axis : Fin 3) (frequency : SpatialFrequency) :
    (fwdDiff 1)^[3] (hodgeDenominatorPath axis frequency) = 0 := by
  funext offset
  fin_cases axis <;>
    simp [hodgeDenominatorPath, fwdDiff, coordinateStep, frequencySquared,
      Fin.sum_univ_succ] <;> ring

/-- Away from the zero frequency, the genuine denominator and the totalized Hodge reciprocal are
actual inverses at the addressed path occurrence. -/
theorem hodgeDenominatorPath_mul_hodgeReciprocalPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ)
    (hnonzero : frequencySquared (frequency + offset • coordinateStep axis) ≠ 0) :
    hodgeDenominatorPath axis frequency offset *
        hodgeReciprocalPath axis frequency offset = 1 := by
  have hcomplex :
      ((frequencySquared (frequency + offset • coordinateStep axis) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnonzero
  unfold hodgeDenominatorPath hodgeReciprocalPath hodgeReciprocal
  rw [one_div]
  exact mul_inv_cancel₀ hcomplex

/-- The order-six reciprocal recurrence now applies to the actual Hodge denominator on every
seven-point annular coordinate window that stays away from zero. -/
theorem hodgeReciprocalPath_sixthDifference_recurrence
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ offset ≤ 6,
      frequencySquared (frequency + offset • coordinateStep axis) ≠ 0) :
    hodgeDenominatorPath axis frequency 0 *
        (fwdDiff 1)^[6] (hodgeReciprocalPath axis frequency) 0 =
      -(6 * fwdDiff 1 (hodgeDenominatorPath axis frequency) 0 *
          (fwdDiff 1)^[5] (hodgeReciprocalPath axis frequency) 1 +
        15 * (fwdDiff 1)^[2] (hodgeDenominatorPath axis frequency) 0 *
          (fwdDiff 1)^[4] (hodgeReciprocalPath axis frequency) 2) := by
  apply quadraticReciprocal_sixthDifference_recurrence
  · intro offset hoff
    simpa using hodgeDenominatorPath_mul_hodgeReciprocalPath
      axis frequency offset (hnonzero offset hoff)
  · exact hodgeDenominatorPath_thirdDifference_eq_zero axis frequency

/-! ## The three-axis order-six stencil has a sparse quadratic denominator face -/

/-- Iterated forward differences in all three genuine lattice coordinates. -/
def threeAxisMixedForwardDifference
    (first second third : Fin 3)
    (firstOrder secondOrder thirdOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) : SpatialFrequency → ℂ :=
  (fwdDiff (coordinateStep first))^[firstOrder]
    ((fwdDiff (coordinateStep second))^[secondOrder]
      ((fwdDiff (coordinateStep third))^[thirdOrder] coefficient))

/-- The seven possible nonzero denominator faces: its value, one first difference in any of three
coordinates, or one same-coordinate second difference. -/
inductive QuadraticDenominatorFace
  | value
  | first (axis : Fin 3)
  | second (axis : Fin 3)
  deriving DecidableEq, Fintype

/-- The separable quadratic denominator has exactly seven candidate faces before any product
estimate is taken. -/
theorem quadraticDenominatorFace_card : Fintype.card QuadraticDenominatorFace = 7 := by
  native_decide

/-- Cross-coordinate first differences of the genuine frequency denominator vanish exactly. -/
theorem frequencySquared_crossDifference_eq_zero
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) :
    fwdDiff (coordinateStep first)
      (fwdDiff (coordinateStep second)
        (fun current ↦ (frequencySquared current : ℂ))) frequency = 0 := by
  fin_cases first <;> fin_cases second <;>
    simp_all [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- Every same-coordinate second difference of the genuine frequency denominator is exactly two. -/
theorem frequencySquared_sameAxis_secondDifference_eq_two
    (axis : Fin 3) (frequency : SpatialFrequency) :
    (fwdDiff (coordinateStep axis))^[2]
      (fun current ↦ (frequencySquared current : ℂ)) frequency = 2 := by
  fin_cases axis <;>
    simp [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ] <;>
    ring

/-- Every same-coordinate third denominator difference vanishes. -/
theorem frequencySquared_sameAxis_thirdDifference_eq_zero
    (axis : Fin 3) :
    (fwdDiff (coordinateStep axis))^[3]
      (fun current ↦ (frequencySquared current : ℂ)) = 0 := by
  funext frequency
  fin_cases axis <;>
    simp [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ] <;>
    ring

end Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.fwdDiff_iter_mul_eq_sum_choose_through_six
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.reciprocalDifference_recurrence_through_six
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.quadraticReciprocal_sixthDifference_recurrence
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.hodgeReciprocalPath_sixthDifference_recurrence
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.frequencySquared_crossDifference_eq_zero
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.frequencySquared_sameAxis_thirdDifference_eq_zero
