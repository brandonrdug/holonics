import ElementaryHolonics.RH.LeftMassReceiver

/-!
# The off-line population under the Jensen bound

The unconditional Jensen bound controls the multiplicity-weighted count of zeros of `ξ` in a
centred disc.  Through the reflection splitting it controls the on-line mass, the left mass, and
the number of off-line, off-axis zeros: each of these is at most the Jensen receiver divided by
`log 2` (the left mass by half of it).
-/

noncomputable section

namespace Soma.Holonics.RH.OffLineJensen

open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.ZeroOrbitCount
open Soma.Holonics.RH.ZeroCountParity
open Soma.Holonics.RH.LeftMassReceiver
open Soma.Holonics.RH.RiemannXiZeroCounting
open Complex Metric

/-- The Jensen receiver of the centred disc of radius `R` with constant `C`. -/
def jensenReceiver (C R : ℝ) : ℝ :=
  C * (‖(1 / 2 : ℂ)‖ + 2 * R + 2) * Real.log (‖(1 / 2 : ℂ)‖ + 2 * R + 2) -
    Real.log ‖riemannXi (1 / 2)‖

/-- **The disc mass under the Jensen bound.** -/
theorem logTwo_mul_divisorMass_le {R : ℝ} (hR : 1 ≤ R) (hc : riemannXi (1 / 2) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ Real.log 2 * (divisorMass R : ℝ) ≤ jensenReceiver C R := by
  obtain ⟨C, hC, h⟩ := innerRiemannXiZeroCount_isUnconditionallyBounded (c := (1 / 2 : ℂ)) hR hc
  refine ⟨C, hC, ?_⟩
  rw [innerRiemannXiZeroCount_eq_divisorMass_cast (by linarith)] at h
  exact h

/-- **The on-line mass under the Jensen bound.** -/
theorem logTwo_mul_onLineMass_le {R : ℝ} (hR : 1 ≤ R) (hc : riemannXi (1 / 2) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ Real.log 2 * (onLineMass R : ℝ) ≤ jensenReceiver C R := by
  obtain ⟨C, hC, h⟩ := logTwo_mul_divisorMass_le hR hc
  refine ⟨C, hC, le_trans ?_ h⟩
  have hle : (onLineMass R : ℝ) ≤ (divisorMass R : ℝ) := by
    exact_mod_cast onLineMass_le_divisorMass R
  exact mul_le_mul_of_nonneg_left hle (Real.log_nonneg (by norm_num))

/-- **The left mass under the Jensen bound**: half the receiver, by reflection. -/
theorem two_logTwo_mul_leftMass_le {R : ℝ} (hR : 1 ≤ R) (hc : riemannXi (1 / 2) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ 2 * Real.log 2 * (leftMass R : ℝ) ≤ jensenReceiver C R := by
  obtain ⟨C, hC, h⟩ := logTwo_mul_divisorMass_le hR hc
  refine ⟨C, hC, le_trans ?_ h⟩
  have hsplit : (divisorMass R : ℝ) = 2 * (leftMass R : ℝ) + (onLineMass R : ℝ) := by
    exact_mod_cast divisorMass_eq_two_mul_leftMass_add_onLineMass R
  have hon : (0 : ℝ) ≤ (onLineMass R : ℝ) := by
    have h0 : (0 : ℤ) ≤ onLineMass R := by
      unfold onLineMass
      exact Finset.sum_nonneg (fun u _ => centredDivisor_nonneg R u)
    exact_mod_cast h0
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hsplit]
  nlinarith [mul_nonneg hlog hon]

/-- The off-line mass: the divisor summed over the off-line support. -/
theorem sum_offLine_eq_two_mul_leftMass (R : ℝ) :
    ∑ u ∈ (centredSupport R).filter (fun u => ¬ u.re = 1 / 2), centredDivisor R u =
      2 * leftMass R := by
  classical
  have h := divisorMass_eq_two_mul_leftMass_add_onLineMass R
  unfold divisorMass onLineMass at h
  rw [← Finset.sum_filter_add_sum_filter_not (centredSupport R) (fun u => u.re = 1 / 2)] at h
  linarith

/-- The off-line, off-axis zeros lie in the off-line support (for `0 < R`). -/
theorem offLineZeros_subset {R : ℝ} (hR : 0 < R) :
    offLineZeros R ⊆ (centredSupport R).filter (fun u => ¬ u.re = 1 / 2) := by
  classical
  intro u hu
  rw [mem_offLineZeros, abs_of_pos hR] at hu
  obtain ⟨⟨hmem, hz⟩, hre, _⟩ := hu
  exact Finset.mem_filter.mpr
    ⟨mem_centredSupport.mpr ((centredDivisor_ne_zero_iff R u).mpr ⟨hmem, hz⟩), hre⟩

/-- **The off-line count is at most twice the left mass.** -/
theorem card_offLineZeros_le {R : ℝ} (hR : 0 < R) :
    ((offLineZeros R).card : ℤ) ≤ 2 * leftMass R := by
  classical
  rw [← sum_offLine_eq_two_mul_leftMass]
  calc ((offLineZeros R).card : ℤ) = ∑ u ∈ offLineZeros R, (1 : ℤ) := by simp
    _ ≤ ∑ u ∈ offLineZeros R, centredDivisor R u := by
        apply Finset.sum_le_sum
        intro u hu
        have hne : centredDivisor R u ≠ 0 := by
          have := (Finset.mem_filter.mp (offLineZeros_subset hR hu)).1
          exact mem_centredSupport.mp this
        have hnn := centredDivisor_nonneg R u
        omega
    _ ≤ ∑ u ∈ (centredSupport R).filter (fun u => ¬ u.re = 1 / 2), centredDivisor R u :=
        Finset.sum_le_sum_of_subset_of_nonneg (offLineZeros_subset hR)
          (fun u _ _ => centredDivisor_nonneg R u)

/-- **The off-line count under the Jensen bound.** -/
theorem logTwo_mul_card_offLineZeros_le {R : ℝ} (hR : 1 ≤ R) (hc : riemannXi (1 / 2) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ Real.log 2 * ((offLineZeros R).card : ℝ) ≤ jensenReceiver C R := by
  obtain ⟨C, hC, h⟩ := two_logTwo_mul_leftMass_le hR hc
  refine ⟨C, hC, le_trans ?_ h⟩
  have hcard : ((offLineZeros R).card : ℝ) ≤ 2 * (leftMass R : ℝ) := by
    exact_mod_cast card_offLineZeros_le (by linarith : 0 < R)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hcard hlog]

end Soma.Holonics.RH.OffLineJensen
