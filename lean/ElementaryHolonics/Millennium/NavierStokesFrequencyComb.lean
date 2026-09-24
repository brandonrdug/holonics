import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The balanced frequency comb behind the logarithmic vorticity estimate

A periodic BKM estimate splits the velocity-Jacobian receiver into low, middle, and high frequency
populations.  The middle population pays once per dyadic shell, while the high tail decays
geometrically against a high-order receiver.  Choosing the shell depth as the ceiling of the
base-two logarithm balances these two faces and is the exact source of the logarithmic loss.

This module proves that scalar balancing passage.  It does not assert that a Navier--Stokes field
supplies the three shell estimates; the Fourier/Hodge and Sobolev owners must establish those
analytic inputs separately.
-/

noncomputable section

open Real

namespace Soma.Holonics.Millennium.NavierStokesFrequencyComb

/-- The first natural shell depth whose real value is at least `log_2 H`. -/
def shellDepth (H : ℝ) : ℕ := Nat.ceil (Real.logb 2 H)

/-- The chosen depth lies above the base-two logarithm. -/
theorem logb_le_shellDepth (H : ℝ) :
    Real.logb 2 H ≤ (shellDepth H : ℝ) := by
  exact Nat.le_ceil _

/-- For a receiver of size at least one, the chosen depth overshoots by less than one shell. -/
theorem shellDepth_lt_logb_add_one {H : ℝ} (hH : 1 ≤ H) :
    (shellDepth H : ℝ) < Real.logb 2 H + 1 := by
  apply Nat.ceil_lt_add_one
  exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hH

/-- The chosen dyadic scale dominates the high-order receiver. -/
theorem le_two_rpow_shellDepth {H : ℝ} (hH : 1 ≤ H) :
    H ≤ (2 : ℝ) ^ (shellDepth H : ℝ) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hHpos).mp
    (logb_le_shellDepth H)

/-- Consequently the balanced high-frequency tail costs at most one. -/
theorem div_two_rpow_shellDepth_le_one {H : ℝ} (hH : 1 ≤ H) :
    H / (2 : ℝ) ^ (shellDepth H : ℝ) ≤ 1 := by
  exact (div_le_one (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).2
    (le_two_rpow_shellDepth hH)

/-- Receiver-local low/middle/high testimony at one dyadic shell depth. -/
structure ThreeBandCombBound
    (total low middle high lowBound critical highOrder : ℝ) (shells : ℕ) : Prop where
  total_le : total ≤ low + middle + high
  low_le : low ≤ lowBound
  middle_le : middle ≤ (shells : ℝ) * critical
  high_le : high ≤ highOrder / (2 : ℝ) ^ (shells : ℝ)
  critical_nonneg : 0 ≤ critical

/-- **Balanced comb inequality.**  Low frequencies pay their independent bound, middle
frequencies pay the critical receiver once per occupied shell, and the high tail pays one after
choosing `ceil(log_2 H)` shells.  The complete receiver is therefore logarithmic in the high-order
size. -/
theorem ThreeBandCombBound.logarithmic_bound
    {total low middle high lowBound critical highOrder : ℝ}
    (hH : 1 ≤ highOrder)
    (bounds : ThreeBandCombBound total low middle high lowBound critical highOrder
      (shellDepth highOrder)) :
    total ≤ lowBound + (Real.logb 2 highOrder + 1) * critical + 1 := by
  have hshell : (shellDepth highOrder : ℝ) ≤ Real.logb 2 highOrder + 1 :=
    (shellDepth_lt_logb_add_one hH).le
  have hmiddle : middle ≤ (Real.logb 2 highOrder + 1) * critical :=
    bounds.middle_le.trans
      (mul_le_mul_of_nonneg_right hshell bounds.critical_nonneg)
  have hhigh : high ≤ 1 := bounds.high_le.trans
    (div_two_rpow_shellDepth_le_one hH)
  linarith [bounds.total_le, bounds.low_le]

/-- The same balance with a unit low-frequency face has the familiar
`constant + critical * logarithm` shape. -/
theorem ThreeBandCombBound.logarithmic_bound_of_low_le_one
    {total low middle high critical highOrder : ℝ}
    (hH : 1 ≤ highOrder)
    (bounds : ThreeBandCombBound total low middle high 1 critical highOrder
      (shellDepth highOrder)) :
    total ≤ 2 + (Real.logb 2 highOrder + 1) * critical := by
  have h := bounds.logarithmic_bound hH
  linarith

section Audit

#print axioms logb_le_shellDepth
#print axioms le_two_rpow_shellDepth
#print axioms ThreeBandCombBound.logarithmic_bound
#print axioms ThreeBandCombBound.logarithmic_bound_of_low_le_one

end Audit

end Soma.Holonics.Millennium.NavierStokesFrequencyComb
