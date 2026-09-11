import Mathlib

/-!
# The sine iteration constraint

For the MathWorld iteration `F x = x + sin x`, this file records the exact
fixed points, local derivatives, branch inequalities, and period transport
which can be read directly from the trigonometric identities.  In particular,
the fixed-point information alone is not a convergence theorem: any claim
about a nearest-multiple iteration must also state its basin and hypotheses.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.PiIterationConstraint

/-- The iteration map studied here. -/
def F (x : ℝ) : ℝ := x + Real.sin x

@[simp] theorem F_zero : F 0 = 0 := by
  simp [F]

@[simp] theorem F_pi : F Real.pi = Real.pi := by
  simp [F]

@[simp] theorem F_two_pi : F (2 * Real.pi) = 2 * Real.pi := by
  simp [F]

theorem F_pi_add (d : ℝ) : F (Real.pi + d) - Real.pi = d - Real.sin d := by
  simp only [F, Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, one_mul,
    neg_one_mul, add_zero]
  ring

theorem F_deriv_at_pi : deriv (fun x : ℝ => x + Real.sin x) Real.pi = 0 := by
  have h := (hasDerivAt_id' Real.pi).add (Real.hasDerivAt_sin Real.pi)
  simpa using h.deriv

theorem F_deriv_at_zero : deriv (fun x : ℝ => x + Real.sin x) 0 = 2 := by
  have h := (hasDerivAt_id' 0).add (Real.hasDerivAt_sin 0)
  convert h.deriv using 1
  · congr 1
  · norm_num [Real.cos_zero]

theorem F_add_two_pi (x : ℝ) : F (x + 2 * Real.pi) = F x + 2 * Real.pi := by
  simp only [F]
  have hs : Real.sin (x + 2 * Real.pi) = Real.sin x := by
    convert Real.sin_add_int_mul_two_pi x 1 using 1 <;> norm_num
  rw [hs]
  ring

theorem F_maps_Icc_zero_pi {x : ℝ} (hx0 : 0 ≤ x) (hxp : x ≤ Real.pi) :
    F x ∈ Set.Icc 0 Real.pi := by
  simp only [F]
  have hsin_nonneg : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxp
  have hsin_upper : Real.sin x ≤ Real.pi - x := by
    rw [← Real.sin_pi_sub x]
    exact Real.sin_le (sub_nonneg.mpr hxp)
  constructor <;> linarith [hsin_nonneg, hsin_upper]

theorem F_strictly_advances_Ioo_zero_pi {x : ℝ} (hx0 : 0 < x)
    (hxp : x < Real.pi) : x < F x := by
  simp only [F]
  linarith [Real.sin_pos_of_pos_of_lt_pi hx0 hxp]

theorem F_maps_Icc_pi_two_pi {x : ℝ} (hxp : Real.pi ≤ x)
    (hx2 : x ≤ 2 * Real.pi) : F x ∈ Set.Icc Real.pi (2 * Real.pi) := by
  simp only [F]
  have hd0 : 0 ≤ x - Real.pi := sub_nonneg.mpr hxp
  have hdp : x - Real.pi ≤ Real.pi := by linarith
  have hs : Real.sin x = -Real.sin (x - Real.pi) := by
    rw [show x = Real.pi + (x - Real.pi) by ring, Real.sin_add]
    rw [Real.sin_pi, Real.cos_pi]
    ring_nf
  have hsin_nonpos : Real.sin x ≤ 0 := by
    rw [hs]
    exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hd0 hdp)
  have hsin_lower : -(x - Real.pi) ≤ Real.sin x := by
    rw [hs]
    exact neg_le_neg (Real.sin_le hd0)
  constructor <;> linarith [hsin_nonpos, hsin_lower]

theorem F_strictly_retreats_Ioo_pi_two_pi {x : ℝ} (hxp : Real.pi < x)
    (hx2 : x < 2 * Real.pi) : F x < x := by
  have hd0 : 0 < x - Real.pi := sub_pos.mpr hxp
  have hdp : x - Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hs : Real.sin x = -Real.sin (x - Real.pi) := by
    rw [show x = Real.pi + (x - Real.pi) by ring, Real.sin_add]
    rw [Real.sin_pi, Real.cos_pi]
    ring_nf
  simp only [F]
  rw [hs]
  linarith [Real.sin_pos_of_pos_of_lt_pi hd0 hdp]

@[simp] theorem F_int_mul_pi (n : ℤ) : F (n * Real.pi) = n * Real.pi := by
  simp only [F]
  rw [Real.sin_int_mul_pi]
  simp

end Soma.Holonics.Mathematics.PiIterationConstraint
