import ElementaryHolonics.Millennium.HolonicEntropyActionInduction

/-!
# A temporal heat instance of the oriented entropy current

Two explicit four-axis currents are transported by different heat frequencies.  Their oriented
cross-current is computed before taking the heat defect; no entropy balance or statistical
cross-entropy identification is introduced here.
-/

noncomputable section

open Function Set Topology

namespace Soma.Holonics.Millennium.HolonicEntropyHeatCurrent

open Soma.Holonics
open Soma.Holonics.Millennium.HolonicEntropyActionInduction

/-- The complex receiver of the first two addressed current axes. -/
def complexPlaneFace (current : FourTorusEntropyCurrent ℝ) : ℂ :=
  (current 0 : ℂ) + Complex.I * (current 1 : ℂ)

/-- The existing oriented current is the imaginary face of the conjugate complex pairing. -/
theorem entropyAxisCrossCurrent_eq_complex_pairing
    (left right : FourTorusEntropyCurrent ℝ) :
    entropyAxisCrossCurrent left right 0 1 =
      (star (complexPlaneFace left) * complexPlaneFace right).im := by
  simp [complexPlaneFace, entropyAxisCrossCurrent, Complex.mul_im]
  ring

def entropyHeatJ (nu t x : ℝ) : FourTorusEntropyCurrent ℝ :=
  fun axis ↦ if axis = 0 then Real.exp (-nu * t) * Real.cos x
    else if axis = 1 then Real.exp (-nu * t) * Real.sin x else 0

def entropyHeatK (nu t x : ℝ) : FourTorusEntropyCurrent ℝ :=
  fun axis ↦ if axis = 0 then (1 + Real.exp (-4 * nu * t) * Real.cos (2 * x)) / 2
    else if axis = 1 then Real.exp (-4 * nu * t) * Real.sin (2 * x) / 2 else 0

theorem entropyHeatK_initial_aligned (nu x : ℝ) :
    entropyHeatK nu 0 x = fun axis ↦ Real.cos x * entropyHeatJ nu 0 x axis := by
  funext axis
  fin_cases axis
  · simp [entropyHeatJ, entropyHeatK]
    rw [Real.cos_two_mul]
    ring
  · simp [entropyHeatJ, entropyHeatK]
    rw [Real.sin_two_mul]
    ring
  · simp [entropyHeatJ, entropyHeatK]
  · simp [entropyHeatJ, entropyHeatK]

theorem entropyHeatCrossCurrent_eq (nu t x : ℝ) :
    entropyAxisCrossCurrent (entropyHeatJ nu t x) (entropyHeatK nu t x) 0 1 =
      Real.exp (-nu * t) * (Real.exp (-4 * nu * t) - 1) * Real.sin x / 2 := by
  simp [entropyAxisCrossCurrent, entropyHeatJ, entropyHeatK]
  ring_nf
  rw [show x * 2 = 2 * x by ring, Real.sin_two_mul, Real.cos_two_mul]
  ring

theorem entropyHeatCrossCurrent_initial (nu x : ℝ) :
    entropyAxisCrossCurrent (entropyHeatJ nu 0 x) (entropyHeatK nu 0 x) 0 1 = 0 := by
  rw [entropyHeatCrossCurrent_eq]
  simp

theorem entropyHeatCrossCurrent_nonzero {nu t x : ℝ}
    (hnu : 0 < nu) (ht : 0 < t) (hsin : Real.sin x ≠ 0) :
    entropyAxisCrossCurrent (entropyHeatJ nu t x) (entropyHeatK nu t x) 0 1 ≠ 0 := by
  rw [entropyHeatCrossCurrent_eq]
  have hexp1 : Real.exp (-nu * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hexp4 : Real.exp (-4 * nu * t) - 1 ≠ 0 := by
    have hlt : Real.exp (-4 * nu * t) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    exact ne_of_lt (sub_neg.mpr hlt)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hexp1 hexp4) hsin) (inv_ne_zero htwo)

theorem entropyHeatCrossCurrent_euler (x : ℝ) (t : ℝ) :
    entropyAxisCrossCurrent (entropyHeatJ 0 t x) (entropyHeatK 0 t x) 0 1 = 0 := by
  rw [entropyHeatCrossCurrent_eq]
  simp

private theorem deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ ↦ Real.exp (a * y)) x = a * Real.exp (a * x) := by
  convert (((hasDerivAt_id x).const_mul a).exp).deriv using 1 <;> simp [id_eq] <;> ring

private theorem deriv_sin_mul (a x : ℝ) :
    deriv (fun y : ℝ ↦ Real.sin (a * y)) x = a * Real.cos (a * x) := by
  convert (((hasDerivAt_id x).const_mul a).sin).deriv using 1 <;> simp [id_eq] <;> ring

private theorem deriv_cos_mul (a x : ℝ) :
    deriv (fun y : ℝ ↦ Real.cos (a * y)) x = -a * Real.sin (a * x) := by
  convert (((hasDerivAt_id x).const_mul a).cos).deriv using 1 <;> simp [id_eq] <;> ring

/-- Every addressed component of the first current obeys the actual heat equation. -/
theorem entropyHeatJ_heat_equation (nu t x : ℝ) (axis : Fin 4) :
    deriv (fun s ↦ entropyHeatJ nu s x axis) t =
      nu * deriv (fun y ↦ deriv (fun z ↦ entropyHeatJ nu t z axis) y) x := by
  fin_cases axis <;>
    simp (disch := fun_prop) [entropyHeatJ, deriv_exp, deriv_mul_const_field, deriv_const_mul_field,
      Real.deriv_cos, Real.deriv_sin, deriv_exp_mul, deriv_neg] <;> ring

/-- The second current includes the zero mode and second harmonic of the same heat source. -/
theorem entropyHeatK_heat_equation (nu t x : ℝ) (axis : Fin 4) :
    deriv (fun s ↦ entropyHeatK nu s x axis) t =
      nu * deriv (fun y ↦ deriv (fun z ↦ entropyHeatK nu t z axis) y) x := by
  fin_cases axis <;>
    simp (disch := fun_prop) [entropyHeatK, deriv_exp, deriv_mul_const_field, deriv_const_mul_field, deriv_div_const,
      deriv_const_add, deriv_exp_mul, deriv_sin_mul, deriv_cos_mul, deriv_neg] <;> ring

/-- The oriented cross-current has its own nonzero heat source. -/
theorem entropyHeatCrossCurrent_heat_defect (nu t x : ℝ) :
    deriv (fun s ↦ entropyAxisCrossCurrent (entropyHeatJ nu s x)
        (entropyHeatK nu s x) 0 1) t -
      nu * deriv (fun y ↦ deriv (fun z ↦ entropyAxisCrossCurrent
        (entropyHeatJ nu t z) (entropyHeatK nu t z) 0 1) y) x =
      -2 * nu * Real.exp (-5 * nu * t) * Real.sin x := by
  simp_rw [entropyHeatCrossCurrent_eq]
  simp (disch := fun_prop) only [deriv_div_const, deriv_mul_const_field,
    deriv_const_mul_field, deriv_fun_mul, deriv_sub_const, deriv_exp_mul,
    Real.deriv_sin, Real.deriv_cos]
  rw [show -5 * nu * t = -nu * t + -4 * nu * t by ring, Real.exp_add]
  ring

/-- The mixed spatial derivatives supply exactly the retained source term. -/
theorem entropyHeatCrossCurrent_spatial_source (nu t x : ℝ) :
    entropyAxisCrossCurrent (fun axis ↦ deriv (fun z ↦ entropyHeatJ nu t z axis) x)
      (fun axis ↦ deriv (fun z ↦ entropyHeatK nu t z axis) x) 0 1 =
      Real.exp (-5 * nu * t) * Real.sin x := by
  change deriv (fun z ↦ Real.exp (-nu * t) * Real.cos z) x *
      deriv (fun z ↦ Real.exp (-4 * nu * t) * Real.sin (2 * z) / 2) x -
    deriv (fun z ↦ Real.exp (-nu * t) * Real.sin z) x *
      deriv (fun z ↦ (1 + Real.exp (-4 * nu * t) * Real.cos (2 * z)) / 2) x = _
  simp only [deriv_div_const, deriv_const_mul_field, deriv_const_add,
    Real.deriv_cos, Real.deriv_sin, deriv_sin_mul, deriv_cos_mul]
  rw [Real.sin_two_mul, Real.cos_two_mul,
    show -5 * nu * t = -nu * t + -4 * nu * t by ring, Real.exp_add]
  ring

/-- Source composition: heat of the relation includes the mixed derivative current. -/
theorem entropyHeatCrossCurrent_sourced_heat_equation (nu t x : ℝ) :
    deriv (fun s ↦ entropyAxisCrossCurrent (entropyHeatJ nu s x)
        (entropyHeatK nu s x) 0 1) t -
      nu * deriv (fun y ↦ deriv (fun z ↦ entropyAxisCrossCurrent
        (entropyHeatJ nu t z) (entropyHeatK nu t z) 0 1) y) x =
      -2 * nu * entropyAxisCrossCurrent
        (fun axis ↦ deriv (fun z ↦ entropyHeatJ nu t z axis) x)
        (fun axis ↦ deriv (fun z ↦ entropyHeatK nu t z axis) x) 0 1 := by
  rw [entropyHeatCrossCurrent_heat_defect, entropyHeatCrossCurrent_spatial_source]
  ring

#print axioms entropyAxisCrossCurrent_eq_complex_pairing
#print axioms entropyHeatK_initial_aligned
#print axioms entropyHeatCrossCurrent_eq
#print axioms entropyHeatCrossCurrent_initial
#print axioms entropyHeatCrossCurrent_nonzero
#print axioms entropyHeatCrossCurrent_euler

#print axioms entropyHeatJ_heat_equation
#print axioms entropyHeatK_heat_equation
#print axioms entropyHeatCrossCurrent_sourced_heat_equation

end Soma.Holonics.Millennium.HolonicEntropyHeatCurrent
