import Mathlib

/-!
# Connection-covariant passive phase contact

For complex port values `x,y` and a unit connection phase `u`, the transported
difference is `δ = y - u*x`.  The contact mixes the two values in their local
frames.  This is a finite two-port law; `u` is supplied by the declared seam
connection and is not inferred from raster proximity.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicComplexParametron

def seamDifference (u x y : ℂ) : ℂ := y - u * x

def seamMix (u : ℂ) (alpha : ℝ) (x y : ℂ) : ℂ × ℂ :=
  (x + (alpha : ℂ) * starRingEnd ℂ u * seamDifference u x y,
    y - (alpha : ℂ) * seamDifference u x y)

def seamEnergy (x y : ℂ) : ℝ := Complex.normSq x + Complex.normSq y

/-- Heat returned by one passive contact in the same declared receiver chart. -/
def seamContactHeat (u x y : ℂ) (alpha : ℝ) : ℝ :=
  2 * alpha * (1 - alpha) * Complex.normSq (seamDifference u x y)

private theorem complex_mix_energy (alpha : ℝ) (x z : ℂ) :
    Complex.normSq (x + (alpha : ℂ) * z) +
        Complex.normSq (x + (1 - alpha : ℂ) * z) =
      Complex.normSq x + Complex.normSq (x + z) -
        2 * alpha * (1 - alpha) * Complex.normSq z := by
  norm_num [Complex.normSq_apply]
  ring

theorem seamMix_energy_decrement
    (u x y : ℂ) (alpha : ℝ) (hunit : Complex.normSq u = 1) :
    seamEnergy (seamMix u alpha x y).1 (seamMix u alpha x y).2 =
      seamEnergy x y -
        2 * alpha * (1 - alpha) * Complex.normSq (seamDifference u x y) := by
  let z : ℂ := starRingEnd ℂ u * seamDifference u x y
  have huconj : u * starRingEnd ℂ u = 1 := by
    simp [Complex.mul_conj, hunit]
  have hrepr : y = u * (x + z) := by
    calc
      y = u * x + (y - u * x) := by ring
      _ = u * x + u * (starRingEnd ℂ u * (y - u * x)) := by
        rw [← mul_assoc, huconj, one_mul]
      _ = u * (x + z) := by simp [z, seamDifference]; ring
  have hz : Complex.normSq z = Complex.normSq (seamDifference u x y) := by
    simp [z, Complex.normSq_mul, hunit]
  have hleft : (seamMix u alpha x y).1 = x + (alpha : ℂ) * z := by
    simp [seamMix, z]
    ring
  have hright : (seamMix u alpha x y).2 = u * (x + (1 - alpha : ℂ) * z) := by
    change y - (alpha : ℂ) * seamDifference u x y = _
    rw [hrepr]
    unfold seamDifference
    ring
  rw [hleft, hright]
  simp only [seamEnergy]
  rw [show Complex.normSq y = Complex.normSq (u * (x + z)) by rw [hrepr]]
  simp only [Complex.normSq_mul, hunit, one_mul]
  rw [← hz]
  simpa only [one_mul] using complex_mix_energy alpha x z

theorem seamMix_energy_nonincreasing
    (u x y : ℂ) (alpha : ℝ) (hunit : Complex.normSq u = 1)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1) :
    seamEnergy (seamMix u alpha x y).1 (seamMix u alpha x y).2 ≤
      seamEnergy x y := by
  rw [seamMix_energy_decrement u x y alpha hunit]
  have hcoef : 0 ≤ 2 * alpha * (1 - alpha) := by positivity
  exact sub_le_self _ (mul_nonneg hcoef (Complex.normSq_nonneg _))

/-- The transported pair sum is unchanged by the equal-and-opposite contact. -/
theorem seamMix_transported_sum
    (u x y : ℂ) (alpha : ℝ) :
    (seamMix u alpha x y).1 + starRingEnd ℂ u * (seamMix u alpha x y).2 =
      x + starRingEnd ℂ u * y := by
  simp [seamMix, seamDifference]
  ring

/-- The lost seam energy is exactly returned through the explicit heat port. -/
theorem seamMix_energy_plus_heat
    (u x y : ℂ) (alpha : ℝ) (hunit : Complex.normSq u = 1) :
    seamEnergy (seamMix u alpha x y).1 (seamMix u alpha x y).2 +
        seamContactHeat u x y alpha = seamEnergy x y := by
  rw [seamMix_energy_decrement u x y alpha hunit]
  unfold seamContactHeat
  ring

/-! ## A signed three-cycle holonomy witness -/

/-- Parallel sections for a three-cycle with signs `(+1,+1,-1)`. -/
def signedThreeCycle (x y z : ℂ) : Prop := y = x ∧ z = y ∧ x = -z

/-- The negative sign holonomy admits only the zero parallel section. -/
theorem signedThreeCycle_only_zero {x y z : ℂ}
    (h : signedThreeCycle x y z) : x = 0 ∧ y = 0 ∧ z = 0 := by
  rcases h with ⟨hxy, hyz, hzx⟩
  have hx : x = 0 := by
    simp [hxy, hyz] at hzx
    linear_combination (1 / 2 : ℂ) * hzx
  exact ⟨hx, hxy ▸ hx, hyz ▸ hxy ▸ hx⟩

/-- The all-positive three-cycle admits every constant parallel section. -/
theorem positiveThreeCycle_constant (c : ℂ) : c = c ∧ c = c ∧ c = c :=
  ⟨rfl, rfl, rfl⟩

/-- Unit receiver reorientations transport a seam contact covariantly. -/
theorem seamMix_gauge_covariant
    (g h u x y : ℂ) (alpha : ℝ)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1) :
    seamMix (h * u * starRingEnd ℂ g) alpha (g * x) (h * y) =
      (g * (seamMix u alpha x y).1, h * (seamMix u alpha x y).2) := by
  have hgc : starRingEnd ℂ g * g = 1 := by
    simp [Complex.mul_conj, hg, mul_comm]
  have hhc : starRingEnd ℂ h * h = 1 := by
    simp [Complex.mul_conj, hh, mul_comm]
  have hdelta :
      seamDifference (h * u * starRingEnd ℂ g) (g * x) (h * y) =
        h * seamDifference u x y := by
    unfold seamDifference
    calc
      h * y - (h * u * starRingEnd ℂ g) * (g * x) =
          h * y - h * u * (starRingEnd ℂ g * g) * x := by ring
      _ = h * (y - u * x) := by rw [hgc]; ring
  have hcoef :
      starRingEnd ℂ (h * u * starRingEnd ℂ g) * h =
        g * starRingEnd ℂ u := by
    simp only [map_mul, starRingEnd_apply]
    simp
    calc
      starRingEnd ℂ h * starRingEnd ℂ u * g * h =
          starRingEnd ℂ u * g * (starRingEnd ℂ h * h) := by ring
      _ = g * starRingEnd ℂ u := by rw [hhc]; ring
  apply Prod.ext
  · change g * x + (alpha : ℂ) *
      starRingEnd ℂ (h * u * starRingEnd ℂ g) *
        seamDifference (h * u * starRingEnd ℂ g) (g * x) (h * y) =
      g * (x + (alpha : ℂ) * starRingEnd ℂ u * seamDifference u x y)
    rw [hdelta]
    rw [show (alpha : ℂ) * starRingEnd ℂ (h * u * starRingEnd ℂ g) *
        (h * seamDifference u x y) =
        (alpha : ℂ) * (starRingEnd ℂ (h * u * starRingEnd ℂ g) * h) *
          seamDifference u x y by ring]
    rw [hcoef]
    simp [seamDifference]
    ring
  · change h * y - (alpha : ℂ) *
      seamDifference (h * u * starRingEnd ℂ g) (g * x) (h * y) =
      h * (y - (alpha : ℂ) * seamDifference u x y)
    rw [hdelta]
    simp [seamDifference]
    ring

/-- The connection phase remains unit under the two receiver reorientations. -/
theorem seamMix_gauge_unit
    (g h u : ℂ) (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hu : Complex.normSq u = 1) :
    Complex.normSq (h * u * starRingEnd ℂ g) = 1 := by
  simp [Complex.normSq_mul, Complex.normSq_conj, hg, hh, hu]

/-- Affine nodal intensity loses exactly the retained phase variance. -/
theorem interpolation_intensity_defect (x y : ℂ) (t : ℝ) :
    (1 - t) * Complex.normSq x + t * Complex.normSq y -
        Complex.normSq ((1 - t : ℂ) * x + (t : ℂ) * y) =
      t * (1 - t) * Complex.normSq (y - x) := by
  norm_num [Complex.normSq_apply]
  ring

/-- The interpolation intensity defect is nonnegative on the unit interval. -/
theorem interpolation_intensity_defect_nonneg
    (x y : ℂ) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ (1 - t) * Complex.normSq x + t * Complex.normSq y -
      Complex.normSq ((1 - t : ℂ) * x + (t : ℂ) * y) := by
  rw [interpolation_intensity_defect]
  exact mul_nonneg (mul_nonneg ht₀ (sub_nonneg.mpr ht₁))
    (Complex.normSq_nonneg _)

end Soma.Holonics.Millennium.HolonicComplexParametron
