import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeProductMass
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling

/-!
# Inverse-cube scaling of the three-axis Hodge mass

The scale descent and the twenty-seven-face product allocation are exact before this file.  Here
they are evaluated on the dyadic annular aperture.  The recursive reciprocal orders scale as
`R⁻⁵`, `R⁻⁶`, `R⁻⁷`, and `R⁻⁸`; after the quadratic Hodge numerator weights are restored, every
surviving allocation has the common `R⁻⁶` scale.  Since the Hodge denominator is quadratic, this
is inverse cube in `q = |k|²`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling

private theorem mixedOneOneEnvelope_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocalMixedOneOneEnvelope lower bound := by
  unfold hodgeReciprocalMixedOneOneEnvelope
  positivity

private theorem mixedOneTwoEnvelope_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocalMixedOneTwoEnvelope lower bound := by
  unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
    hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
  positivity

private theorem mixedTwoTwoEnvelope_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
  unfold hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalValueEnvelope
    hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
  positivity

private theorem envelope111_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocal111Envelope lower bound := by
  unfold hodgeReciprocal111Envelope
  positivity [mixedOneOneEnvelope_nonneg hlower hbound]

private theorem envelope112_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocal112Envelope lower bound := by
  unfold hodgeReciprocal112Envelope
  positivity [envelope111_nonneg hlower hbound,
    mixedOneTwoEnvelope_nonneg hlower hbound,
    mixedOneOneEnvelope_nonneg hlower hbound]

private theorem envelope122_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocal122Envelope lower bound := by
  unfold hodgeReciprocal122Envelope
  positivity [mixedTwoTwoEnvelope_nonneg hlower hbound,
    envelope112_nonneg hlower hbound, mixedOneTwoEnvelope_nonneg hlower hbound]

private theorem envelope222_nonneg
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound) :
    0 ≤ hodgeReciprocal222Envelope lower bound := by
  unfold hodgeReciprocal222Envelope
  positivity [envelope122_nonneg hlower hbound, mixedTwoTwoEnvelope_nonneg hlower hbound]

/-- The first three-axis reciprocal order has the expected inverse-fifth radial scale. -/
theorem hodgeReciprocal111Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocal111Envelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      3000000 / (dyadicRadius scale : ℝ) ^ 5 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let mixed11 := hodgeReciprocalMixedOneOneEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ bound := by
    dsimp [bound, dyadicHodgeControlledBound]
    positivity
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hmixed11 : mixed11 ≤ 15500 / radius ^ 4 := by
    simpa [mixed11, lower, bound, radius] using
      hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have hinverse : lower⁻¹ ≤ 4 / radius ^ 2 := by
    simpa [one_div, lower, radius] using
      one_div_dyadicHodgeControlledLower_le scale hscale
  have hmixed11Nonneg : 0 ≤ mixed11 := mixedOneOneEnvelope_nonneg hlower hbound
  have hinverseNonneg : 0 ≤ lower⁻¹ := inv_nonneg.mpr hlower.le
  have hnumerator : 3 * (2 * bound + 1) * mixed11 ≤
      3 * (11 * radius) * (15500 / radius ^ 4) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hlinear (by norm_num)) hmixed11
      hmixed11Nonneg (by positivity)
  unfold hodgeReciprocal111Envelope
  change 3 * (2 * bound + 1) * mixed11 / lower ≤ _
  rw [div_eq_mul_inv]
  calc
    3 * (2 * bound + 1) * mixed11 * lower⁻¹ ≤
        (3 * (11 * radius) * (15500 / radius ^ 4)) * (4 / radius ^ 2) :=
      mul_le_mul hnumerator hinverse hinverseNonneg (by positivity)
    _ ≤ 3000000 / radius ^ 5 := by
      field_simp [hradius.ne']
      norm_num

/-- The `112` reciprocal order has inverse-sixth radial scale. -/
theorem hodgeReciprocal112Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocal112Envelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      600000000 / (dyadicRadius scale : ℝ) ^ 6 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e111 := hodgeReciprocal111Envelope lower bound
  let mixed12 := hodgeReciprocalMixedOneTwoEnvelope lower bound
  let mixed11 := hodgeReciprocalMixedOneOneEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ bound := by
    dsimp [bound, dyadicHodgeControlledBound]
    positivity
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h111 : e111 ≤ 3000000 / radius ^ 5 := by
    simpa [e111, lower, bound, radius] using hodgeReciprocal111Envelope_dyadic_le scale hscale
  have h12 : mixed12 ≤ 2200000 / radius ^ 5 := by
    simpa [mixed12, lower, bound, radius] using
      hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have h11 : mixed11 ≤ 15500 / radius ^ 4 := by
    simpa [mixed11, lower, bound, radius] using
      hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have hinverse : lower⁻¹ ≤ 4 / radius ^ 2 := by
    simpa [one_div, lower, radius] using
      one_div_dyadicHodgeControlledLower_le scale hscale
  have h111Nonneg : 0 ≤ e111 := envelope111_nonneg hlower hbound
  have h12Nonneg : 0 ≤ mixed12 := mixedOneTwoEnvelope_nonneg hlower hbound
  have h11Nonneg : 0 ≤ mixed11 := mixedOneOneEnvelope_nonneg hlower hbound
  have hinverseNonneg : 0 ≤ lower⁻¹ := inv_nonneg.mpr hlower.le
  have hterm111 : 2 * (2 * bound + 1) * e111 ≤
      2 * (11 * radius) * (3000000 / radius ^ 5) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h111
      h111Nonneg (by positivity)
  have hterm12 : 2 * (2 * bound + 1) * mixed12 ≤
      2 * (11 * radius) * (2200000 / radius ^ 5) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h12
      h12Nonneg (by positivity)
  have hterm11 : 2 * mixed11 ≤ 2 * (15500 / radius ^ 4) :=
    mul_le_mul_of_nonneg_left h11 (by norm_num)
  have hnumerator :
      2 * (2 * bound + 1) * e111 + 2 * (2 * bound + 1) * mixed12 + 2 * mixed11 ≤
        2 * (11 * radius) * (3000000 / radius ^ 5) +
          2 * (11 * radius) * (2200000 / radius ^ 5) +
            2 * (15500 / radius ^ 4) := by
    exact add_le_add (add_le_add hterm111 hterm12) hterm11
  unfold hodgeReciprocal112Envelope
  change (2 * (2 * bound + 1) * e111 + 2 * (2 * bound + 1) * mixed12 +
    2 * mixed11) / lower ≤ _
  rw [div_eq_mul_inv]
  calc
    (2 * (2 * bound + 1) * e111 + 2 * (2 * bound + 1) * mixed12 +
        2 * mixed11) * lower⁻¹ ≤
      (2 * (11 * radius) * (3000000 / radius ^ 5) +
          2 * (11 * radius) * (2200000 / radius ^ 5) +
            2 * (15500 / radius ^ 4)) * (4 / radius ^ 2) :=
      mul_le_mul hnumerator hinverse hinverseNonneg (by positivity)
    _ ≤ 600000000 / radius ^ 6 := by
      field_simp [hradius.ne']
      norm_num

/-- The `122` reciprocal order has inverse-seventh radial scale. -/
theorem hodgeReciprocal122Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocal122Envelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      150000000000 / (dyadicRadius scale : ℝ) ^ 7 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let mixed22 := hodgeReciprocalMixedTwoTwoEnvelope lower bound
  let e112 := hodgeReciprocal112Envelope lower bound
  let mixed12 := hodgeReciprocalMixedOneTwoEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ bound := by
    dsimp [bound, dyadicHodgeControlledBound]
    positivity
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h22 : mixed22 ≤ 420000000 / radius ^ 6 := by
    simpa [mixed22, lower, bound, radius] using
      hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le scale hscale
  have h112 : e112 ≤ 600000000 / radius ^ 6 := by
    simpa [e112, lower, bound, radius] using hodgeReciprocal112Envelope_dyadic_le scale hscale
  have h12 : mixed12 ≤ 2200000 / radius ^ 5 := by
    simpa [mixed12, lower, bound, radius] using
      hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have hinverse : lower⁻¹ ≤ 4 / radius ^ 2 := by
    simpa [one_div, lower, radius] using
      one_div_dyadicHodgeControlledLower_le scale hscale
  have h22Nonneg : 0 ≤ mixed22 := mixedTwoTwoEnvelope_nonneg hlower hbound
  have h112Nonneg : 0 ≤ e112 := envelope112_nonneg hlower hbound
  have h12Nonneg : 0 ≤ mixed12 := mixedOneTwoEnvelope_nonneg hlower hbound
  have hinverseNonneg : 0 ≤ lower⁻¹ := inv_nonneg.mpr hlower.le
  have hterm22 : (2 * bound + 1) * mixed22 ≤
      (11 * radius) * (420000000 / radius ^ 6) :=
    mul_le_mul hlinear h22 h22Nonneg (by positivity)
  have hterm112 : 4 * (2 * bound + 1) * e112 ≤
      4 * (11 * radius) * (600000000 / radius ^ 6) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h112
      h112Nonneg (by positivity)
  have hterm12 : 4 * mixed12 ≤ 4 * (2200000 / radius ^ 5) :=
    mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hnumerator :
      (2 * bound + 1) * mixed22 + 4 * (2 * bound + 1) * e112 + 4 * mixed12 ≤
        (11 * radius) * (420000000 / radius ^ 6) +
          4 * (11 * radius) * (600000000 / radius ^ 6) +
            4 * (2200000 / radius ^ 5) := by
    exact add_le_add (add_le_add hterm22 hterm112) hterm12
  unfold hodgeReciprocal122Envelope
  change ((2 * bound + 1) * mixed22 + 4 * (2 * bound + 1) * e112 +
    4 * mixed12) / lower ≤ _
  rw [div_eq_mul_inv]
  calc
    ((2 * bound + 1) * mixed22 + 4 * (2 * bound + 1) * e112 +
        4 * mixed12) * lower⁻¹ ≤
      ((11 * radius) * (420000000 / radius ^ 6) +
          4 * (11 * radius) * (600000000 / radius ^ 6) +
            4 * (2200000 / radius ^ 5)) * (4 / radius ^ 2) :=
      mul_le_mul hnumerator hinverse hinverseNonneg (by positivity)
    _ ≤ 150000000000 / radius ^ 7 := by
      field_simp [hradius.ne']
      norm_num

/-- The top `222` reciprocal order has inverse-eighth radial scale. -/
theorem hodgeReciprocal222Envelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocal222Envelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      50000000000000 / (dyadicRadius scale : ℝ) ^ 8 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e122 := hodgeReciprocal122Envelope lower bound
  let mixed22 := hodgeReciprocalMixedTwoTwoEnvelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower : 0 < lower := by
    simpa [lower] using dyadicHodgeControlledLower_pos scale hscale
  have hbound : 0 ≤ bound := by
    dsimp [bound, dyadicHodgeControlledBound]
    positivity
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h122 : e122 ≤ 150000000000 / radius ^ 7 := by
    simpa [e122, lower, bound, radius] using hodgeReciprocal122Envelope_dyadic_le scale hscale
  have h22 : mixed22 ≤ 420000000 / radius ^ 6 := by
    simpa [mixed22, lower, bound, radius] using
      hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le scale hscale
  have hinverse : lower⁻¹ ≤ 4 / radius ^ 2 := by
    simpa [one_div, lower, radius] using
      one_div_dyadicHodgeControlledLower_le scale hscale
  have h122Nonneg : 0 ≤ e122 := envelope122_nonneg hlower hbound
  have h22Nonneg : 0 ≤ mixed22 := mixedTwoTwoEnvelope_nonneg hlower hbound
  have hinverseNonneg : 0 ≤ lower⁻¹ := inv_nonneg.mpr hlower.le
  have hterm122 : 6 * (2 * bound + 1) * e122 ≤
      6 * (11 * radius) * (150000000000 / radius ^ 7) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h122
      h122Nonneg (by positivity)
  have hterm22 : 6 * mixed22 ≤ 6 * (420000000 / radius ^ 6) :=
    mul_le_mul_of_nonneg_left h22 (by norm_num)
  have hnumerator :
      6 * (2 * bound + 1) * e122 + 6 * mixed22 ≤
        6 * (11 * radius) * (150000000000 / radius ^ 7) +
          6 * (420000000 / radius ^ 6) := add_le_add hterm122 hterm22
  unfold hodgeReciprocal222Envelope
  change (6 * (2 * bound + 1) * e122 + 6 * mixed22) / lower ≤ _
  rw [div_eq_mul_inv]
  calc
    (6 * (2 * bound + 1) * e122 + 6 * mixed22) * lower⁻¹ ≤
      (6 * (11 * radius) * (150000000000 / radius ^ 7) +
        6 * (420000000 / radius ^ 6)) * (4 / radius ^ 2) :=
      mul_le_mul hnumerator hinverse hinverseNonneg (by positivity)
    _ ≤ 50000000000000 / radius ^ 8 := by
      field_simp [hradius.ne']
      norm_num

/-- The full `(2,2,2)` Hodge allocation mass is inverse cubic in the quadratic frequency scale:
equivalently, it is bounded by an explicit constant times `R⁻⁶`. -/
theorem hodgeJacobianEntryThreeAxisFullMixedEnvelope_dyadic_inverseCube_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryThreeAxisFullMixedEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      4000000000000000 / (dyadicRadius scale : ℝ) ^ 6 := by
  let radius : ℝ := dyadicRadius scale
  let lower := dyadicHodgeControlledLower scale
  let bound := dyadicHodgeControlledBound scale
  let e222 := hodgeReciprocal222Envelope lower bound
  let e122 := hodgeReciprocal122Envelope lower bound
  let mixed22 := hodgeReciprocalMixedTwoTwoEnvelope lower bound
  let e112 := hodgeReciprocal112Envelope lower bound
  have hradius : 0 < radius := by
    dsimp [radius]
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hboundSq : bound ^ 2 ≤ 25 * radius ^ 2 := by
    simpa [bound, radius] using dyadicHodgeControlledBound_sq_le scale hscale
  have hlinear : 2 * bound + 1 ≤ 11 * radius := by
    simpa [bound, radius] using two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have h222 : e222 ≤ 50000000000000 / radius ^ 8 := by
    simpa [e222, lower, bound, radius] using hodgeReciprocal222Envelope_dyadic_le scale hscale
  have h122 : e122 ≤ 150000000000 / radius ^ 7 := by
    simpa [e122, lower, bound, radius] using hodgeReciprocal122Envelope_dyadic_le scale hscale
  have h22 : mixed22 ≤ 420000000 / radius ^ 6 := by
    simpa [mixed22, lower, bound, radius] using
      hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le scale hscale
  have h112 : e112 ≤ 600000000 / radius ^ 6 := by
    simpa [e112, lower, bound, radius] using hodgeReciprocal112Envelope_dyadic_le scale hscale
  have h222Nonneg : 0 ≤ e222 := by
    dsimp [e222, lower, bound]
    unfold hodgeReciprocal222Envelope hodgeReciprocal122Envelope
      hodgeReciprocal112Envelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalMixedOneTwoEnvelope
      hodgeReciprocalMixedOneOneEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h122Nonneg : 0 ≤ e122 := by
    dsimp [e122, lower, bound]
    unfold hodgeReciprocal122Envelope hodgeReciprocal112Envelope
      hodgeReciprocal111Envelope hodgeReciprocalMixedTwoTwoEnvelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h22Nonneg : 0 ≤ mixed22 := by
    dsimp [mixed22, lower, bound]
    unfold hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have h112Nonneg : 0 ≤ e112 := by
    dsimp [e112, lower, bound]
    unfold hodgeReciprocal112Envelope hodgeReciprocal111Envelope
      hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalMixedOneOneEnvelope
      hodgeReciprocalValueEnvelope hodgeReciprocalFirstEnvelope
      hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hterm222 : 3 * bound ^ 2 * e222 ≤
      3 * (25 * radius ^ 2) * (50000000000000 / radius ^ 8) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hboundSq (by norm_num)) h222
      h222Nonneg (by positivity)
  have hterm122 : 6 * (2 * bound + 1) * e122 ≤
      6 * (11 * radius) * (150000000000 / radius ^ 7) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlinear (by norm_num)) h122
      h122Nonneg (by positivity)
  have hterm22 : 6 * mixed22 ≤ 6 * (420000000 / radius ^ 6) :=
    mul_le_mul_of_nonneg_left h22 (by norm_num)
  have hterm112 : 24 * e112 ≤ 24 * (600000000 / radius ^ 6) :=
    mul_le_mul_of_nonneg_left h112 (by norm_num)
  unfold hodgeJacobianEntryThreeAxisFullMixedEnvelope
  change 3 * bound ^ 2 * e222 + 6 * (2 * bound + 1) * e122 +
    6 * mixed22 + 24 * e112 ≤ _
  calc
    3 * bound ^ 2 * e222 + 6 * (2 * bound + 1) * e122 +
        6 * mixed22 + 24 * e112 ≤
      3 * (25 * radius ^ 2) * (50000000000000 / radius ^ 8) +
        6 * (11 * radius) * (150000000000 / radius ^ 7) +
          6 * (420000000 / radius ^ 6) + 24 * (600000000 / radius ^ 6) := by
      exact add_le_add (add_le_add (add_le_add hterm222 hterm122) hterm22) hterm112
    _ ≤ 4000000000000000 / radius ^ 6 := by
      field_simp [hradius.ne']
      norm_num

end Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass

section Audit
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeDyadicMass
#print axioms hodgeReciprocal111Envelope_dyadic_le
#print axioms hodgeReciprocal112Envelope_dyadic_le
#print axioms hodgeReciprocal122Envelope_dyadic_le
#print axioms hodgeReciprocal222Envelope_dyadic_le
#print axioms hodgeJacobianEntryThreeAxisFullMixedEnvelope_dyadic_inverseCube_le
end Audit
