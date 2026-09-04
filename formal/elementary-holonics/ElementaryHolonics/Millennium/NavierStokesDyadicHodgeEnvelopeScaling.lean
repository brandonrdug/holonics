import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeSupportStencil

/-!
# Explicit scaling of the dyadic Hodge envelopes

**[proved-derived]** On scales at least three, the support-controlled denominator
`(2^s-3)^2` and aperture `outer+4` convert every rational Hodge envelope used by the
two-coordinate product rule into its required inverse dyadic power.  Constants are explicit and
intentionally coarse; no asymptotic premise is introduced.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil

def dyadicHodgeControlledLower (scale : ℕ) : ℝ :=
  ((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) ^ 2

def dyadicHodgeControlledBound (scale : ℕ) : ℝ :=
  (dyadicHodgeOuterCutoff (scale + 1) + 4 : ℝ)

theorem dyadicRadius_ge_eight_of_three_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    8 ≤ dyadicRadius scale := by
  change 2 ^ 3 ≤ 2 ^ scale
  exact Nat.pow_le_pow_right (by norm_num) hscale

theorem dyadicHodgeControlledBound_le_five_mul_radius
    (scale : ℕ) (hscale : 3 ≤ scale) :
    dyadicHodgeControlledBound scale ≤ 5 * (dyadicRadius scale : ℝ) := by
  have hradius := dyadicRadius_ge_eight_of_three_le scale hscale
  have hnext : dyadicRadius (scale + 2) = 4 * dyadicRadius scale := by
    simp only [dyadicRadius,
      show scale + 2 = (scale + 1) + 1 by omega, pow_succ]
    ring
  have hnat : dyadicHodgeOuterCutoff (scale + 1) + 4 ≤
      5 * dyadicRadius scale := by
    rw [dyadicHodgeOuterCutoff_eq, hnext]
    omega
  unfold dyadicHodgeControlledBound
  exact_mod_cast hnat

theorem half_radius_le_controlled_root
    (scale : ℕ) (hscale : 3 ≤ scale) :
    (dyadicRadius scale : ℝ) / 2 ≤
      ((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) := by
  have hradiusNat := dyadicRadius_ge_eight_of_three_le scale hscale
  have hsub : 3 ≤ dyadicHodgeInnerCutoff scale := by
    unfold dyadicHodgeInnerCutoff
    omega
  have hcast : ((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) =
      (dyadicRadius scale : ℝ) - 3 := by
    unfold dyadicHodgeInnerCutoff
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  have hradiusReal : (8 : ℝ) ≤ (dyadicRadius scale : ℝ) := by
    exact_mod_cast hradiusNat
  linarith

theorem dyadicHodgeControlledLower_pos
    (scale : ℕ) (hscale : 3 ≤ scale) :
    0 < dyadicHodgeControlledLower scale := by
  unfold dyadicHodgeControlledLower
  have hroot := half_radius_le_controlled_root scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hrootPos : 0 <
      ((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) :=
    (half_pos hradius).trans_le hroot
  exact sq_pos_of_pos hrootPos

theorem one_div_dyadicHodgeControlledLower_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    1 / dyadicHodgeControlledLower scale ≤
      4 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hroot := half_radius_le_controlled_root scale hscale
  have hsquare : (dyadicRadius scale : ℝ) ^ 2 ≤
      4 * dyadicHodgeControlledLower scale := by
    unfold dyadicHodgeControlledLower
    nlinarith [sq_nonneg
      (((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) -
        (dyadicRadius scale : ℝ) / 2)]
  rw [div_le_div_iff₀ hlower (sq_pos_of_pos hradius)]
  nlinarith

theorem one_div_dyadicHodgeControlledLower_sq_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    1 / dyadicHodgeControlledLower scale ^ 2 ≤
      16 / (dyadicRadius scale : ℝ) ^ 4 := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  calc
    1 / dyadicHodgeControlledLower scale ^ 2 =
        (1 / dyadicHodgeControlledLower scale) ^ 2 := by
          field_simp [hlower.ne']
    _ ≤ (4 / (dyadicRadius scale : ℝ) ^ 2) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity)
        (one_div_dyadicHodgeControlledLower_le scale hscale) 2
    _ = 16 / (dyadicRadius scale : ℝ) ^ 4 := by
      field_simp [hradius.ne']
      ring

theorem one_div_dyadicHodgeControlledLower_cube_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    1 / dyadicHodgeControlledLower scale ^ 3 ≤
      64 / (dyadicRadius scale : ℝ) ^ 6 := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  calc
    1 / dyadicHodgeControlledLower scale ^ 3 =
        (1 / dyadicHodgeControlledLower scale) ^ 3 := by
          field_simp [hlower.ne']
    _ ≤ (4 / (dyadicRadius scale : ℝ) ^ 2) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity)
        (one_div_dyadicHodgeControlledLower_le scale hscale) 3
    _ = 64 / (dyadicRadius scale : ℝ) ^ 6 := by
      field_simp [hradius.ne']
      ring

theorem two_mul_bound_add_one_le_eleven_mul_radius
    (scale : ℕ) (hscale : 3 ≤ scale) :
    2 * dyadicHodgeControlledBound scale + 1 ≤
      11 * (dyadicRadius scale : ℝ) := by
  have hbound := dyadicHodgeControlledBound_le_five_mul_radius scale hscale
  have hradius : 1 ≤ (dyadicRadius scale : ℝ) := by
    exact_mod_cast Nat.one_le_pow scale 2 (by norm_num)
  linarith

theorem four_mul_bound_add_four_le_twenty_four_mul_radius
    (scale : ℕ) (hscale : 3 ≤ scale) :
    4 * dyadicHodgeControlledBound scale + 4 ≤
      24 * (dyadicRadius scale : ℝ) := by
  have hbound := dyadicHodgeControlledBound_le_five_mul_radius scale hscale
  have hradius : 1 ≤ (dyadicRadius scale : ℝ) := by
    exact_mod_cast Nat.one_le_pow scale 2 (by norm_num)
  linarith

/-! ## Reciprocal envelopes -/

theorem hodgeReciprocalValueEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) ≤
      4 / (dyadicRadius scale : ℝ) ^ 2 := by
  exact one_div_dyadicHodgeControlledLower_le scale hscale

theorem hodgeReciprocalFirstEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalFirstEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      176 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  calc
    hodgeReciprocalFirstEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) =
      (2 * dyadicHodgeControlledBound scale + 1) *
        (1 / dyadicHodgeControlledLower scale ^ 2) := by
          unfold hodgeReciprocalFirstEnvelope
          field_simp [hlower.ne']
    _ ≤ (11 * (dyadicRadius scale : ℝ)) *
        (16 / (dyadicRadius scale : ℝ) ^ 4) := by
      exact mul_le_mul
        (two_mul_bound_add_one_le_eleven_mul_radius scale hscale)
        (one_div_dyadicHodgeControlledLower_sq_le scale hscale)
        (by positivity) (by positivity)
    _ = 176 / (dyadicRadius scale : ℝ) ^ 3 := by
      field_simp [hradius.ne']
      ring

theorem hodgeReciprocalSecondEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalSecondEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      17000 / (dyadicRadius scale : ℝ) ^ 4 := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  calc
    hodgeReciprocalSecondEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) =
      2 * (1 / dyadicHodgeControlledLower scale ^ 2) +
        (2 * dyadicHodgeControlledBound scale + 1) *
          (4 * dyadicHodgeControlledBound scale + 4) *
            (1 / dyadicHodgeControlledLower scale ^ 3) := by
      unfold hodgeReciprocalSecondEnvelope
      field_simp [hlower.ne']
    _ ≤ 2 * (16 / (dyadicRadius scale : ℝ) ^ 4) +
        (11 * (dyadicRadius scale : ℝ)) *
          (24 * (dyadicRadius scale : ℝ)) *
            (64 / (dyadicRadius scale : ℝ) ^ 6) := by
      have hfirst := mul_le_mul_of_nonneg_left
        (one_div_dyadicHodgeControlledLower_sq_le scale hscale)
        (by norm_num : (0 : ℝ) ≤ 2)
      have hboundProduct := mul_le_mul
        (two_mul_bound_add_one_le_eleven_mul_radius scale hscale)
        (four_mul_bound_add_four_le_twenty_four_mul_radius scale hscale)
        (by unfold dyadicHodgeControlledBound; positivity) (by positivity)
      have hsecond := mul_le_mul hboundProduct
        (one_div_dyadicHodgeControlledLower_cube_le scale hscale)
        (by positivity) (by positivity)
      exact add_le_add hfirst (by simpa only [mul_assoc] using hsecond)
    _ ≤ 17000 / (dyadicRadius scale : ℝ) ^ 4 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeReciprocalMixedOneOneEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalMixedOneOneEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      15500 / (dyadicRadius scale : ℝ) ^ 4 := by
  have hlower := dyadicHodgeControlledLower_pos scale hscale
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  calc
    hodgeReciprocalMixedOneOneEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) =
      2 * (2 * dyadicHodgeControlledBound scale + 1) ^ 2 *
        (1 / dyadicHodgeControlledLower scale ^ 3) := by
      unfold hodgeReciprocalMixedOneOneEnvelope
      field_simp [hlower.ne']
    _ ≤ 2 * (11 * (dyadicRadius scale : ℝ)) ^ 2 *
        (64 / (dyadicRadius scale : ℝ) ^ 6) := by
      have hboundSq := pow_le_pow_left₀
        (by unfold dyadicHodgeControlledBound; positivity)
        (two_mul_bound_add_one_le_eleven_mul_radius scale hscale) 2
      have hleft := mul_le_mul_of_nonneg_left hboundSq
        (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul hleft
        (one_div_dyadicHodgeControlledLower_cube_le scale hscale)
        (by positivity) (by positivity)
    _ ≤ 15500 / (dyadicRadius scale : ℝ) ^ 4 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeReciprocalMixedOneTwoEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalMixedOneTwoEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      2200000 / (dyadicRadius scale : ℝ) ^ 5 := by
  let value := hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale)
  let first := hodgeReciprocalFirstEnvelope
    (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
  let second := hodgeReciprocalSecondEnvelope
    (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
  let interaction := 2 * value * second + 2 * first ^ 2
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hvalue : value ≤ 4 / (dyadicRadius scale : ℝ) ^ 2 :=
    hodgeReciprocalValueEnvelope_dyadic_le scale hscale
  have hfirst : first ≤ 176 / (dyadicRadius scale : ℝ) ^ 3 :=
    hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hsecond : second ≤ 17000 / (dyadicRadius scale : ℝ) ^ 4 :=
    hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have hvalueNonneg : 0 ≤ value := by
    dsimp [value]
    unfold hodgeReciprocalValueEnvelope dyadicHodgeControlledLower
    positivity
  have hfirstNonneg : 0 ≤ first := by
    dsimp [first]
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hsecondNonneg : 0 ≤ second := by
    dsimp [second]
    unfold hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hvalueSecond := mul_le_mul hvalue hsecond hsecondNonneg (by positivity)
  have hvalueSecond' := mul_le_mul_of_nonneg_left hvalueSecond
    (by norm_num : (0 : ℝ) ≤ 2)
  have hfirstSq := pow_le_pow_left₀ hfirstNonneg hfirst 2
  have hfirstSq' := mul_le_mul_of_nonneg_left hfirstSq
    (by norm_num : (0 : ℝ) ≤ 2)
  have hinteraction : interaction ≤
      198000 / (dyadicRadius scale : ℝ) ^ 6 := by
    dsimp [interaction]
    calc
      2 * value * second + 2 * first ^ 2 ≤
          2 * (4 / (dyadicRadius scale : ℝ) ^ 2) *
              (17000 / (dyadicRadius scale : ℝ) ^ 4) +
            2 * (176 / (dyadicRadius scale : ℝ) ^ 3) ^ 2 :=
        add_le_add (by simpa only [mul_assoc] using hvalueSecond') hfirstSq'
      _ ≤ 198000 / (dyadicRadius scale : ℝ) ^ 6 := by
        field_simp [hradius.ne']
        norm_num
  have hinteractionNonneg : 0 ≤ interaction := by
    dsimp [interaction]
    positivity
  have hbound := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  unfold hodgeReciprocalMixedOneTwoEnvelope
  change (2 * dyadicHodgeControlledBound scale + 1) * interaction ≤ _
  calc
    (2 * dyadicHodgeControlledBound scale + 1) * interaction ≤
        (11 * (dyadicRadius scale : ℝ)) *
          (198000 / (dyadicRadius scale : ℝ) ^ 6) :=
      mul_le_mul hbound hinteraction hinteractionNonneg (by positivity)
    _ ≤ 2200000 / (dyadicRadius scale : ℝ) ^ 5 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeReciprocalMixedTwoTwoEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      420000000 / (dyadicRadius scale : ℝ) ^ 6 := by
  let value := hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale)
  let first := hodgeReciprocalFirstEnvelope
    (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
  let second := hodgeReciprocalSecondEnvelope
    (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale)
  let interaction := 2 * value * second + 2 * first ^ 2
  let higher := 3 * value ^ 2 * second + 6 * value * first ^ 2
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hvalue : value ≤ 4 / (dyadicRadius scale : ℝ) ^ 2 :=
    hodgeReciprocalValueEnvelope_dyadic_le scale hscale
  have hfirst : first ≤ 176 / (dyadicRadius scale : ℝ) ^ 3 :=
    hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hsecond : second ≤ 17000 / (dyadicRadius scale : ℝ) ^ 4 :=
    hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have hvalueNonneg : 0 ≤ value := by
    dsimp [value]
    unfold hodgeReciprocalValueEnvelope dyadicHodgeControlledLower
    positivity
  have hfirstNonneg : 0 ≤ first := by
    dsimp [first]
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hsecondNonneg : 0 ≤ second := by
    dsimp [second]
    unfold hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hvalueSq := pow_le_pow_left₀ hvalueNonneg hvalue 2
  have hfirstSq := pow_le_pow_left₀ hfirstNonneg hfirst 2
  have hvalueSecond := mul_le_mul hvalue hsecond hsecondNonneg (by positivity)
  have hvalueSqSecond := mul_le_mul hvalueSq hsecond hsecondNonneg (by positivity)
  have hvalueFirstSq := mul_le_mul hvalue hfirstSq (sq_nonneg first) (by positivity)
  have hinteraction : interaction ≤
      198000 / (dyadicRadius scale : ℝ) ^ 6 := by
    dsimp [interaction]
    calc
      2 * value * second + 2 * first ^ 2 ≤
          2 * (4 / (dyadicRadius scale : ℝ) ^ 2) *
              (17000 / (dyadicRadius scale : ℝ) ^ 4) +
            2 * (176 / (dyadicRadius scale : ℝ) ^ 3) ^ 2 := by
        exact add_le_add
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hvalueSecond (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hfirstSq (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ 198000 / (dyadicRadius scale : ℝ) ^ 6 := by
        field_simp [hradius.ne']
        norm_num
  have hhigher : higher ≤
      1560000 / (dyadicRadius scale : ℝ) ^ 8 := by
    dsimp [higher]
    calc
      3 * value ^ 2 * second + 6 * value * first ^ 2 ≤
          3 * (4 / (dyadicRadius scale : ℝ) ^ 2) ^ 2 *
              (17000 / (dyadicRadius scale : ℝ) ^ 4) +
            6 * (4 / (dyadicRadius scale : ℝ) ^ 2) *
              (176 / (dyadicRadius scale : ℝ) ^ 3) ^ 2 := by
        exact add_le_add
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hvalueSqSecond (by norm_num : (0 : ℝ) ≤ 3))
          (by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hvalueFirstSq (by norm_num : (0 : ℝ) ≤ 6))
      _ ≤ 1560000 / (dyadicRadius scale : ℝ) ^ 8 := by
        field_simp [hradius.ne']
        norm_num
  have hinteractionNonneg : 0 ≤ interaction := by
    dsimp [interaction]
    positivity
  have hhigherNonneg : 0 ≤ higher := by
    dsimp [higher]
    positivity
  have hboundProduct := mul_le_mul
    (two_mul_bound_add_one_le_eleven_mul_radius scale hscale)
    (four_mul_bound_add_four_le_twenty_four_mul_radius scale hscale)
    (by unfold dyadicHodgeControlledBound; positivity) (by positivity)
  unfold hodgeReciprocalMixedTwoTwoEnvelope
  change 2 * interaction +
      (2 * dyadicHodgeControlledBound scale + 1) *
        (4 * dyadicHodgeControlledBound scale + 4) * higher ≤ _
  calc
    2 * interaction +
        (2 * dyadicHodgeControlledBound scale + 1) *
          (4 * dyadicHodgeControlledBound scale + 4) * higher ≤
      2 * (198000 / (dyadicRadius scale : ℝ) ^ 6) +
        ((11 * (dyadicRadius scale : ℝ)) *
          (24 * (dyadicRadius scale : ℝ))) *
            (1560000 / (dyadicRadius scale : ℝ) ^ 8) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hinteraction (by norm_num))
        (mul_le_mul hboundProduct hhigher hhigherNonneg (by positivity))
    _ ≤ 420000000 / (dyadicRadius scale : ℝ) ^ 6 := by
      field_simp [hradius.ne']
      norm_num

/-! ## Genuine Hodge-entry envelopes -/

theorem dyadicHodgeControlledBound_sq_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    dyadicHodgeControlledBound scale ^ 2 ≤
      25 * (dyadicRadius scale : ℝ) ^ 2 := by
  have hbound := dyadicHodgeControlledBound_le_five_mul_radius scale hscale
  have hboundNonneg : 0 ≤ dyadicHodgeControlledBound scale := by
    unfold dyadicHodgeControlledBound
    positivity
  have hsquare := pow_le_pow_left₀ hboundNonneg hbound 2
  nlinarith

theorem hodgeJacobianEntryFirstEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryFirstEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      14000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hvalue := hodgeReciprocalValueEnvelope_dyadic_le scale hscale
  have hfirst := hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hlinear := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hsq := dyadicHodgeControlledBound_sq_le scale hscale
  have hvalueNonneg : 0 ≤
      hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) := by
    unfold hodgeReciprocalValueEnvelope dyadicHodgeControlledLower
    positivity
  have hfirstNonneg : 0 ≤ hodgeReciprocalFirstEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  unfold hodgeJacobianEntryFirstEnvelope
  calc
    (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) +
        3 * dyadicHodgeControlledBound scale ^ 2 *
          hodgeReciprocalFirstEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      (11 * (dyadicRadius scale : ℝ)) *
          (4 / (dyadicRadius scale : ℝ) ^ 2) +
        (3 * (25 * (dyadicRadius scale : ℝ) ^ 2)) *
          (176 / (dyadicRadius scale : ℝ) ^ 3) := by
      exact add_le_add
        (mul_le_mul hlinear hvalue hvalueNonneg (by positivity))
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3))
          hfirst hfirstNonneg (by positivity))
    _ ≤ 14000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeJacobianEntrySecondEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntrySecondEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      1300000 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hvalue := hodgeReciprocalValueEnvelope_dyadic_le scale hscale
  have hfirst := hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hsecond := hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have hlinear := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hsq := dyadicHodgeControlledBound_sq_le scale hscale
  have hvalueNonneg : 0 ≤
      hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) := by
    unfold hodgeReciprocalValueEnvelope dyadicHodgeControlledLower
    positivity
  have hfirstNonneg : 0 ≤ hodgeReciprocalFirstEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hsecondNonneg : 0 ≤ hodgeReciprocalSecondEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  unfold hodgeJacobianEntrySecondEnvelope
  calc
    2 * hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) +
        2 * (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalFirstEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        3 * dyadicHodgeControlledBound scale ^ 2 *
          hodgeReciprocalSecondEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      2 * (4 / (dyadicRadius scale : ℝ) ^ 2) +
        (2 * (11 * (dyadicRadius scale : ℝ))) *
          (176 / (dyadicRadius scale : ℝ) ^ 3) +
        (3 * (25 * (dyadicRadius scale : ℝ) ^ 2)) *
          (17000 / (dyadicRadius scale : ℝ) ^ 4) := by
      have htermValue := mul_le_mul_of_nonneg_left hvalue
        (by norm_num : (0 : ℝ) ≤ 2)
      have htermFirst := mul_le_mul
        (mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2))
        hfirst hfirstNonneg (by positivity)
      have htermSecond := mul_le_mul
        (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3))
        hsecond hsecondNonneg (by positivity)
      exact add_le_add (add_le_add htermValue htermFirst) htermSecond
    _ ≤ 1300000 / (dyadicRadius scale : ℝ) ^ 2 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeJacobianEntryMixedOneOneEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryMixedOneOneEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      1200000 / (dyadicRadius scale : ℝ) ^ 2 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hvalue := hodgeReciprocalValueEnvelope_dyadic_le scale hscale
  have hfirst := hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hmixed := hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have hlinear := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hsq := dyadicHodgeControlledBound_sq_le scale hscale
  have hfirstNonneg : 0 ≤ hodgeReciprocalFirstEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hmixedNonneg : 0 ≤ hodgeReciprocalMixedOneOneEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedOneOneEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  unfold hodgeJacobianEntryMixedOneOneEnvelope
  calc
    2 * hodgeReciprocalValueEnvelope (dyadicHodgeControlledLower scale) +
        2 * (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalFirstEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        3 * dyadicHodgeControlledBound scale ^ 2 *
          hodgeReciprocalMixedOneOneEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      2 * (4 / (dyadicRadius scale : ℝ) ^ 2) +
        (2 * (11 * (dyadicRadius scale : ℝ))) *
          (176 / (dyadicRadius scale : ℝ) ^ 3) +
        (3 * (25 * (dyadicRadius scale : ℝ) ^ 2)) *
          (15500 / (dyadicRadius scale : ℝ) ^ 4) := by
      have htermValue := mul_le_mul_of_nonneg_left hvalue
        (by norm_num : (0 : ℝ) ≤ 2)
      have htermFirst := mul_le_mul
        (mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2))
        hfirst hfirstNonneg (by positivity)
      have htermMixed := mul_le_mul
        (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3))
        hmixed hmixedNonneg (by positivity)
      exact add_le_add (add_le_add htermValue htermFirst) htermMixed
    _ ≤ 1200000 / (dyadicRadius scale : ℝ) ^ 2 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryMixedOneTwoEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      166000000 / (dyadicRadius scale : ℝ) ^ 3 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hfirst := hodgeReciprocalFirstEnvelope_dyadic_le scale hscale
  have hsecond := hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have hmixed11 := hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have hmixed12 := hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have hlinear := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hsq := dyadicHodgeControlledBound_sq_le scale hscale
  have hfirstNonneg : 0 ≤ hodgeReciprocalFirstEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalFirstEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hsecondNonneg : 0 ≤ hodgeReciprocalSecondEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hmixed11Nonneg : 0 ≤ hodgeReciprocalMixedOneOneEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedOneOneEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hmixed12Nonneg : 0 ≤ hodgeReciprocalMixedOneTwoEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  unfold hodgeJacobianEntryMixedOneTwoEnvelope
  calc
    6 * hodgeReciprocalFirstEnvelope
          (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalSecondEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        2 * (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalMixedOneOneEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        3 * dyadicHodgeControlledBound scale ^ 2 *
          hodgeReciprocalMixedOneTwoEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      6 * (176 / (dyadicRadius scale : ℝ) ^ 3) +
        (11 * (dyadicRadius scale : ℝ)) *
          (17000 / (dyadicRadius scale : ℝ) ^ 4) +
        (2 * (11 * (dyadicRadius scale : ℝ))) *
          (15500 / (dyadicRadius scale : ℝ) ^ 4) +
        (3 * (25 * (dyadicRadius scale : ℝ) ^ 2)) *
          (2200000 / (dyadicRadius scale : ℝ) ^ 5) := by
      have htermFirst := mul_le_mul_of_nonneg_left hfirst
        (by norm_num : (0 : ℝ) ≤ 6)
      have htermSecond := mul_le_mul hlinear hsecond hsecondNonneg (by positivity)
      have htermMixed11 := mul_le_mul
        (mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 2))
        hmixed11 hmixed11Nonneg (by positivity)
      have htermMixed12 := mul_le_mul
        (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3))
        hmixed12 hmixed12Nonneg (by positivity)
      exact add_le_add
        (add_le_add (add_le_add htermFirst htermSecond) htermMixed11)
        htermMixed12
    _ ≤ 166000000 / (dyadicRadius scale : ℝ) ^ 3 := by
      field_simp [hradius.ne']
      norm_num

theorem hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    hodgeJacobianEntryMixedTwoTwoEnvelope
        (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      32000000000 / (dyadicRadius scale : ℝ) ^ 4 := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hsecond := hodgeReciprocalSecondEnvelope_dyadic_le scale hscale
  have hmixed11 := hodgeReciprocalMixedOneOneEnvelope_dyadic_le scale hscale
  have hmixed12 := hodgeReciprocalMixedOneTwoEnvelope_dyadic_le scale hscale
  have hmixed22 := hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le scale hscale
  have hlinear := two_mul_bound_add_one_le_eleven_mul_radius scale hscale
  have hsq := dyadicHodgeControlledBound_sq_le scale hscale
  have hsecondNonneg : 0 ≤ hodgeReciprocalSecondEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalSecondEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hmixed11Nonneg : 0 ≤ hodgeReciprocalMixedOneOneEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedOneOneEnvelope dyadicHodgeControlledLower
      dyadicHodgeControlledBound
    positivity
  have hmixed12Nonneg : 0 ≤ hodgeReciprocalMixedOneTwoEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedOneTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  have hmixed22Nonneg : 0 ≤ hodgeReciprocalMixedTwoTwoEnvelope
      (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) := by
    unfold hodgeReciprocalMixedTwoTwoEnvelope hodgeReciprocalValueEnvelope
      hodgeReciprocalFirstEnvelope hodgeReciprocalSecondEnvelope
      dyadicHodgeControlledLower dyadicHodgeControlledBound
    positivity
  unfold hodgeJacobianEntryMixedTwoTwoEnvelope
  calc
    4 * hodgeReciprocalSecondEnvelope
          (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        8 * hodgeReciprocalMixedOneOneEnvelope
          (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        4 * (2 * dyadicHodgeControlledBound scale + 1) *
          hodgeReciprocalMixedOneTwoEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) +
        3 * dyadicHodgeControlledBound scale ^ 2 *
          hodgeReciprocalMixedTwoTwoEnvelope
            (dyadicHodgeControlledLower scale) (dyadicHodgeControlledBound scale) ≤
      4 * (17000 / (dyadicRadius scale : ℝ) ^ 4) +
        8 * (15500 / (dyadicRadius scale : ℝ) ^ 4) +
        (4 * (11 * (dyadicRadius scale : ℝ))) *
          (2200000 / (dyadicRadius scale : ℝ) ^ 5) +
        (3 * (25 * (dyadicRadius scale : ℝ) ^ 2)) *
          (420000000 / (dyadicRadius scale : ℝ) ^ 6) := by
      have htermSecond := mul_le_mul_of_nonneg_left hsecond
        (by norm_num : (0 : ℝ) ≤ 4)
      have htermMixed11 := mul_le_mul_of_nonneg_left hmixed11
        (by norm_num : (0 : ℝ) ≤ 8)
      have htermMixed12 := mul_le_mul
        (mul_le_mul_of_nonneg_left hlinear (by norm_num : (0 : ℝ) ≤ 4))
        hmixed12 hmixed12Nonneg (by positivity)
      have htermMixed22 := mul_le_mul
        (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 3))
        hmixed22 hmixed22Nonneg (by positivity)
      exact add_le_add
        (add_le_add (add_le_add htermSecond htermMixed11) htermMixed12)
        htermMixed22
    _ ≤ 32000000000 / (dyadicRadius scale : ℝ) ^ 4 := by
      field_simp [hradius.ne']
      norm_num

section Audit

#print axioms hodgeReciprocalMixedTwoTwoEnvelope_dyadic_le
#print axioms hodgeJacobianEntryMixedOneTwoEnvelope_dyadic_le
#print axioms hodgeJacobianEntryMixedTwoTwoEnvelope_dyadic_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeEnvelopeScaling
