import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.XiEdgeDecomposition

/-!
# `ξ` is not small on the line `Re s = 2`

Landau's lemma for `ξ` about the base point `2 + iT` normalises by `|ξ(2 + iT)|`, so the
horizontal-edge bound of the explicit formula needs a lower bound there.  Three facts give it:
`|ζ(s)| ≥ 6/π²` right of `Re s = 2` (the Möbius series inverts `ζ` and is bounded by `ζ(2)`),
`|Γ(1 + iy)|² = πy / sinh(πy)` (the reflection formula), and `|s (s − 1)| ≥ 2`.  Together,
`log |ξ(2 + iT)| ≥ −(|T| + 2)` for `|T| ≥ 2`: linear in the height, as the horizontal-edge
bound requires.
-/

open Complex ArithmeticFunction
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiEdgeDecomposition

namespace Soma.Holonics.RH.XiLowerBoundOnLineTwo

/-! ### The Möbius series inverts `ζ` -/

theorem norm_LSeries_moebius_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries (fun n => (moebius n : ℂ)) s‖ ≤ Real.pi ^ 2 / 6 := by
  have hs1 : 1 < s.re := by linarith
  have hsum : Summable fun n => ‖LSeries.term (fun n => (moebius n : ℂ)) s n‖ :=
    (LSeriesSummable_moebius_iff.mpr hs1).norm
  have hb : ∀ n : ℕ, ‖LSeries.term (fun n => (moebius n : ℂ)) s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · positivity
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      have hμ : ‖(moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast abs_moebius_le_one
      have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn hs
      rw [Real.rpow_two] at hpow
      have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      calc ‖(moebius n : ℂ)‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by gcongr
        _ ≤ 1 / (n : ℝ) ^ 2 := by gcongr
  calc ‖LSeries (fun n => (moebius n : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (fun n => (moebius n : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hb hsum (Real.summable_one_div_nat_pow.mpr one_lt_two)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

theorem norm_riemannZeta_ge {s : ℂ} (hs : 2 ≤ s.re) : 1 / 2 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by linarith
  have h := LSeries_zeta_mul_Lseries_moebius hs1
  rw [LSeries_zeta_eq_riemannZeta hs1] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_one] at hn
  have hμ := norm_LSeries_moebius_le hs
  have hπ : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h0 := norm_nonneg (riemannZeta s)
  have h1 := norm_nonneg (LSeries (fun n => (moebius n : ℂ)) s)
  nlinarith

/-! ### `|Γ(1 + iy)|² = πy / sinh(πy)` -/

theorem Gamma_one_add_mul_Gamma_one_sub {y : ℝ} (hy : 0 < y) :
    Gamma (1 + y * I) * Gamma (1 - y * I) =
      ((Real.pi * y / Real.sinh (Real.pi * y) : ℝ) : ℂ) := by
  have hI : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy.ne') I_ne_zero
  have h1 : Gamma (1 - y * I) = (-(y * I)) * Gamma (-(y * I)) := by
    have := Complex.Gamma_add_one (-(y * I)) (neg_ne_zero.mpr hI)
    rw [← this]
    congr 1
    ring
  have h2 : Gamma (1 + y * I) * Gamma (-(y * I)) = Real.pi / sin (Real.pi * (1 + y * I)) := by
    have := Complex.Gamma_mul_Gamma_one_sub (1 + y * I)
    rw [show (1 : ℂ) - (1 + y * I) = -(y * I) by ring] at this
    exact this
  have hsin : sin ((Real.pi : ℂ) * (1 + y * I)) = -((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I := by
    rw [show (Real.pi : ℂ) * (1 + y * I) = ((Real.pi * y : ℝ) : ℂ) * I + Real.pi by push_cast; ring,
      Complex.sin_antiperiodic (((Real.pi * y : ℝ) : ℂ) * I), Complex.sin_mul_I,
      ← Complex.ofReal_sinh]
    ring
  have hS0 : ((Real.sinh (Real.pi * y) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sinh_pos_iff.mpr (by positivity)).ne'
  calc Gamma (1 + y * I) * Gamma (1 - y * I)
      = (-(y * I)) * (Gamma (1 + y * I) * Gamma (-(y * I))) := by rw [h1]; ring
    _ = (-(y * I)) * (Real.pi / (-((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I)) := by rw [h2, hsin]
    _ = ((Real.pi * y / Real.sinh (Real.pi * y) : ℝ) : ℂ) := by
        push_cast
        rw [← Complex.ofReal_mul, ← Complex.ofReal_sinh]
        field_simp [hS0, I_ne_zero]
        push_cast
        ring

theorem normSq_Gamma_one_add {y : ℝ} (hy : 0 < y) :
    ‖Gamma (1 + y * I)‖ ^ 2 = Real.pi * y / Real.sinh (Real.pi * y) := by
  have hconj : Gamma (1 - y * I) = (starRingEnd ℂ) (Gamma (1 + y * I)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have h := Gamma_one_add_mul_Gamma_one_sub hy
  rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem norm_Gamma_one_add_ge {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (-(Real.pi * y) / 2) ≤ ‖Gamma (1 + y * I)‖ := by
  have hy0 : 0 < y := by linarith
  have hsq := normSq_Gamma_one_add hy0
  have hsinh : Real.sinh (Real.pi * y) ≤ Real.exp (Real.pi * y) / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(Real.pi * y))
    linarith
  have hspos : 0 < Real.sinh (Real.pi * y) := Real.sinh_pos_iff.mpr (by positivity)
  have hlow : Real.exp (-(Real.pi * y)) ≤ ‖Gamma (1 + y * I)‖ ^ 2 := by
    rw [hsq, le_div_iff₀ hspos]
    calc Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y)
        ≤ Real.exp (-(Real.pi * y)) * (Real.exp (Real.pi * y) / 2) := by gcongr
      _ = 1 / 2 := by rw [← mul_div_assoc, ← Real.exp_add]; simp
      _ ≤ Real.pi * y := by nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(Real.pi * y) / 2) ^ 2 = Real.exp (-(Real.pi * y)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← h2] at hlow
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).mp hlow

theorem norm_Gamma_one_add_ge_abs {y : ℝ} (hy : 1 ≤ |y|) :
    Real.exp (-(Real.pi * |y|) / 2) ≤ ‖Gamma (1 + y * I)‖ := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h] at hy ⊢
    exact norm_Gamma_one_add_ge hy
  · rw [abs_of_neg h] at hy ⊢
    have hconj : Gamma (1 + y * I) = (starRingEnd ℂ) (Gamma (1 + (-y : ℝ) * I)) := by
      rw [← Complex.Gamma_conj]
      congr 1
      apply Complex.ext <;> simp
    rw [hconj, Complex.norm_conj]
    exact norm_Gamma_one_add_ge hy

/-! ### `Γ_ℝ` and `ξ` on the line `Re s = 2` -/

theorem norm_Gammaℝ_two_add (T : ℝ) :
    ‖Gammaℝ (2 + T * I)‖ = ‖Gamma (1 + (T / 2 : ℝ) * I)‖ / Real.pi := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-(2 + T * I) / 2).re = -1 := by simp
  have harg : (2 + T * I) / 2 = 1 + (T / 2 : ℝ) * I := by push_cast; ring
  rw [hre, Real.rpow_neg_one, harg]
  ring

theorem norm_Gammaℝ_two_add_ge {T : ℝ} (hT : 2 ≤ |T|) :
    Real.exp (-(Real.pi * |T|) / 4) / Real.pi ≤ ‖Gammaℝ (2 + T * I)‖ := by
  rw [norm_Gammaℝ_two_add]
  have hy : 1 ≤ |T / 2| := by rw [abs_div, abs_two]; linarith
  have h := norm_Gamma_one_add_ge_abs hy
  rw [abs_div, abs_two] at h
  have he : Real.exp (-(Real.pi * |T|) / 4) = Real.exp (-(Real.pi * (|T| / 2)) / 2) := by
    congr 1
    ring
  rw [he]
  gcongr

/-- **`ξ` is not small on the line `Re s = 2`.** -/
theorem log_norm_riemannXi_two_add_ge {T : ℝ} (hT : 2 ≤ |T|) :
    -(|T| + 2) ≤ Real.log ‖riemannXi (2 + T * I)‖ := by
  have hre : (2 + (T : ℂ) * I).re = 2 := by simp
  have hs2 : 1 < (2 + (T : ℂ) * I).re := by rw [hre]; norm_num
  rw [riemannXi_eq_mul_zeta hs2]
  have hζ := norm_riemannZeta_ge (s := 2 + T * I) (by rw [hre])
  have hΓ := norm_Gammaℝ_two_add_ge hT
  have hsn : 2 ≤ ‖(2 + (T : ℂ) * I)‖ := by
    have := Complex.abs_re_le_norm (2 + (T : ℂ) * I)
    rw [hre, abs_two] at this
    exact this
  have hs1n : 1 ≤ ‖(2 + (T : ℂ) * I) - 1‖ := by
    have := Complex.abs_re_le_norm ((2 + (T : ℂ) * I) - 1)
    have hre1 : ((2 + (T : ℂ) * I) - 1).re = 1 := by simp; norm_num
    rw [hre1, abs_one] at this
    exact this
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hprod : Real.exp (-(Real.pi * |T|) / 4) / (2 * Real.pi) ≤
      ‖(1 / 2 : ℂ) * (2 + T * I) * ((2 + T * I) - 1) * Gammaℝ (2 + T * I) *
        riemannZeta (2 + T * I)‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hhalf]
    calc Real.exp (-(Real.pi * |T|) / 4) / (2 * Real.pi)
        = 1 / 2 * 2 * 1 * (Real.exp (-(Real.pi * |T|) / 4) / Real.pi) * (1 / 2) := by
          field_simp
      _ ≤ 1 / 2 * ‖(2 + (T : ℂ) * I)‖ * ‖(2 + (T : ℂ) * I) - 1‖ * ‖Gammaℝ (2 + T * I)‖ *
          ‖riemannZeta (2 + T * I)‖ := by gcongr
  have hlog : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by gcongr
    norm_num at h3
    rw [h2]
    nlinarith [Real.pi_lt_d2]
  have hπ4 : Real.pi * |T| / 4 ≤ |T| := by nlinarith [Real.pi_lt_d2, abs_nonneg T]
  calc -(|T| + 2) ≤ Real.log (Real.exp (-(Real.pi * |T|) / 4) / (2 * Real.pi)) := by
        rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp]
        linarith
    _ ≤ Real.log ‖(1 / 2 : ℂ) * (2 + T * I) * ((2 + T * I) - 1) * Gammaℝ (2 + T * I) *
          riemannZeta (2 + T * I)‖ := Real.log_le_log (by positivity) hprod

end Soma.Holonics.RH.XiLowerBoundOnLineTwo
