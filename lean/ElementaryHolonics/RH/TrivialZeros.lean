import ElementaryHolonics.RH.PairPopulation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The trivial zeros, and Mathlib's Riemann hypothesis is the pair population's emptiness

Left of `Re s = 0` the zeros of `ζ` are exactly `−2, −4, …`: at `s = −k` the value is a
Bernoulli number, nonzero for odd `k` since `ζ(2m) ≠ 0`, and for `s` not a nonpositive integer the
functional equation transports `ζ(1 − s) ≠ 0` to `ζ(s) ≠ 0`.  Hence every nontrivial zero of `ζ`
lies in the open strip, where it is a zero of `ξ`, and Mathlib's `RiemannHypothesis` is exactly
the `ξ`-form: every zero of `ξ` on the line, that is, the pair population empty.
-/

open Complex
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.WeilPositivity
open Soma.Holonics.RH.PairPopulation

namespace Soma.Holonics.RH.TrivialZeros

/-- Even Bernoulli numbers are nonzero, through `ζ(2k) ≠ 0`. -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) : ((bernoulli (2 * k) : ℚ) : ℂ) ≠ 0 := by
  intro h
  have hz := riemannZeta_two_mul_nat hk
  rw [h, mul_zero, zero_div] at hz
  have hre : (1 : ℝ) ≤ (2 * (k : ℂ)).re := by
    simp only [mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith
  exact riemannZeta_ne_zero_of_one_le_re hre hz

/-- `ζ(−k) ≠ 0` for odd `k`. -/
theorem riemannZeta_neg_odd_ne_zero {k : ℕ} (hk : Odd k) : riemannZeta (-(k : ℂ)) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli]
  obtain ⟨m, rfl⟩ := hk
  have hb := bernoulli_two_mul_ne_zero (k := m + 1) (by omega)
  have hidx : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
  rw [hidx]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hb) (Nat.cast_add_one_ne_zero _)

/-- **The trivial zeros.**  For `Re s ≤ 0`, `ζ(s) = 0` exactly when `s = −2(n + 1)`. -/
theorem riemannZeta_eq_zero_iff_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * (n + 1) := by
  constructor
  · intro h0
    by_cases hnat : ∃ n : ℕ, s = -n
    · obtain ⟨n, rfl⟩ := hnat
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨m, hm⟩ := heven
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exfalso
          rw [hm, hm0] at h0
          simp [riemannZeta_zero] at h0
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          refine ⟨m', ?_⟩
          rw [hm]
          push_cast
          ring
      · exfalso
        exact riemannZeta_neg_odd_ne_zero hodd h0
    · push Not at hnat
      exfalso
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hfe := riemannZeta_one_sub hnat hs1
      rw [h0, mul_zero] at hfe
      have hre : (1 : ℝ) ≤ (1 - s).re := by
        simp only [sub_re, one_re]
        linarith
      exact riemannZeta_ne_zero_of_one_le_re hre hfe
  · rintro ⟨n, rfl⟩
    exact riemannZeta_neg_two_mul_nat_add_one n

/-- **Mathlib's Riemann hypothesis is the `ξ`-form.** -/
theorem riemannHypothesis_iff_xi :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    exact riemannXi_zero_re_of_RH hRH hρ
  · intro hxi s hs htriv hs1
    rcases lt_or_ge s.re 1 with hlt | hge
    · rcases lt_or_ge 0 s.re with hpos | hnp
      · exact hxi s ((riemannXi_eq_zero_iff_riemannZeta_eq_zero hpos hlt).mpr hs)
      · exact absurd ((riemannZeta_eq_zero_iff_of_re_nonpos hnp).mp hs) htriv
    · exact absurd hs (riemannZeta_ne_zero_of_one_le_re hge)

/-- **The Riemann hypothesis is the emptiness of the pair population.** -/
theorem riemannHypothesis_iff_pairPopulation_eq_empty :
    RiemannHypothesis ↔ pairPopulation = ∅ := by
  rw [riemannHypothesis_iff_xi, pairPopulation_eq_empty_iff]

end Soma.Holonics.RH.TrivialZeros
