module

public import HolonicsResearch.Zeta.ActualFiniteBeurlingMellinDomain
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
set_option autoImplicit false

/-!
Actual exterior Mellin compensation at a declared physical cut.

The private source passed the whole-module v149 native gate with three standard-axiom queries.
The sole native queue owns rechecks after import relocation. This is the
exterior component of the same actual finite Mobius receiver, not an
independent approximation family. N>0, a>=1/N and Re(s)<1 pay the actual
tail integral. There is no assumed signed cancellation, denominator
margin, simple zero, Mellin-value consumer or RH premise.

The full-ray integral value cannot be replaced by the interior value:
the omitted complex term is B_N*a^(s-1)/(1-s), including its phase.
-/

noncomputable section
namespace Holonics.Zeta.ActualBeurlingCompensatedTail

open Set MeasureTheory Complex
open Holonics.Zeta.ActualFiniteBeurlingReceiver

def tailMellinIntegrand (N : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * complexPhysicalResidual N x

lemma actual_tail_integrand {N : ℕ} (hN : 0 < N) {s : ℂ} {x : ℝ}
    (hx : 1 / (N : ℝ) ≤ x) :
    tailMellinIntegrand N s x =
      (harmonicMobius N : ℂ) * (x : ℂ) ^ (s - 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := (one_div_pos.mpr hNr).trans_le hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  rw [tailMellinIntegrand, complexPhysicalResidual,
    actual_nb_tail_pointwise hN hx, Complex.ofReal_div,
    show s - 2 = (s - 1) - 1 by ring,
    Complex.cpow_sub (s - 1) 1 hxC, Complex.cpow_one]
  simp only [div_eq_mul_inv]
  ring

theorem actual_tail_mellin_integrable {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : s.re < 1) {a : ℝ} (ha : 1 / (N : ℝ) ≤ a) :
    IntegrableOn (tailMellinIntegrand N s) (Ioi a) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := (one_div_pos.mpr hNr).trans_le ha
  have hexp : (s - 2).re < -1 := by
    change s.re - 2 < -1
    linarith
  have hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi a) :=
    integrableOn_Ioi_cpow_of_lt hexp ha0
  exact MeasureTheory.IntegrableOn.congr_fun
    (hi.const_mul (harmonicMobius N : ℂ))
    (fun x hx => (actual_tail_integrand hN (ha.trans hx.le)).symm) measurableSet_Ioi

/-- The actual omitted exterior is a complex phase-bearing term. -/
theorem actual_tail_mellin_integral {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : s.re < 1) {a : ℝ} (ha : 1 / (N : ℝ) ≤ a) :
    (∫ x : ℝ in Ioi a, tailMellinIntegrand N s x) =
      (harmonicMobius N : ℂ) * (a : ℂ) ^ (s - 1) / (1 - s) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := (one_div_pos.mpr hNr).trans_le ha
  have hexp : (s - 2).re < -1 := by
    change s.re - 2 < -1
    linarith
  calc
    _ = ∫ x : ℝ in Ioi a, (harmonicMobius N : ℂ) * (x : ℂ) ^ (s - 2) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx =>
        actual_tail_integrand hN (ha.trans hx.le)
    _ = (harmonicMobius N : ℂ) * (∫ x : ℝ in Ioi a, (x : ℂ) ^ (s - 2)) :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_Ioi_cpow_of_lt hexp ha0,
        show s - 2 + 1 = s - 1 by ring,
        show 1 - s = -(s - 1) by ring]
      simp only [div_eq_mul_inv, inv_neg]
      ring

/-- Exact tail magnitude; there is no universal lower denominator margin. -/
theorem actual_tail_mellin_norm {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : s.re < 1) {a : ℝ} (ha : 1 / (N : ℝ) ≤ a) :
    ‖∫ x : ℝ in Ioi a, tailMellinIntegrand N s x‖ =
      |harmonicMobius N| * a ^ (s.re - 1) / ‖1 - s‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := (one_div_pos.mpr hNr).trans_le ha
  rw [actual_tail_mellin_integral hN hs ha, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ha0]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.sub_re, Complex.one_re]

end Holonics.Zeta.ActualBeurlingCompensatedTail

#print axioms Holonics.Zeta.ActualBeurlingCompensatedTail.actual_tail_mellin_integrable
#print axioms Holonics.Zeta.ActualBeurlingCompensatedTail.actual_tail_mellin_integral
#print axioms Holonics.Zeta.ActualBeurlingCompensatedTail.actual_tail_mellin_norm
