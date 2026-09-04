import Mathlib
import ElementaryHolonics.RH.DescentComb
import ElementaryHolonics.RH.GammaStirling

/-!
# RT3 (i): the flowed Gamma factor, and every event is its shift

The flowed `n = 1` event `Γ_t(w) = ∫ e^{−t u²} e^{(w − ½) u} φ(u) du` is entire, and **every flowed
integer event is exactly a shift of it**:

`∫ flowedTerm t z n = e^{−t L²} e^{−z L} Γ_t(z + 2 t L)`, `L = log |n|`,

by the change of variables `u = v − L` under `e^{−t u²}` (the binding defect of `HeatFlowBinding`
in its exact form). On `Re w > 1`, `Γ_t` is the Gaussian convolution of the Gamma factor
`γ(s) = ¼ s(s − 1) π^{−s/2} Γ(s/2)` along the vertical line through `w`:

`Γ_t(w) = (4πt)^{−1/2} ∫ e^{−y²/(4t)} γ(w + iy) dy`.

So the asymptotics of every event reduce to the asymptotics of the one function `Γ_t`.
-/

noncomputable section

namespace Soma.Holonics.RH.FlowedGamma

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.DescentComb

/-! ## The events in the profile form -/

theorem flowedTerm_eq (t : ℝ) (z : ℂ) {n : ℤ} (hn : n ≠ 0) (u : ℝ) :
    flowedTerm t z n u =
      Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) * Complex.exp ((z - 1 / 2) * u) *
        ((((|(n : ℝ)|) ^ (-(1 / 2 : ℝ)) * φ (u + Real.log |(n : ℝ)|) : ℝ)) : ℂ) := by
  unfold flowedTerm lapTerm
  rw [event_eq hn]
  ring

theorem flowedTerm_one (t : ℝ) (w : ℂ) (u : ℝ) :
    flowedTerm t w 1 u =
      Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) * Complex.exp ((w - 1 / 2) * u) * ((φ u : ℝ) : ℂ) := by
  rw [flowedTerm_eq t w one_ne_zero u]
  simp

/-- **The flowed Gamma factor**: the flowed `n = 1` event. -/
def Γt (t : ℝ) (w : ℂ) : ℂ := ∫ u : ℝ, flowedTerm t w 1 u

/-! ## Every event is a shift of `Γ_t` -/

/-- **The exact shift identity**: `∫ flowedTerm t z n = e^{−tL²} e^{−zL} Γ_t(z + 2tL)`. -/
theorem integral_flowedTerm_eq_shift (t : ℝ) (z : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : ℝ, flowedTerm t z n u =
      Complex.exp (-(t : ℂ) * ((Real.log |(n : ℝ)| : ℝ) : ℂ) ^ 2) *
        Complex.exp (-z * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) *
        Γt t (z + 2 * t * ((Real.log |(n : ℝ)| : ℝ) : ℂ)) := by
  have hna : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  set L : ℝ := Real.log |(n : ℝ)| with hL
  unfold Γt
  rw [← MeasureTheory.integral_sub_right_eq_self (fun u => flowedTerm t z n u) L,
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext v
  rw [flowedTerm_eq t z hn, flowedTerm_one, sub_add_cancel]
  have hpow : (|(n : ℝ)|) ^ (-(1 / 2 : ℝ)) = Real.exp (L * (-(1 / 2))) := by
    rw [hL, Real.rpow_def_of_pos hna]
  rw [hpow, Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  have e1 : Complex.exp (-(t : ℂ) * ((v : ℂ) - (L : ℂ)) ^ 2) *
      Complex.exp ((z - 1 / 2) * ((v : ℂ) - (L : ℂ))) *
      (Complex.exp ((L : ℂ) * (-(1 / 2))) * ((φ v : ℝ) : ℂ)) =
      Complex.exp (-(t : ℂ) * ((v : ℂ) - (L : ℂ)) ^ 2 + (z - 1 / 2) * ((v : ℂ) - (L : ℂ)) +
        (L : ℂ) * (-(1 / 2))) * ((φ v : ℝ) : ℂ) := by
    rw [Complex.exp_add, Complex.exp_add]
    ring
  have e2 : Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2) * Complex.exp (-z * (L : ℂ)) *
      (Complex.exp (-(t : ℂ) * (v : ℂ) ^ 2) *
        Complex.exp ((z + 2 * (t : ℂ) * (L : ℂ) - 1 / 2) * (v : ℂ)) * ((φ v : ℝ) : ℂ)) =
      Complex.exp (-(t : ℂ) * (L : ℂ) ^ 2 + -z * (L : ℂ) + -(t : ℂ) * (v : ℂ) ^ 2 +
        (z + 2 * (t : ℂ) * (L : ℂ) - 1 / 2) * (v : ℂ)) * ((φ v : ℝ) : ℂ) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
    ring
  rw [e1, e2]
  congr 2
  ring

/-! ## The Gamma factor and the vertical-line representation -/

/-- The Gamma factor `γ(s) = ¼ s(s − 1) π^{−s/2} Γ(s/2)`, the transform of the single event. -/
def γ (s : ℂ) : ℂ := (1 / 4 : ℂ) * (s * (s - 1)) * ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))

theorem integral_lapTerm_one {s : ℂ} (hs : 1 < s.re) : ∫ u : ℝ, lapTerm (-1) s 1 u = γ s := by
  rw [integral_lapTerm (-1) hs one_ne_zero, termValue_neg_one_eq hs one_ne_zero]
  unfold γ
  simp

/-- The Gaussian Fourier pair: `e^{−t u²} = (4πt)^{−1/2} ∫ e^{−y²/(4t)} e^{i y u} dy`. -/
theorem gaussian_fourier {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ∫ y : ℝ, Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * u) * y) =
      (√(4 * π * t) : ℝ) * Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) := by
  have hb : (-(1 / (4 * t) : ℂ)).re < 0 := by
    simp
    positivity
  have h := integral_cexp_quadratic hb (Complex.I * u) 0
  simp only [add_zero, zero_sub] at h
  rw [h]
  have hI : (Complex.I * u) ^ 2 / (4 * -(1 / (4 * t) : ℂ)) = (t : ℂ) * (u : ℂ) ^ 2 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hI]
  have hpos : (0 : ℝ) < 4 * π * t := by positivity
  rw [show (π : ℂ) / -(-(1 / (4 * t) : ℂ)) = ((4 * π * t : ℝ) : ℂ) by
    push_cast
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp]
  rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hpos.le,
    Real.sqrt_eq_rpow]
  congr 1
  ring

theorem sqrt_four_pi_t_pos {t : ℝ} (ht : 0 < t) : 0 < √(4 * π * t) :=
  Real.sqrt_pos.mpr (by positivity)

/-- **The vertical-line representation**: for `Re w > 1`,
`Γ_t(w) = (4πt)^{−1/2} ∫ e^{−y²/(4t)} γ(w + iy) dy`. -/
theorem Γt_eq_gaussian_line {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 1 < w.re) :
    Γt t w = ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      ∫ y : ℝ, Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2) * γ (w + Complex.I * y) := by
  have hs : 0 < √(4 * π * t) := sqrt_four_pi_t_pos ht
  have hsC : ((√(4 * π * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hlap : ∀ (y : ℝ) (u : ℝ), lapTerm (-1) (w + Complex.I * y) 1 u =
      Complex.exp ((Complex.I * y) * u) * lapTerm (-1) w 1 u := by
    intro y u
    unfold lapTerm
    rw [show (w + Complex.I * y - 1 / 2) * (u : ℂ) = (Complex.I * y) * u + (w - 1 / 2) * u by ring,
      Complex.exp_add]
    ring
  -- the integrand on the product
  set F : ℝ → ℝ → ℂ := fun u y =>
    Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2) *
      (Complex.exp ((Complex.I * y) * u) * lapTerm (-1) w 1 u) with hF
  -- pointwise: the flowed term is the y-integral of F
  have hpt : ∀ u : ℝ, flowedTerm t w 1 u = ((√(4 * π * t) : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, F u y := by
    intro u
    unfold flowedTerm
    have h := gaussian_fourier ht u
    have hsplit : ∫ y : ℝ, F u y =
        (∫ y : ℝ, Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * u) * y)) *
          lapTerm (-1) w 1 u := by
      rw [← MeasureTheory.integral_mul_const]
      congr 1
      funext y
      simp only [hF]
      rw [Complex.exp_add]
      ring
    rw [hsplit, h]
    field_simp
  -- integrability on the product
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hg : Integrable (fun y : ℝ => Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2)) := by
      have := integrable_cexp_quadratic (b := (1 / (4 * t) : ℂ)) (by simp; positivity) 0 0
      refine this.congr (Eventually.of_forall fun y => ?_)
      simp
    have hl : Integrable (fun u : ℝ => ‖lapTerm (-1) w 1 u‖) := (integrable_lapTerm (-1) hw 1).norm
    have hprod := hl.mul_prod hg.norm
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have hc2 : Continuous fun p : ℝ × ℝ => lapTerm (-1) w 1 p.1 :=
        (continuous_lapTerm (-1) w 1).comp continuous_fst
      rw [hF]
      show Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2) *
          (Complex.exp ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ)) * lapTerm (-1) w 1 p.1)
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2)).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ))).mul hc2)
    · show ‖F p.1 p.2‖ ≤ ‖lapTerm (-1) w 1 p.1‖ *
        ‖Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2)‖
      simp only [hF]
      rw [norm_mul, norm_mul, Complex.norm_exp (Complex.I * (p.2 : ℂ) * (p.1 : ℂ))]
      have : ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero, one_mul, mul_comm]
  -- swap
  unfold Γt
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_integral_swap hint]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  show ∫ u : ℝ, F u y = _
  simp only [hF]
  rw [MeasureTheory.integral_const_mul, ← integral_lapTerm_one (by simp; exact hw)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun u => (hlap y u).symm

end Soma.Holonics.RH.FlowedGamma
