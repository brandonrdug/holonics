import Mathlib
import ElementaryHolonics.RH.FlowedGamma
import ElementaryHolonics.RH.GammaPhase

/-!
# RT3 (iii-a): the transform continued, and the flowed Gamma factor on every vertical line

The single-event transform `T(s) = ∫ e^{(s − ½)u} φ(u) du` converges on `Re s > −2` and equals
`γ(s) = ½ (s − 1) π^{−s/2} Γ(s/2 + 1)` there (analytic continuation from `Re s > 1`). Hence the
flowed Gamma factor has the representation

`Γ_t(w) = (4πt)^{−1/2} ∫ e^{(c + iy − w)²/(4t)} γ(c + iy) dy`  for every real `c > −2`,

by the complex-shifted Gaussian pair `e^{−t(u−a)²} = (4πt)^{−1/2} ∫ e^{−y²/(4t)} e^{iy(u−a)} dy`
and Fubini: the contour may be placed through the saddle without a Cauchy argument.
-/

noncomputable section

namespace Soma.Holonics.RH.FlowedGammaContour

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.FlowedExplicitFormula
open Soma.Holonics.RH.DescentComb
open Soma.Holonics.RH.FlowedGamma

/-! ## The profile's left decay -/

theorem abs_φ_le_of_nonpos {v : ℝ} (hv : v ≤ 0) : |φ v| ≤ Mφ * Real.exp (5 / 2 * v) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  unfold φ
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hpoly : |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)| ≤
      2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v) := by
    calc |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)|
        ≤ |2 * π ^ 2 * Real.exp (4 * v)| + |3 * π * Real.exp (2 * v)| := abs_sub _ _
      _ = 2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v) := by
          rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hE : Real.exp (-π * Real.exp (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.exp_pos (2 * v), Real.pi_pos]
  have h4 : Real.exp (4 * v) ≤ Real.exp (2 * v) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (v / 2) * |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)| *
        Real.exp (-π * Real.exp (2 * v))
      ≤ Real.exp (v / 2) * (2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v)) * 1 := by
        gcongr
    _ ≤ Real.exp (v / 2) * (2 * π ^ 2 * Real.exp (2 * v) + 3 * π * Real.exp (2 * v)) * 1 := by
        gcongr
    _ = Mφ * (Real.exp (v / 2) * Real.exp (2 * v)) := by
        unfold Mφ
        ring
    _ = Mφ * Real.exp (5 / 2 * v) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-! ## The single event on `Re s > −2` -/

theorem norm_lapTerm_one_eq (s : ℂ) (u : ℝ) :
    ‖lapTerm (-1) s 1 u‖ = Real.exp ((s.re - 1 / 2) * u) * |φ u| := by
  rw [norm_lapTerm_eq, ← abs_of_pos (Real.exp_pos (u / 2)), ← abs_mul, event_eq one_ne_zero]
  simp

/-- **The exponential majorant of the single event** on `−2 + δ ≤ Re s ≤ ρ`. -/
theorem norm_lapTerm_one_le {δ ρ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs1 : -2 + δ ≤ s.re) (hs2 : s.re ≤ ρ)
    (u : ℝ) :
    ‖lapTerm (-1) s 1 u‖ ≤ Mφ * Real.exp ((|ρ| + δ + 2) ^ 2 / 4) * Real.exp (-δ * |u|) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  rw [norm_lapTerm_one_eq]
  set c : ℝ := |ρ| + δ + 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hK1 : (1 : ℝ) ≤ Real.exp (c ^ 2 / 4) := Real.one_le_exp (by positivity)
  rcases le_or_gt u 0 with hu | hu
  · rw [abs_of_nonpos hu]
    calc Real.exp ((s.re - 1 / 2) * u) * |φ u|
        ≤ Real.exp ((s.re - 1 / 2) * u) * (Mφ * Real.exp (5 / 2 * u)) := by
          gcongr
          exact abs_φ_le_of_nonpos hu
      _ = Mφ * Real.exp ((s.re + 2) * u) := by
          rw [← mul_assoc, mul_comm (Real.exp _) Mφ, mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ Mφ * Real.exp (δ * u) := by
          have := mul_le_mul_of_nonpos_right (show δ ≤ s.re + 2 by linarith) hu
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hM
      _ = Mφ * 1 * Real.exp (-δ * -u) := by ring_nf
      _ ≤ Mφ * Real.exp (c ^ 2 / 4) * Real.exp (-δ * -u) := by gcongr
  · rw [abs_of_pos hu]
    have hφ := abs_φ_le_of_nonneg hu.le
    calc Real.exp ((s.re - 1 / 2) * u) * |φ u|
        ≤ Real.exp ((s.re - 1 / 2) * u) * (Mφ * Real.exp (-u) * Real.exp (-(Real.exp (2 * u) / 2))) := by
          gcongr
      _ = Mφ * Real.exp ((s.re - 1 / 2) * u + -u + -(Real.exp (2 * u) / 2)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
      _ = Mφ * Real.exp ((s.re - 3 / 2 + δ) * u - Real.exp (2 * u) / 2) * Real.exp (-δ * u) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ Mφ * Real.exp (c ^ 2 / 4) * Real.exp (-δ * u) := by
          gcongr
          -- `(Re s − 3/2 + δ) u − e^{2u}/2 ≤ c²/4` since `e^{2u} ≥ 2u²`
          have h1 : (s.re - 3 / 2 + δ) * u ≤ c * u := by
            have : s.re - 3 / 2 + δ ≤ c := by
              rw [hc]
              linarith [le_abs_self ρ]
            exact mul_le_mul_of_nonneg_right this hu.le
          have h2 : 2 * u ^ 2 ≤ Real.exp (2 * u) := by
            have := Real.pow_div_factorial_le_exp (2 * u) (by linarith) 2
            norm_num [Nat.factorial] at this
            nlinarith
          nlinarith [sq_nonneg (c - 2 * u)]

theorem integrable_exp_neg_mul_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => Real.exp (-δ * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-δ * |u|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hδ 0).congr_fun (fun u hu => ?_) measurableSet_Iic
    rw [abs_of_nonpos hu]
    ring_nf
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-δ * |u|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hδ).congr_fun (fun u hu => ?_) measurableSet_Ioi
    rw [abs_of_pos hu]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact h1.union h2

theorem integrable_lapTerm_one' {s : ℂ} (hs : -2 < s.re) : Integrable (lapTerm (-1) s 1) := by
  set δ : ℝ := (s.re + 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ((integrable_exp_neg_mul_abs hδ0).const_mul
    (Mφ * Real.exp ((|s.re| + δ + 2) ^ 2 / 4))).mono'
    (continuous_lapTerm (-1) s 1).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  exact norm_lapTerm_one_le hδ0 (by rw [hδ]; linarith) le_rfl u

/-- The single-event transform. -/
def T (s : ℂ) : ℂ := ∫ u : ℝ, lapTerm (-1) s 1 u

/-- The Gamma factor in its pole-free form, `γ₁(s) = ½ (s − 1) π^{−s/2} Γ(s/2 + 1)`. -/
def γ₁ (s : ℂ) : ℂ := (1 / 2 : ℂ) * (s - 1) * ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))

theorem γ₁_eq_γ {s : ℂ} (hs : s ≠ 0) : γ₁ s = γ s := by
  unfold γ₁ γ
  have h2 : s / 2 ≠ 0 := by
    intro h
    apply hs
    have : s = 2 * (s / 2) := by ring
    rw [this, h, mul_zero]
  rw [Complex.Gamma_add_one (s / 2) h2]
  ring

theorem T_eq_γ₁_of_one_lt {s : ℂ} (hs : 1 < s.re) : T s = γ₁ s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [γ₁_eq_γ hs0]
  exact integral_lapTerm_one hs

theorem hasDerivAt_lapTerm_one (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => lapTerm (-1) z 1 u) ((u : ℂ) * lapTerm (-1) s 1 u) s := by
  unfold lapTerm
  have h : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (u : ℂ)) ((u : ℂ)) s := by
    have := ((hasDerivAt_id' s).sub_const (1 / 2 : ℂ)).mul_const (u : ℂ)
    simpa using this
  have := (h.cexp).mul_const ((Real.exp (u / 2) * Ψterm' (-1) 1 (Real.exp (2 * u)) : ℝ) : ℂ)
  refine this.congr_deriv ?_
  ring

theorem abs_le_exp_half {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : |u| ≤ (2 / δ) * Real.exp (δ / 2 * |u|) := by
  have h := Real.add_one_le_exp (δ / 2 * |u|)
  have : δ / 2 * |u| ≤ Real.exp (δ / 2 * |u|) := by linarith
  calc |u| = (2 / δ) * (δ / 2 * |u|) := by field_simp
    _ ≤ (2 / δ) * Real.exp (δ / 2 * |u|) := by gcongr

/-- **The transform is differentiable on `Re s > −2`.** -/
theorem hasDerivAt_T {s₀ : ℂ} (hs₀ : -2 < s₀.re) :
    HasDerivAt T (∫ u : ℝ, (u : ℂ) * lapTerm (-1) s₀ 1 u) s₀ := by
  set δ : ℝ := (s₀.re + 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ : ℝ := s₀.re + δ with hρ
  set K : ℝ := (2 / δ) * (Mφ * Real.exp ((|ρ| + δ + 2) ^ 2 / 4)) with hK
  have hball : ∀ z ∈ Metric.ball s₀ δ, -2 + δ ≤ z.re ∧ z.re ≤ ρ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - s₀)
    rw [Complex.sub_re] at h
    have := abs_lt.mp (lt_of_le_of_lt h hz)
    constructor
    · rw [hδ] at this ⊢
      linarith [this.1]
    · rw [hρ]
      linarith [this.2]
  have hbound : Integrable (fun u : ℝ => K * Real.exp (-(δ / 2) * |u|)) :=
    (integrable_exp_neg_mul_abs (by positivity : (0 : ℝ) < δ / 2)).const_mul K
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z u => lapTerm (-1) z 1 u) (F' := fun z u => (u : ℂ) * lapTerm (-1) z 1 u) (x₀ := s₀)
    (bound := fun u => K * Real.exp (-(δ / 2) * |u|)) (s := Metric.ball s₀ δ)
    (Metric.ball_mem_nhds s₀ hδ0)
    (Eventually.of_forall fun z => (continuous_lapTerm (-1) z 1).aestronglyMeasurable)
    (integrable_lapTerm_one' hs₀)
    (Complex.continuous_ofReal.mul (continuous_lapTerm (-1) s₀ 1)).aestronglyMeasurable
    (Eventually.of_forall fun u z hz => ?_) hbound
    (Eventually.of_forall fun u z _ => hasDerivAt_lapTerm_one u z)
  · exact h.2
  · obtain ⟨hz1, hz2⟩ := hball z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |u| * ‖lapTerm (-1) z 1 u‖
        ≤ ((2 / δ) * Real.exp (δ / 2 * |u|)) *
            (Mφ * Real.exp ((|ρ| + δ + 2) ^ 2 / 4) * Real.exp (-δ * |u|)) := by
          gcongr
          · exact abs_le_exp_half hδ0 u
          · exact norm_lapTerm_one_le hδ0 hz1 hz2 u
      _ = K * Real.exp (-(δ / 2) * |u|) := by
          rw [hK]
          have : Real.exp (δ / 2 * |u|) * Real.exp (-δ * |u|) = Real.exp (-(δ / 2) * |u|) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc (2 / δ) * Real.exp (δ / 2 * |u|) *
                (Mφ * Real.exp ((|ρ| + δ + 2) ^ 2 / 4) * Real.exp (-δ * |u|))
              = (2 / δ) * (Mφ * Real.exp ((|ρ| + δ + 2) ^ 2 / 4)) *
                  (Real.exp (δ / 2 * |u|) * Real.exp (-δ * |u|)) := by ring
            _ = _ := by rw [this]

theorem isOpen_halfPlane (r : ℝ) : IsOpen {s : ℂ | r < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- `γ₁` is differentiable on `Re s > −2`. -/
theorem differentiableAt_γ₁ {s : ℂ} (hs : -2 < s.re) : DifferentiableAt ℂ γ₁ s := by
  unfold γ₁
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2 + 1)) s := by
    apply DifferentiableAt.comp
    · apply Complex.differentiableAt_Gamma
      intro m h
      have hre : (s / 2 + 1).re = s.re / 2 + 1 := by simp
      have hm : ((-(m : ℂ)) : ℂ).re = -(m : ℝ) := by simp
      rw [h, hm] at hre
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · fun_prop
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    exact Or.inl hπ
  exact ((differentiableAt_const _).mul (by fun_prop)).mul (hcpow.mul hΓ)

/-- **`T = γ₁` on `Re s > −2`**, by analytic continuation from `Re s > 1`. -/
theorem T_eq_γ₁ {s : ℂ} (hs : -2 < s.re) : T s = γ₁ s := by
  have hU : IsOpen {z : ℂ | -2 < z.re} := isOpen_halfPlane (-2)
  have hconn : IsPreconnected {z : ℂ | -2 < z.re} := (convex_halfSpace_re_gt (-2)).isPreconnected
  have hT : AnalyticOnNhd ℂ T {z : ℂ | -2 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (hasDerivAt_T hz).differentiableAt.differentiableWithinAt
  have hγ : AnalyticOnNhd ℂ γ₁ {z : ℂ | -2 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_γ₁ hz).differentiableWithinAt
  have hev : T =ᶠ[𝓝 (2 : ℂ)] γ₁ := by
    filter_upwards [(isOpen_halfPlane 1).mem_nhds (by simp : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact T_eq_γ₁_of_one_lt hz
  exact (hT.eqOn_of_preconnected_of_eventuallyEq hγ hconn (by simp) hev) hs

/-! ## The flowed Gamma factor on every vertical line -/

/-- The complex-shifted Gaussian pair:
`∫ e^{−y²/(4t)} e^{i y (u − a)} dy = √(4πt) e^{−t(u − a)²}` for complex `a`. -/
theorem gaussian_fourier_shift {t : ℝ} (ht : 0 < t) (u : ℝ) (a : ℂ) :
    ∫ y : ℝ, Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * ((u : ℂ) - a)) * y) =
      (√(4 * π * t) : ℝ) * Complex.exp (-(t : ℂ) * ((u : ℂ) - a) ^ 2) := by
  have hb : (-(1 / (4 * t) : ℂ)).re < 0 := by
    simp
    positivity
  have h := integral_cexp_quadratic hb (Complex.I * ((u : ℂ) - a)) 0
  simp only [add_zero, zero_sub] at h
  rw [h]
  have hI : (Complex.I * ((u : ℂ) - a)) ^ 2 / (4 * -(1 / (4 * t) : ℂ)) = (t : ℂ) * ((u : ℂ) - a) ^ 2 := by
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

/-- **The flowed Gamma factor on the vertical line `Re z = c`**, any real `c > −2`:
`Γ_t(w) = (4πt)^{−1/2} ∫ e^{(c + iy − w)²/(4t)} γ(c + iy) dy`. -/
theorem Γt_eq_contour {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : -2 < c) (w : ℂ) :
    Γt t w = ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      ∫ y : ℝ, Complex.exp (((c : ℂ) + Complex.I * y - w) ^ 2 / (4 * t)) * γ₁ (c + Complex.I * y) := by
  have hs : 0 < √(4 * π * t) := sqrt_four_pi_t_pos ht
  have hsC : ((√(4 * π * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set a : ℂ := (w - c) / (2 * t) with ha
  have hlap : ∀ (y : ℝ) (u : ℝ), lapTerm (-1) ((c : ℂ) + Complex.I * y) 1 u =
      Complex.exp ((Complex.I * y) * u) * lapTerm (-1) (c : ℂ) 1 u := by
    intro y u
    unfold lapTerm
    rw [show ((c : ℂ) + Complex.I * y - 1 / 2) * (u : ℂ) =
      (Complex.I * y) * u + ((c : ℂ) - 1 / 2) * u by ring, Complex.exp_add]
    ring
  -- the integrand on the product
  set F : ℝ → ℝ → ℂ := fun u y =>
    Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * (-a)) * y) *
      (Complex.exp ((Complex.I * y) * u) * lapTerm (-1) (c : ℂ) 1 u) with hF
  -- the flowed term as the y-integral of F
  have hpt : ∀ u : ℝ, flowedTerm t w 1 u =
      Complex.exp ((w - c) ^ 2 / (4 * t)) * (((√(4 * π * t) : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, F u y) := by
    intro u
    have h := gaussian_fourier_shift ht u a
    have hsplit : ∫ y : ℝ, F u y =
        (∫ y : ℝ, Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * ((u : ℂ) - a)) * y)) *
          lapTerm (-1) (c : ℂ) 1 u := by
      rw [← MeasureTheory.integral_mul_const]
      congr 1
      funext y
      simp only [hF]
      rw [Complex.exp_add, Complex.exp_add]
      ring_nf
      rw [Complex.exp_add]
      ring
    rw [hsplit, h]
    -- `e^{−tu²} e^{(w−c)u} = e^{(w−c)²/(4t)} e^{−t(u−a)²}` and the `c`-term
    unfold flowedTerm lapTerm
    rw [show ((c : ℂ) - 1 / 2) * (u : ℂ) = (w - 1 / 2) * u - (w - c) * u by ring, Complex.exp_sub]
    have hexp : Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) =
        Complex.exp ((w - c) ^ 2 / (4 * t)) * Complex.exp (-(t : ℂ) * ((u : ℂ) - a) ^ 2) /
          Complex.exp ((w - c) * u) := by
      rw [eq_div_iff (Complex.exp_ne_zero _), ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [ha]
      field_simp
      ring
    rw [hexp]
    field_simp
    try ring
  -- integrability on the product
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hg : Integrable (fun y : ℝ =>
        Complex.exp (-(1 / (4 * t) : ℂ) * (y : ℂ) ^ 2 + (Complex.I * (-a)) * y)) := by
      have := integrable_cexp_quadratic (b := (1 / (4 * t) : ℂ)) (by simp; positivity)
        (Complex.I * (-a)) 0
      refine this.congr (Eventually.of_forall fun y => ?_)
      simp
    have hl : Integrable (fun u : ℝ => ‖lapTerm (-1) (c : ℂ) 1 u‖) :=
      (integrable_lapTerm_one' (by simpa using hc)).norm
    have hprod := hl.mul_prod hg.norm
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have hc2 : Continuous fun p : ℝ × ℝ => lapTerm (-1) (c : ℂ) 1 p.1 :=
        (continuous_lapTerm (-1) (c : ℂ) 1).comp continuous_fst
      rw [hF]
      show Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2 + (Complex.I * (-a)) * (p.2 : ℂ)) *
          (Complex.exp ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ)) * lapTerm (-1) (c : ℂ) 1 p.1)
      exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2 + (Complex.I * (-a)) * (p.2 : ℂ))).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ))).mul hc2)
    · show ‖F p.1 p.2‖ ≤ ‖lapTerm (-1) (c : ℂ) 1 p.1‖ *
        ‖Complex.exp (-(1 / (4 * t) : ℂ) * ((p.2 : ℝ) : ℂ) ^ 2 + (Complex.I * (-a)) * (p.2 : ℂ))‖
      simp only [hF]
      rw [norm_mul, norm_mul, Complex.norm_exp (Complex.I * (p.2 : ℂ) * (p.1 : ℂ))]
      have : ((Complex.I * (p.2 : ℂ)) * (p.1 : ℂ)).re = 0 := by simp
      rw [this, Real.exp_zero, one_mul, mul_comm]
  -- swap
  unfold Γt
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, integral_integral_swap hint]
  rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  show Complex.exp ((w - c) ^ 2 / (4 * t)) * ∫ u : ℝ, F u y = _
  simp only [hF]
  rw [MeasureTheory.integral_const_mul]
  have hT : ∫ u : ℝ, Complex.exp ((Complex.I * y) * u) * lapTerm (-1) (c : ℂ) 1 u =
      γ₁ ((c : ℂ) + Complex.I * y) := by
    rw [← T_eq_γ₁ (by simpa using hc)]
    unfold T
    apply integral_congr_ae
    exact Eventually.of_forall fun u => (hlap y u).symm
  rw [hT, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [ha]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end Soma.Holonics.RH.FlowedGammaContour
