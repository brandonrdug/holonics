import Holonics.Objects.Ratio
import Holonics.Physics.PhaseCarrier
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# The check loop decides, the look settles, and the loss's covector splits into a source and a vortex

The record `research/records/2026-10-23_A_MOMENT_IS_A_LAP_AROUND_A_SINGULARITY_AND_LOOKING_AGAIN_CLOSES_THE_CHECK_LOOP_ON_ANOTHER_FACE.md`
(§§1, 2, 5 and 6; atlas `arith.check-loop-laps`, `phase.look-fixed-point`,
`phase.velocity-gradient-okubo-weiss`, `ratio.loss-singularity-flow`) reads looking again as one
more lap that reads the release on another ring's face, the look as a contracting direct and
reflected passage, a velocity gradient as the same passage, and the loss's covector as the velocity
of a singularity. #410 owes those laws; this file proves them.

[proved-standard; formal-checked] What is proved.

1. **The check loop decides** (`check_loop_decides`, `release_is_value`, `release_add`,
   `release_sub`, `release_mul`): for moduli `Q` whose least common multiple is at least the width
   of the size window, two values in the window with the same residue on every `q ∈ Q` are equal; so
   a release `r` in the window with `q(r) = T_q(q(a), q(b))` for every `q ∈ Q` is `T(a, b)` whenever
   `T(a, b)` lies in the window and `q(T(a, b)) = T_q(q(a), q(b))`, which holds for `+`, `−` and `·`
   (`face_add`, `face_sub`, `face_mul`).
2. **The look settles** (`look_sub`, `look_norm_sub_le`, `look_iterate`, `look_fixed_exists`,
   `look_fixed_unique`, `look_compose`): the look `L(h) = a h + b h̄ + c` is the phase carrier's
   direct and reflected passage plus a drive (`PhaseCarrier.modulatedCarrier`); it moves two readings
   apart by at most `ρ = |a| + |b|`, so for `ρ < 1` it has exactly one fixed point `h*` (Banach) and
   `|Lⁿh − h*| ≤ ρⁿ |h − h*|`; two looks compose to a look (`modulatedCarrier_compose`).
3. **The velocity gradient is a direct and reflected passage** (`gradient_split`, `gradient_det`,
   `okubo_weiss`): with `w = u + iv`, `δẇ = a δz + b δz̄` for `a = ∂_z w = ½(div + iω)` and
   `b = ∂_z̄ w = ½(s_n + i s_s)`; its determinant `|a|² − |b|²` is `u_x v_y − u_y v_x`
   (`modulatedCarrier_real_determinant`), and with no divergence it is `−W/4`,
   `W = s_n² + s_s² − ω²` (Okubo–Weiss).
4. **The loss's covector is a source and a vortex** (`log_norm_hasDerivAt`, `arg_branch_hasDerivAt`,
   `lap_circulation`): along any path `w(t) ≠ 0`, `Re(ẇ/w)` is the derivative of `ln|w|` (exact,
   the source part), and `Im(ẇ/w)` is locally the derivative of a branch of `arg w` (closed, the
   vortex part); round one lap of the singularity, `∮ dw/w = 2πi`, so the real part circulates `0`
   and the imaginary part `2π`. Every lift of the ratio `R = c / w` moves by `R⁻¹dR = −dw/w`
   (`loss_lift_deriv`, through `Objects/Ratio.lift_deriv_eq_logDeriv`), so these are the learning
   covector's two parts.

The computational object is the helical pair interaction: a release is read at a ring's pair
contact, looking again reads it at another ring's contact, and the look is the direct and reflected
passage through one contact. Of the winding guide's six general objects this touches faces and
placement (the residue faces and the release window) and the cell holonomy (the lap's circulation);
the helix, the pair, the tube and the tower thread stay attached.

Consumers: the atlas rows `arith.check-loop-laps`, `phase.look-fixed-point`,
`phase.velocity-gradient-okubo-weiss` and `ratio.loss-singularity-flow`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.CheckLoop

open Holonics.Physics.HolonicParametron (modulatedCarrier modulatedCarrier_compose
  modulatedCarrier_real_determinant)

/-! ## 1. The check loop decides -/

section Check

/-- [proved-standard; formal-checked] **The check loop decides:** two values in a window no wider
than the least common multiple of the moduli, with the same residue on every modulus, are equal. -/
theorem check_loop_decides (Q : Finset ℕ) (L r s : ℤ) (w : ℕ) (hw : w ≤ Q.lcm id)
    (hr : L ≤ r ∧ r < L + w) (hs : L ≤ s ∧ s < L + w)
    (h : ∀ q ∈ Q, (r : ZMod q) = (s : ZMod q)) : r = s := by
  have hdvd : ((Q.lcm id : ℕ) : ℤ) ∣ s - r := by
    rw [Int.natCast_dvd]
    exact Finset.lcm_dvd fun q hq =>
      Int.natCast_dvd.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub r s q).mp (h q hq))
  have hw' : (w : ℤ) ≤ ((Q.lcm id : ℕ) : ℤ) := by exact_mod_cast hw
  have habs : |s - r| < ((Q.lcm id : ℕ) : ℤ) := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/-- [proved-standard; formal-checked] The residue face of a sum is the sum of the faces. -/
theorem face_add (q : ℕ) (a b : ℤ) : ((a + b : ℤ) : ZMod q) = (a : ZMod q) + (b : ZMod q) :=
  Int.cast_add a b

/-- [proved-standard; formal-checked] The residue face of a difference is the difference of the
faces. -/
theorem face_sub (q : ℕ) (a b : ℤ) : ((a - b : ℤ) : ZMod q) = (a : ZMod q) - (b : ZMod q) :=
  Int.cast_sub a b

/-- [proved-standard; formal-checked] The residue face of a product is the product of the faces. -/
theorem face_mul (q : ℕ) (a b : ℤ) : ((a * b : ℤ) : ZMod q) = (a : ZMod q) * (b : ZMod q) :=
  Int.cast_mul a b

/-- [proved-standard; formal-checked] **A release that every face checks is the value:** if `T` has
the faces `T_q`, a release in the window whose residues are `T_q(q(a), q(b))` on every modulus is
`T(a, b)`. -/
theorem release_is_value (Q : Finset ℕ) (L : ℤ) (w : ℕ) (hw : w ≤ Q.lcm id)
    (T : ℤ → ℤ → ℤ) (Tq : ∀ q : ℕ, ZMod q → ZMod q → ZMod q)
    (hT : ∀ (q : ℕ) (a b : ℤ), ((T a b : ℤ) : ZMod q) = Tq q (a : ZMod q) (b : ZMod q))
    (a b r : ℤ) (hr : L ≤ r ∧ r < L + w) (hab : L ≤ T a b ∧ T a b < L + w)
    (h : ∀ q ∈ Q, (r : ZMod q) = Tq q (a : ZMod q) (b : ZMod q)) : r = T a b :=
  check_loop_decides Q L r (T a b) w hw hr hab fun q hq => (h q hq).trans (hT q a b).symm

/-- [proved-standard; formal-checked] The check loop releases a sum. -/
theorem release_add (Q : Finset ℕ) (L : ℤ) (w : ℕ) (hw : w ≤ Q.lcm id) (a b r : ℤ)
    (hr : L ≤ r ∧ r < L + w) (hab : L ≤ a + b ∧ a + b < L + w)
    (h : ∀ q ∈ Q, (r : ZMod q) = (a : ZMod q) + (b : ZMod q)) : r = a + b :=
  release_is_value Q L w hw (· + ·) (fun _ x y => x + y) face_add a b r hr hab h

/-- [proved-standard; formal-checked] The check loop releases a difference. -/
theorem release_sub (Q : Finset ℕ) (L : ℤ) (w : ℕ) (hw : w ≤ Q.lcm id) (a b r : ℤ)
    (hr : L ≤ r ∧ r < L + w) (hab : L ≤ a - b ∧ a - b < L + w)
    (h : ∀ q ∈ Q, (r : ZMod q) = (a : ZMod q) - (b : ZMod q)) : r = a - b :=
  release_is_value Q L w hw (· - ·) (fun _ x y => x - y) face_sub a b r hr hab h

/-- [proved-standard; formal-checked] The check loop releases a product. -/
theorem release_mul (Q : Finset ℕ) (L : ℤ) (w : ℕ) (hw : w ≤ Q.lcm id) (a b r : ℤ)
    (hr : L ≤ r ∧ r < L + w) (hab : L ≤ a * b ∧ a * b < L + w)
    (h : ∀ q ∈ Q, (r : ZMod q) = (a : ZMod q) * (b : ZMod q)) : r = a * b :=
  release_is_value Q L w hw (· * ·) (fun _ x y => x * y) face_mul a b r hr hab h

end Check

/-! ## 2. The look settles -/

section Look

variable (a b c : ℂ)

/-- [definition] The look: the phase carrier's direct and reflected passage plus a drive,
`L(h) = a h + b h̄ + c`. -/
def look (h : ℂ) : ℂ := modulatedCarrier a b h + c

/-- [proved-standard; formal-checked] The look moves a difference by its passage alone. -/
theorem look_sub (x y : ℂ) : look a b c x - look a b c y = modulatedCarrier a b (x - y) := by
  simp only [look, modulatedCarrier, star_sub]
  ring

/-- [proved-standard; formal-checked] The look moves two readings apart by at most
`ρ = |a| + |b|`. -/
theorem look_norm_sub_le (x y : ℂ) :
    ‖look a b c x - look a b c y‖ ≤ (‖a‖ + ‖b‖) * ‖x - y‖ := by
  rw [look_sub]
  calc ‖a * (x - y) + b * star (x - y)‖ ≤ ‖a * (x - y)‖ + ‖b * star (x - y)‖ := norm_add_le _ _
    _ = ‖a‖ * ‖x - y‖ + ‖b‖ * ‖x - y‖ := by rw [norm_mul, norm_mul, norm_star]
    _ = (‖a‖ + ‖b‖) * ‖x - y‖ := by ring

/-- [proved-standard; formal-checked] **Looking again settles geometrically:**
`|Lⁿh − h*| ≤ ρⁿ |h − h*|` at a fixed point `h*`. -/
theorem look_iterate {s : ℂ} (hs : look a b c s = s) (n : ℕ) (h : ℂ) :
    ‖(look a b c)^[n] h - s‖ ≤ (‖a‖ + ‖b‖) ^ n * ‖h - s‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖(look a b c)^[n + 1] h - s‖
        = ‖look a b c ((look a b c)^[n] h) - look a b c s‖ := by
          rw [Function.iterate_succ_apply', hs]
      _ ≤ (‖a‖ + ‖b‖) * ‖(look a b c)^[n] h - s‖ := look_norm_sub_le a b c _ _
      _ ≤ (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) ^ n * ‖h - s‖) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (‖a‖ + ‖b‖) ^ (n + 1) * ‖h - s‖ := by ring

/-- [proved-standard; formal-checked] **The look has a fixed point** when `ρ = |a| + |b| < 1`. -/
theorem look_fixed_exists (hρ : ‖a‖ + ‖b‖ < 1) : ∃ s, look a b c s = s := by
  have hK : ContractingWith (‖a‖ + ‖b‖).toNNReal (look a b c) :=
    ⟨Real.toNNReal_lt_one.mpr hρ, LipschitzWith.of_dist_le' fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact look_norm_sub_le a b c x y⟩
  exact ⟨ContractingWith.fixedPoint _ hK, hK.fixedPoint_isFixedPt⟩

/-- [proved-standard; formal-checked] **The fixed point is unique** when `ρ < 1`. -/
theorem look_fixed_unique (hρ : ‖a‖ + ‖b‖ < 1) {x y : ℂ} (hx : look a b c x = x)
    (hy : look a b c y = y) : x = y := by
  have h := look_norm_sub_le a b c x y
  rw [hx, hy] at h
  have hle : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y), norm_nonneg a, norm_nonneg b]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- [proved-standard; formal-checked] **Two looks compose to a look**, through
`modulatedCarrier_compose`. -/
theorem look_compose (a' b' c' h : ℂ) :
    look a b c (look a' b' c' h) =
      look (a * a' + b * star b') (a * b' + b * star a') (a * c' + b * star c' + c) h := by
  simp only [look, modulatedCarrier, star_add, star_mul, star_star]
  ring

end Look

/-! ## 3. The velocity gradient is a direct and reflected passage -/

section Gradient

variable (ux uy vx vy : ℝ)

/-- [definition] The direct part of a velocity gradient, `∂_z w = ½(div + iω)`. -/
noncomputable def directPart : ℂ := ⟨(ux + vy) / 2, (vx - uy) / 2⟩

/-- [definition] The reflected part of a velocity gradient, `∂_z̄ w = ½(s_n + i s_s)`. -/
noncomputable def reflectedPart : ℂ := ⟨(ux - vy) / 2, (vx + uy) / 2⟩

/-- [proved-standard; formal-checked] **The velocity gradient is a direct and reflected passage:**
`a δz + b δz̄ = (u_x δx + u_y δy) + i (v_x δx + v_y δy)`. -/
theorem gradient_split (δx δy : ℝ) :
    modulatedCarrier (directPart ux uy vx vy) (reflectedPart ux uy vx vy) ⟨δx, δy⟩ =
      ⟨ux * δx + uy * δy, vx * δx + vy * δy⟩ := by
  apply Complex.ext <;>
    simp [modulatedCarrier, directPart, reflectedPart, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- [proved-standard; formal-checked] **Its determinant** is `|a|² − |b|² = u_x v_y − u_y v_x`,
the phase carrier's real determinant. -/
theorem gradient_det :
    Complex.normSq (directPart ux uy vx vy) - Complex.normSq (reflectedPart ux uy vx vy) =
      ux * vy - uy * vx := by
  rw [← modulatedCarrier_real_determinant]
  simp only [directPart, reflectedPart]
  ring

/-- [proved-standard; formal-checked] **Okubo–Weiss:** with no divergence the determinant is
`−W/4`, `W = s_n² + s_s² − ω²`, `s_n = u_x − v_y`, `s_s = v_x + u_y`, `ω = v_x − u_y`. -/
theorem okubo_weiss (h : ux + vy = 0) :
    Complex.normSq (directPart ux uy vx vy) - Complex.normSq (reflectedPart ux uy vx vy) =
      -((ux - vy) ^ 2 + (vx + uy) ^ 2 - (vx - uy) ^ 2) / 4 := by
  rw [gradient_det]
  have hv : vy = -ux := by linarith
  rw [hv]
  ring

end Gradient

/-! ## 4. The loss's covector is a source and a vortex -/

section Covector

variable {γ : ℝ → ℂ} {γ' : ℂ} {t : ℝ}

/-- [proved-standard; formal-checked] **The real part is exact:** along a path `w(t) ≠ 0`,
`Re(ẇ/w)` is the derivative of `ln|w|`, the velocity of a source. -/
theorem log_norm_hasDerivAt (hγ : HasDerivAt γ γ' t) (h0 : γ t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖γ s‖) (γ' / γ t).re t := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane h0 with h | h
  · have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hγ.clog_real h)
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] at hd
    exact hd
  · have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hγ.fun_neg.clog_real h)
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.log_re, norm_neg,
      neg_div_neg_eq] at hd
    exact hd

/-- [proved-standard; formal-checked] **The imaginary part is closed:** along a path `w(t) ≠ 0`,
`Im(ẇ/w)` is locally the derivative of a branch of `arg w` (of `arg w` off the negative axis, of
`arg (−w)` off the positive one), the velocity of a vortex. -/
theorem arg_branch_hasDerivAt (hγ : HasDerivAt γ γ' t) (h0 : γ t ≠ 0) :
    HasDerivAt (fun s => Complex.arg (γ s)) (γ' / γ t).im t ∨
      HasDerivAt (fun s => Complex.arg (-γ s)) (γ' / γ t).im t := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane h0 with h | h
  · left
    have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hγ.clog_real h)
    simp only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] at hd
    exact hd
  · right
    have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hγ.fun_neg.clog_real h)
    simp only [Function.comp_def, Complex.imCLM_apply, Complex.log_im, neg_div_neg_eq] at hd
    exact hd

/-- [proved-standard; formal-checked] **One lap circulates `2π`:** round a circle about the
singularity, `∮ dw/w = 2πi`; its real part circulates `0` and its imaginary part `2π`, so the
vortex part is closed but not exact. -/
theorem lap_circulation (z₀ : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(z₀, R), (z - z₀)⁻¹) = 2 * Real.pi * Complex.I ∧
      (∮ z in C(z₀, R), (z - z₀)⁻¹).re = 0 ∧
      (∮ z in C(z₀, R), (z - z₀)⁻¹).im = 2 * Real.pi := by
  rw [circleIntegral.integral_sub_center_inv z₀ hR]
  refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- [proved-derived; formal-checked] **The join to the loss:** for a fixed target amplitude `c ≠ 0`
and a produced amplitude `w(t) ≠ 0`, every lift `ℓ` of the ratio `R = c / w` (`exp ∘ ℓ = R`) moves
by `ℓ' = R⁻¹ R' = −ẇ/w` (`Objects/Ratio.lift_deriv_eq_logDeriv`), so the loss's covector is the
source (`log_norm_hasDerivAt`) and the vortex (`arg_branch_hasDerivAt`) of the produced amplitude's
singularity, with the sign of descent. -/
theorem loss_lift_deriv {c : ℂ} (hc : c ≠ 0) {L : ℝ → ℂ}
    (hlift : ∀ s, Complex.exp (L s) = c / γ s) (hγ : HasDerivAt γ γ' t) (h0 : γ t ≠ 0)
    {ℓ' : ℂ} (hL : HasDerivAt L ℓ' t) : ℓ' = -(γ' / γ t) := by
  have hR : HasDerivAt (fun s => c / γ s) ((0 * γ t - c * γ') / γ t ^ 2) t :=
    (hasDerivAt_const (x := t) (c := c)).fun_div hγ h0
  rw [Holonics.Objects.Ratio.lift_deriv_eq_logDeriv hlift hL hR]
  field_simp
  ring

end Covector

end Holonics.Mathematics.CheckLoop
