import Holonics.Physics.Fluid.Body
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Fluid.RankineOval: a source and a sink of equal strength in a stream close the dividing streamline

[proved-standard; formal-checked] Sufficiency for the Rankine oval, the converse that `Physics/Fluid/Body` states
beside its necessity (`closed_streamline_net_zero`). Sources: the #410 box "Rankine oval sufficiency: zero net strength
in a uniform stream gives a closed dividing streamline (`Physics/Fluid/Body` proves necessity)"; the egg record
`research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md` §4 ("A body
is a globe"); the atlas rows `fluid.closed-body-net-zero`, whose limits read "sufficiency (the Rankine oval) open",
and `fluid.half-body-tube`, whose half-body (`Body.halfBodyStream`) this module mirrors for zero net strength.

[definition] A source `m > 0` at `−a`, a sink `−m` at `a` (`a > 0`) and a uniform stream `U > 0` along `x` have, in
the principal chart, the stream function

```text
ψ(z) = U Im z + (m/2π) (arg (z + a) − arg (z − a))                    (ovalStream)
```

the imaginary part of `F = U z + (m/2π)(log (z + a) − log (z − a))` (`ovalStream_eq_im`). Above the axis the bracket
is minus the angle `α(x, y) ∈ (0, π)` that the segment `[−a, a]` subtends at `x + iy` (`subtended`), and `α / y` is
the angle per height `∫_(−a)^(a) ds / ((x − s)² + y²)` (`anglePerHeight`). The half-length is
`L = √(a² + m a / (π U))` (`halfLength`); the height `Y(x)` (`height`) is the root of `α / y = 2πU/m` where one
exists and `0` elsewhere; the loop (`ovalLoop`) runs along `x + i Y(x)` from `L` to `−L` and back along the mirror.

What is proved.

1. **The angle as an integral** (§1). Above the axis `arg w = π/2 − arctan (Re w / Im w)`
   (`arg_eq_pi_div_two_sub_arctan`), so `ψ = U y − (m/2π) α` (`ovalStream_eq_subtended`) with
   `α = arctan ((x + a)/y) − arctan ((x − a)/y) = y ∫_(−a)^(a) ds / ((x − s)² + y²)`
   (`subtended_eq_mul_anglePerHeight`, by the fundamental theorem of calculus), and
   `ψ(x + iy) = y (U − (m/2π) α / y)` (`ovalStream_eq_mul`).
2. **The angle per height falls with height** (§2). It strictly decreases in `y > 0`
   (`anglePerHeight_strictAntiOn`), is continuous in `y` and in `x` (`continuousOn_anglePerHeight`,
   `continuous_anglePerHeight_station`), is below `π / y` (`anglePerHeight_lt_pi_div`), is at least `π / (4y)` over
   the segment for `y ≤ a` (`pi_div_four_le_subtended`), and beyond the segment stays below its axis value
   `2a / (x² − a²)` (`integral_one_div_sq`, `anglePerHeight_lt_axis`) and above `(1 − y²/(|x| − a)²)` times it
   (`axis_le_anglePerHeight`).
3. **One height at each station** (§3). Some height has `α / y = 2πU/m` if and only if `|x| < L`
   (`exists_root_iff`): for `|x| < L` one and only one `y > 0` has `ψ(x + iy) = 0` (`station_existsUnique`), and for
   `|x| ≥ L` none has (`station_none`). The height is read off `α / y` (`height_spec`), is positive if and only if
   `|x| < L` (`height_pos_iff`), and the upper branch lies below the half-body's half-width, `y < m/(2U)`
   (`oval_width`, `height_lt_width`), because `α < π`.
4. **The height closes at the stagnation points** (§4). `Y` is continuous on the whole axis (`continuous_height`),
   so on `(−L, L)`, and tends to `0` at `±L` (`tendsto_height_ends`). The axis beyond the segment lies on `ψ = 0`,
   both arguments `0` beyond `a` and both `π` beyond `−a` (`ovalStream_axis`), and the velocity `dF/dz`
   (`ovalVelocity`, `hasDerivAt_potential`) vanishes at `±L` (`ovalVelocity_ends`). `ψ` is odd under reflection in
   the axis (`ovalStream_conj`), so `x + i Y(x)` and its mirror lie on `ψ = 0` for `|x| ≤ L` (`ovalStream_station`).
5. **The oval is a closed curve** (§5). The loop `γ : C(unitInterval, ℂ)` is closed (`ovalLoop_closed`), lies on
   `ψ = 0` (`ovalLoop_stream`), starts at `L` and passes `−L` halfway (`ovalLoop_zero`, `ovalLoop_half`), runs along
   `x + i Y(x)` on its upper half and along the mirror on its lower half (`ovalLoop_eq_upper`,
   `ovalLoop_eq_conj_upper`, `ovalLoop_symm`), is injective on `[0, 1)` (`ovalLoop_injOn`), avoids the segment
   `[−a, a]` (`ovalLoop_avoids`) and stays in `|x| ≤ L`, `|y| = Y(x) < m/(2U)` (`ovalLoop_bounds`);
   `rankine_oval_closes` collects these.
6. **The join to necessity** (§6). Along the oval the path lifting of each ratio `(γ(t) − s : 1)` (`Body.siteLift`)
   is the principal logarithm over the upper half and its conjugate advanced by `2πi` over the lower half
   (`siteLift_ovalLoop`), so the oval winds once around each point of the segment (`ovalLoop_winding`), and the
   stream function read through these lifts is `0` along it (`ovalLoop_potential_im`); `Body.closed_streamline_net_zero`
   applies and reads back `m + (−m) = 0` (`rankine_oval_net_zero`).

What is not claimed. Only the symmetric pair on the stream's axis with the source upstream is treated: a general
zero-sum distribution (several singularities, sites off the axis, circulation) and the egg's uneven fore–aft
distribution are not. The oval's half-width at `x = 0` is bounded (`< m/(2U)`), not computed, and the height is shown
continuous, not differentiable. The level set `ψ = 0` is described station by station above the axis
(`station_existsUnique`, `station_none`) and by reflection below it, not as one set equation; the region the oval
bounds (a Jordan interior) and clauses (1) and (2) of relative completeness are not stated (`Body`'s closing note).

The computational object is the helical pair interaction: here a source–sink pair's lifted logarithms read against a
stream. Each lift advances by one turn around the oval (`ovalLoop_winding`); the pair's two windings enter `ψ` with
opposite strengths and cancel, so `ψ` returns to its value and the streamline closes, where the half-body's single
winding leaves a tube. Of the winding guide's six general objects this touches the helix (each lift is a helix over
its site, the carry `2πi` added once round), the pair (the source and the sink, whose lifts are read together) and
the cell holonomy (the jump `Σ m_k n_k = m − m` read on the closed loop); faces and placement, the tube (the
half-body of `Body`) and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Fluid.RankineOval

open Complex Set
open Holonics.Physics.Fluid.Body

/-! ## 1. The angle the segment subtends, as an arctangent and as an integral -/

/-- [definition] The stream function of a source `m` at `−a`, a sink `−m` at `a` and a stream `U`. -/
def ovalStream (U m a : ℝ) (z : ℂ) : ℝ :=
  U * z.im + m / (2 * Real.pi) * (Complex.arg (z + a) - Complex.arg (z - a))

/-- [definition] The angle `α(x, y)` that the segment `[−a, a]` subtends at `x + iy`. -/
def subtended (a x y : ℝ) : ℝ := Real.arctan ((x + a) / y) - Real.arctan ((x - a) / y)

/-- [definition] The angle per height, `∫_(−a)^(a) ds / ((x − s)² + y²)`. -/
def anglePerHeight (a x y : ℝ) : ℝ := ∫ s in (-a)..a, 1 / ((x - s) ^ 2 + y ^ 2)

/-- [proved-standard; formal-checked] Above the axis, `arg w = π/2 − arctan (Re w / Im w)`. -/
theorem arg_eq_pi_div_two_sub_arctan {w : ℂ} (h : 0 < w.im) :
    Complex.arg w = Real.pi / 2 - Real.arctan (w.re / w.im) := by
  have h0 : 0 < Complex.arg w := arg_pos_of_im_pos h
  have h1 : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr h.ne')
  have htan : Real.tan (Real.pi / 2 - Complex.arg w) = w.re / w.im := by
    rw [Real.tan_pi_div_two_sub, Complex.tan_arg, inv_div]
  have := Real.arctan_eq_of_tan_eq htan ⟨by linarith, by linarith⟩
  linarith

/-- [proved-standard; formal-checked] Above the axis, `arg (z + a) − arg (z − a) = −α`. -/
theorem arg_sub_arg_eq_neg_subtended (a : ℝ) {z : ℂ} (h : 0 < z.im) :
    Complex.arg (z + a) - Complex.arg (z - a) = -subtended a z.re z.im := by
  have hp : 0 < (z + a).im := by simpa using h
  have hm : 0 < (z - a).im := by simpa using h
  rw [arg_eq_pi_div_two_sub_arctan hp, arg_eq_pi_div_two_sub_arctan hm, subtended]
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero, sub_re, sub_im, sub_zero]
  ring

/-- [proved-standard; formal-checked] Above the axis, `ψ = U y − (m/2π) α(x, y)`. -/
theorem ovalStream_eq_subtended (U m a : ℝ) {z : ℂ} (h : 0 < z.im) :
    ovalStream U m a z = U * z.im - m / (2 * Real.pi) * subtended a z.re z.im := by
  rw [ovalStream, arg_sub_arg_eq_neg_subtended a h]
  ring

/-- [proved-standard; formal-checked] **The angle as an integral**: `α = y ∫_(−a)^(a) ds / ((x − s)² + y²)`. -/
theorem subtended_eq_mul_anglePerHeight (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    subtended a x y = y * anglePerHeight a x y := by
  have hderiv : ∀ s ∈ uIcc (-a) a, HasDerivAt (fun s => Real.arctan ((s - x) / y))
      (y / ((x - s) ^ 2 + y ^ 2)) s := by
    intro s _
    have h : HasDerivAt (fun s => Real.arctan ((s - x) / y))
        (1 / (1 + ((s - x) / y) ^ 2) * (1 / y)) s :=
      (((hasDerivAt_id' s).sub_const x).div_const y).arctan
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous fun s : ℝ => y / ((x - s) ^ 2 + y ^ 2) :=
    continuous_const.div (by fun_prop) fun s => by positivity
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  rw [anglePerHeight, ← intervalIntegral.integral_const_mul]
  simp only [mul_one_div]
  rw [hint, subtended]
  have e1 : (-a - x) / y = -((x + a) / y) := by ring
  have e2 : (a - x) / y = -((x - a) / y) := by ring
  rw [e1, e2, Real.arctan_neg, Real.arctan_neg]
  ring

/-- [proved-standard; formal-checked] Above the axis the angle per height is `α / y`. -/
theorem anglePerHeight_eq_div (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    anglePerHeight a x y = subtended a x y / y := by
  rw [subtended_eq_mul_anglePerHeight a x hy]
  field_simp

/-! ## 2. The angle per height falls with height -/

/-- [proved-standard; formal-checked] **The angle per height strictly decreases with the height.** -/
theorem anglePerHeight_strictAntiOn (x : ℝ) {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (anglePerHeight a x) (Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ h12
  rw [mem_Ioi] at hy₁ hy₂
  have hsq : y₁ ^ 2 < y₂ ^ 2 := by nlinarith
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
    ?_ ?_ ?_ ⟨a, ⟨by linarith, le_rfl⟩, ?_⟩
  · exact (continuous_const.div (by fun_prop) fun s => by positivity).continuousOn
  · exact (continuous_const.div (by fun_prop) fun s => by positivity).continuousOn
  · intro s _
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- [proved-standard; formal-checked] The angle per height is continuous in the height. -/
theorem continuousOn_anglePerHeight (a x : ℝ) : ContinuousOn (anglePerHeight a x) (Ioi 0) := by
  have hne : ∀ y ∈ Ioi (0 : ℝ), y ≠ 0 := fun y hy => (mem_Ioi.mp hy).ne'
  have h : ContinuousOn (fun y => subtended a x y / y) (Ioi 0) := by
    refine ContinuousOn.div ?_ continuousOn_id hne
    exact (Real.continuous_arctan.comp_continuousOn (continuousOn_const.div continuousOn_id hne)).sub
      (Real.continuous_arctan.comp_continuousOn (continuousOn_const.div continuousOn_id hne))
  exact h.congr fun y hy => anglePerHeight_eq_div a x (mem_Ioi.mp hy)

/-- [proved-standard; formal-checked] At a fixed height the angle per height is continuous along the stream. -/
theorem continuous_anglePerHeight_station (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous fun x => anglePerHeight a x y := by
  have h : (fun x => anglePerHeight a x y) = fun x => subtended a x y / y :=
    funext fun x => anglePerHeight_eq_div a x hy
  rw [h]
  unfold subtended
  fun_prop

/-- [proved-standard; formal-checked] Above the axis the segment subtends a positive angle. -/
theorem subtended_pos (x : ℝ) {a y : ℝ} (ha : 0 < a) (hy : 0 < y) : 0 < subtended a x y := by
  unfold subtended
  have h : (x - a) / y < (x + a) / y := div_lt_div_of_pos_right (by linarith) hy
  linarith [Real.arctan_strictMono h]

/-- [proved-standard; formal-checked] The subtended angle is below `π`. -/
theorem subtended_lt_pi (a x y : ℝ) : subtended a x y < Real.pi := by
  unfold subtended
  linarith [Real.arctan_lt_pi_div_two ((x + a) / y), Real.neg_pi_div_two_lt_arctan ((x - a) / y)]

/-- [proved-standard; formal-checked] High above, the angle per height is small: `α / y < π / y`. -/
theorem anglePerHeight_lt_pi_div (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    anglePerHeight a x y < Real.pi / y := by
  rw [anglePerHeight_eq_div a x hy]
  exact div_lt_div_of_pos_right (subtended_lt_pi a x y) hy

/-- [proved-standard; formal-checked] Over the segment, no higher than `a`, the segment subtends at least `π/4`. -/
theorem pi_div_four_le_subtended {a x y : ℝ} (hx : |x| ≤ a) (hy : 0 < y) (hya : y ≤ a) :
    Real.pi / 4 ≤ subtended a x y := by
  unfold subtended
  have e : (x - a) / y = -((a - x) / y) := by ring
  rw [e, Real.arctan_neg, ← Real.arctan_one]
  have h1 := Real.arctan_nonneg.mpr (div_nonneg (by linarith [neg_abs_le x]) hy.le :
    (0 : ℝ) ≤ (x + a) / y)
  have h2 := Real.arctan_nonneg.mpr (div_nonneg (by linarith [le_abs_self x]) hy.le :
    (0 : ℝ) ≤ (a - x) / y)
  rcases le_total 0 x with h | h
  · have h3 : 1 ≤ (x + a) / y := by rw [le_div_iff₀ hy]; linarith
    linarith [Real.arctan_mono h3]
  · have h3 : 1 ≤ (a - x) / y := by rw [le_div_iff₀ hy]; linarith
    linarith [Real.arctan_mono h3]

/-- [proved-standard; formal-checked] Off the segment, `(|x| − a)² ≤ (x − s)²` for every `s ∈ [−a, a]`. -/
theorem sq_le_sq_sub_of_mem {a x s : ℝ} (hax : a ≤ |x|) (hs : s ∈ Icc (-a) a) :
    (|x| - a) ^ 2 ≤ (x - s) ^ 2 := by
  rw [← sq_abs (x - s)]
  have h1 := abs_sub_abs_le_abs_sub x s
  have h2 : |s| ≤ a := abs_le.mpr hs
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- [proved-standard; formal-checked] On the axis beyond the segment, `∫_(−a)^(a) ds / (x − s)² = 2a / (x² − a²)`. -/
theorem integral_one_div_sq {a x : ℝ} (ha : 0 < a) (hax : a < |x|) :
    ∫ s in (-a)..a, 1 / (x - s) ^ 2 = 2 * a / (x ^ 2 - a ^ 2) := by
  have hd : 0 < (|x| - a) ^ 2 := pow_pos (by linarith) 2
  have hne : ∀ s ∈ uIcc (-a) a, x - s ≠ 0 := by
    intro s hs h
    rw [uIcc_of_le (by linarith)] at hs
    have := sq_le_sq_sub_of_mem hax.le hs
    rw [h] at this
    linarith [sq_nonneg (0 : ℝ)]
  have hderiv : ∀ s ∈ uIcc (-a) a, HasDerivAt (fun s => (x - s)⁻¹) (1 / (x - s) ^ 2) s := by
    intro s hs
    refine (((hasDerivAt_id' s).const_sub x).inv (hne s hs)).congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun s => 1 / (x - s) ^ 2) (uIcc (-a) a) :=
    continuousOn_const.div (by fun_prop) fun s hs => pow_ne_zero 2 (hne s hs)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : x - a ≠ 0 := hne a (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, le_rfl⟩)
  have h2 : x - -a ≠ 0 := hne (-a) (by rw [uIcc_of_le (by linarith)]; exact ⟨le_rfl, by linarith⟩)
  have h3 : x ^ 2 - a ^ 2 ≠ 0 := by
    have : (x - a) * (x - -a) ≠ 0 := mul_ne_zero h1 h2
    intro h; apply this; linear_combination h
  field_simp
  ring

/-- [proved-standard; formal-checked] Beyond the segment, `α / y < 2a / (x² − a²)`, its value on the axis. -/
theorem anglePerHeight_lt_axis {a x y : ℝ} (ha : 0 < a) (hax : a < |x|) (hy : 0 < y) :
    anglePerHeight a x y < 2 * a / (x ^ 2 - a ^ 2) := by
  rw [← integral_one_div_sq ha hax]
  have hd : 0 < (|x| - a) ^ 2 := pow_pos (by linarith) 2
  have hpos : ∀ s ∈ Icc (-a) a, 0 < (x - s) ^ 2 := fun s hs =>
    lt_of_lt_of_le hd (sq_le_sq_sub_of_mem hax.le hs)
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
    ?_ ?_ ?_ ⟨a, ⟨by linarith, le_rfl⟩, ?_⟩
  · exact (continuous_const.div (by fun_prop) fun s => by positivity).continuousOn
  · exact continuousOn_const.div (by fun_prop) fun s hs => (hpos s hs).ne'
  · intro s hs
    exact one_div_le_one_div_of_le (hpos s (Ioc_subset_Icc_self hs)) (by nlinarith)
  · exact one_div_lt_one_div_of_lt (hpos a ⟨by linarith, le_rfl⟩) (by nlinarith)

/-- [proved-standard; formal-checked] `(1 − t) / A ≤ 1 / (A + w)` when `w ≤ t A`. -/
theorem one_sub_mul_one_div_le {A t w : ℝ} (hA : 0 < A) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (htA : w ≤ t * A) : (1 - t) * (1 / A) ≤ 1 / (A + w) := by
  rw [mul_one_div, div_le_div_iff₀ hA (by linarith)]
  nlinarith [mul_nonneg ht hw]

/-- [proved-standard; formal-checked] Beyond the segment, `(1 − y²/(|x| − a)²) · 2a / (x² − a²) ≤ α / y`. -/
theorem axis_le_anglePerHeight {a x y : ℝ} (ha : 0 < a) (hax : a < |x|) (hy : 0 < y) :
    (1 - y ^ 2 / (|x| - a) ^ 2) * (2 * a / (x ^ 2 - a ^ 2)) ≤ anglePerHeight a x y := by
  rw [← integral_one_div_sq ha hax, ← intervalIntegral.integral_const_mul]
  have hd : 0 < (|x| - a) ^ 2 := pow_pos (by linarith) 2
  have hpos : ∀ s ∈ Icc (-a) a, 0 < (x - s) ^ 2 := fun s hs =>
    lt_of_lt_of_le hd (sq_le_sq_sub_of_mem hax.le hs)
  have hcont : ContinuousOn (fun s => 1 / (x - s) ^ 2) (uIcc (-a) a) := by
    rw [uIcc_of_le (by linarith)]
    exact continuousOn_const.div (by fun_prop) fun s hs => (hpos s hs).ne'
  refine intervalIntegral.integral_mono_on (by linarith) (continuousOn_const.mul hcont).intervalIntegrable
    ((continuous_const.div (by fun_prop) fun s => by positivity).intervalIntegrable _ _) ?_
  intro s hs
  have hA := sq_le_sq_sub_of_mem hax.le hs
  refine one_sub_mul_one_div_le (hpos s hs) (sq_nonneg y) (by positivity) ?_
  have e : y ^ 2 / (|x| - a) ^ 2 * (|x| - a) ^ 2 = y ^ 2 := div_mul_cancel₀ _ hd.ne'
  nlinarith [div_nonneg (sq_nonneg y) hd.le]

/-! ## 3. One height at each station -/

/-- [definition] **The oval's half-length** `L = √(a² + m a / (π U))`. -/
def halfLength (U m a : ℝ) : ℝ := Real.sqrt (a ^ 2 + m * a / (Real.pi * U))

variable {U m a : ℝ}

/-- [proved-standard; formal-checked] `L² = a² + m a / (π U)`. -/
theorem halfLength_sq (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    halfLength U m a ^ 2 = a ^ 2 + m * a / (Real.pi * U) := by
  have := Real.pi_pos
  exact Real.sq_sqrt (by positivity)

/-- [proved-standard; formal-checked] The oval reaches past the pair: `a < L`. -/
theorem lt_halfLength (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) : a < halfLength U m a := by
  have := Real.pi_pos
  rw [halfLength, Real.lt_sqrt ha.le]
  have : 0 < m * a / (Real.pi * U) := by positivity
  linarith

/-- [proved-standard; formal-checked] Beyond the segment, `2πU/m < 2a / (x² − a²)` if and only if `|x| < L`. -/
theorem lt_axis_iff (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ} (hax : a < |x|) :
    2 * Real.pi * U / m < 2 * a / (x ^ 2 - a ^ 2) ↔ |x| < halfLength U m a := by
  have hD : 0 < x ^ 2 - a ^ 2 := by have := sq_abs x; nlinarith
  have hpi := Real.pi_pos
  rw [lt_div_iff₀ hD, halfLength, Real.lt_sqrt (abs_nonneg x), sq_abs, div_mul_eq_mul_div,
    div_lt_iff₀ hm, ← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- [proved-standard; formal-checked] If `α / y ≥ c > 0` at some height, then `α / y = c` at some height. -/
theorem exists_root_of_le {x y c : ℝ} (hc : 0 < c) (hy : 0 < y) (hle : c ≤ anglePerHeight a x y) :
    ∃ y', 0 < y' ∧ anglePerHeight a x y' = c := by
  have hy₁ : y ≤ max y (Real.pi / c) := le_max_left _ _
  have hy₁0 : 0 < max y (Real.pi / c) := lt_of_lt_of_le hy hy₁
  have hlow : anglePerHeight a x (max y (Real.pi / c)) ≤ c := by
    have h1 := anglePerHeight_lt_pi_div a x hy₁0
    have h2 : Real.pi / max y (Real.pi / c) ≤ c := by
      rw [div_le_iff₀ hy₁0]
      have h3 := le_max_right y (Real.pi / c)
      rw [div_le_iff₀ hc] at h3
      linarith
    linarith
  have hcont : ContinuousOn (anglePerHeight a x) (Icc y (max y (Real.pi / c))) :=
    (continuousOn_anglePerHeight a x).mono fun t ht => lt_of_lt_of_le hy ht.1
  obtain ⟨y', hy', h⟩ := intermediate_value_Icc' hy₁ hcont ⟨hlow, hle⟩
  exact ⟨y', lt_of_lt_of_le hy hy'.1, h⟩

/-- [proved-standard; formal-checked] For `0 < c < K` and `d > 0` some `y > 0` has `c ≤ (1 − y²/d²) K`. -/
theorem exists_le_of_lt {c K d : ℝ} (hc : 0 < c) (hcK : c < K) (hd : 0 < d) :
    ∃ y, 0 < y ∧ c ≤ (1 - y ^ 2 / d ^ 2) * K := by
  have hK : 0 < K := hc.trans hcK
  have hq0 : 0 < 1 - c / K := by rw [sub_pos, div_lt_one hK]; exact hcK
  have hq1 : 1 - c / K < 1 := by have : 0 < c / K := div_pos hc hK; linarith
  refine ⟨d * (1 - c / K) / 2, by positivity, ?_⟩
  have e : (d * (1 - c / K) / 2) ^ 2 / d ^ 2 = (1 - c / K) ^ 2 / 4 := by field_simp; ring
  rw [e]
  calc c = (1 - (1 - c / K)) * K := by rw [sub_sub_cancel, div_mul_cancel₀ c hK.ne']
    _ ≤ (1 - (1 - c / K) ^ 2 / 4) * K := by
      apply mul_le_mul_of_nonneg_right _ hK.le
      nlinarith

/-- [proved-standard; formal-checked] **Some height has `α / y = 2πU/m` if and only if `|x| < L`.** -/
theorem exists_root_iff (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (x : ℝ) :
    (∃ y, 0 < y ∧ anglePerHeight a x y = 2 * Real.pi * U / m) ↔ |x| < halfLength U m a := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi * U / m := by positivity
  constructor
  · rintro ⟨y, hy, h⟩
    by_contra hL
    push Not at hL
    have hax : a < |x| := lt_of_lt_of_le (lt_halfLength hU hm ha) hL
    have h1 := anglePerHeight_lt_axis ha hax hy
    have h2 := mt (lt_axis_iff hU hm ha hax).mp (not_lt.mpr hL)
    push Not at h2
    linarith
  · intro hL
    rcases le_or_gt |x| a with hxa | hax
    · have hy0 : 0 < min a (Real.pi / (4 * (2 * Real.pi * U / m))) := lt_min ha (by positivity)
      refine exists_root_of_le hc hy0 ?_
      have h1 := pi_div_four_le_subtended hxa hy0 (min_le_left _ _)
      rw [anglePerHeight_eq_div a x hy0, le_div_iff₀ hy0]
      have h2 := min_le_right a (Real.pi / (4 * (2 * Real.pi * U / m)))
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith
    · obtain ⟨y, hy, h⟩ := exists_le_of_lt hc ((lt_axis_iff hU hm ha hax).mpr hL)
        (by linarith : 0 < |x| - a)
      exact exists_root_of_le hc hy (h.trans (axis_le_anglePerHeight ha hax hy))

open Classical in
/-- [definition] **The oval's height** `Y(x)`: the height with `α / y = 2πU/m` where one exists, else `0`. -/
def height (U m a x : ℝ) : ℝ :=
  if h : ∃ y, 0 < y ∧ anglePerHeight a x y = 2 * Real.pi * U / m then h.choose else 0

/-- [proved-standard; formal-checked] The height is nonnegative. -/
theorem height_nonneg (U m a x : ℝ) : 0 ≤ height U m a x := by
  unfold height
  split_ifs with h
  · exact h.choose_spec.1.le
  · exact le_rfl

/-- [proved-standard; formal-checked] For `y > 0`: `α / y < 2πU/m ↔ Y(x) < y` and `2πU/m < α / y ↔ y < Y(x)`. -/
theorem height_spec (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (anglePerHeight a x y < 2 * Real.pi * U / m ↔ height U m a x < y) ∧
      (2 * Real.pi * U / m < anglePerHeight a x y ↔ y < height U m a x) := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi * U / m := by positivity
  have hanti := anglePerHeight_strictAntiOn x ha
  unfold height
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h.choose_spec
    have e := hanti.lt_iff_gt hy h0
    have e' := hanti.lt_iff_gt h0 hy
    rw [h1] at e e'
    exact ⟨e, e'⟩
  · push Not at h
    have hlt : anglePerHeight a x y < 2 * Real.pi * U / m := by
      by_contra hge
      push Not at hge
      obtain ⟨y', hy', h'⟩ := exists_root_of_le hc hy hge
      exact h y' hy' h'
    exact ⟨⟨fun _ => hy, fun _ => hlt⟩, ⟨fun h' => absurd h' (not_lt.mpr hlt.le),
      fun h' => absurd h' (not_lt.mpr hy.le)⟩⟩

/-- [proved-standard; formal-checked] At a positive height, `α / Y = 2πU/m`. -/
theorem anglePerHeight_height (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (h : 0 < height U m a x) : anglePerHeight a x (height U m a x) = 2 * Real.pi * U / m := by
  have hs := height_spec hU hm ha x h
  rcases lt_trichotomy (anglePerHeight a x (height U m a x)) (2 * Real.pi * U / m) with h1 | h1 | h1
  · exact absurd (hs.1.mp h1) (lt_irrefl _)
  · exact h1
  · exact absurd (hs.2.mp h1) (lt_irrefl _)

/-- [proved-standard; formal-checked] **The height is positive if and only if `|x| < L`.** -/
theorem height_pos_iff (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (x : ℝ) :
    0 < height U m a x ↔ |x| < halfLength U m a := by
  rw [← exists_root_iff hU hm ha x]
  constructor
  · intro h
    exact ⟨_, h, anglePerHeight_height hU hm ha h⟩
  · intro h
    unfold height
    rw [dif_pos h]
    exact h.choose_spec.1

/-- [proved-standard; formal-checked] At and beyond the half-length the height is `0`. -/
theorem height_eq_zero (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (hx : halfLength U m a ≤ |x|) : height U m a x = 0 :=
  le_antisymm (not_lt.mp fun h => not_lt.mpr hx ((height_pos_iff hU hm ha x).mp h))
    (height_nonneg U m a x)

/-- [proved-standard; formal-checked] Above the axis, `ψ(x + iy) = y (U − (m/2π) α / y)`. -/
theorem ovalStream_eq_mul (U m a x : ℝ) {y : ℝ} (hy : 0 < y) :
    ovalStream U m a (x + y * I) = y * (U - m / (2 * Real.pi) * anglePerHeight a x y) := by
  have him : ((x : ℂ) + y * I).im = y := by simp
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hz : 0 < ((x : ℂ) + y * I).im := by rw [him]; exact hy
  rw [ovalStream_eq_subtended U m a hz, him, hre, subtended_eq_mul_anglePerHeight a x hy]
  ring

/-- [proved-standard; formal-checked] Above the axis, `ψ(x + iy) = 0 ↔ α / y = 2πU/m`. -/
theorem ovalStream_eq_zero_iff (U : ℝ) (hm : 0 < m) (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    ovalStream U m a (x + y * I) = 0 ↔ anglePerHeight a x y = 2 * Real.pi * U / m := by
  have hpi := Real.pi_pos
  rw [ovalStream_eq_mul U m a x hy, mul_eq_zero, or_iff_right hy.ne', sub_eq_zero,
    eq_div_iff hm.ne']
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    field_simp
    linarith

/-- [proved-standard; formal-checked] **One height at each station**: for `|x| < L` one and only one `y > 0` has
`ψ(x + iy) = 0`. -/
theorem station_existsUnique (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (hx : |x| < halfLength U m a) : ∃! y : ℝ, 0 < y ∧ ovalStream U m a (x + y * I) = 0 := by
  obtain ⟨y, hy, h⟩ := (exists_root_iff hU hm ha x).mpr hx
  refine ⟨y, ⟨hy, (ovalStream_eq_zero_iff U hm a x hy).mpr h⟩, ?_⟩
  rintro y' ⟨hy', h'⟩
  rw [ovalStream_eq_zero_iff U hm a x hy'] at h'
  exact (anglePerHeight_strictAntiOn x ha).injOn hy' hy (h'.trans h.symm)

/-- [proved-standard; formal-checked] **No height beyond the half-length**: `ψ(x + iy) ≠ 0` for `|x| ≥ L`, `y > 0`. -/
theorem station_none (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (hx : halfLength U m a ≤ |x|) {y : ℝ} (hy : 0 < y) : ovalStream U m a (x + y * I) ≠ 0 := by
  intro h
  rw [ovalStream_eq_zero_iff U hm a x hy] at h
  exact absurd ((exists_root_iff hU hm ha x).mp ⟨y, hy, h⟩) (not_lt.mpr hx)

/-- [proved-standard; formal-checked] The height is the station's root: `ψ(x + i Y(x)) = 0` where `Y(x) > 0`. -/
theorem ovalStream_height (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (h : 0 < height U m a x) : ovalStream U m a (x + height U m a x * I) = 0 :=
  (ovalStream_eq_zero_iff U hm a x h).mpr (anglePerHeight_height hU hm ha h)

/-- [proved-standard; formal-checked] **The oval is below the half-body's half-width**: `Im z < m/(2U)` on `ψ = 0`. -/
theorem oval_width (hU : 0 < U) (hm : 0 < m) {z : ℂ} (hz : 0 < z.im)
    (hψ : ovalStream U m a z = 0) : z.im < m / (2 * U) := by
  have hpi := Real.pi_pos
  rw [ovalStream_eq_subtended U m a hz] at hψ
  have h1 := subtended_lt_pi a z.re z.im
  have h2 : m / (2 * Real.pi) * subtended a z.re z.im < m / (2 * Real.pi) * Real.pi :=
    mul_lt_mul_of_pos_left h1 (by positivity)
  have h3 : m / (2 * Real.pi) * Real.pi = m / 2 := by field_simp
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- [proved-standard; formal-checked] Every height is below the half-width: `Y(x) < m/(2U)`. -/
theorem height_lt_width (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (x : ℝ) :
    height U m a x < m / (2 * U) := by
  rcases (height_nonneg U m a x).lt_or_eq with h | h
  · have := oval_width hU hm (z := x + height U m a x * I) (by simpa using h)
      (ovalStream_height hU hm ha h)
    simpa using this
  · rw [← h]
    positivity

/-! ## 4. The height is continuous and closes at the stagnation points -/

/-- [proved-standard; formal-checked] **The height is continuous along the whole axis.** -/
theorem continuous_height (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) : Continuous (height U m a) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge b 0 with hb0 | hb0
    · exact Filter.Eventually.of_forall fun x => lt_of_lt_of_le hb0 (height_nonneg U m a x)
    · have hy : 0 < (b + height U m a x₀) / 2 := by linarith
      have h1 := (height_spec hU hm ha x₀ hy).2.mpr (by linarith)
      have h2 := ((continuous_anglePerHeight_station a hy).tendsto x₀).eventually (lt_mem_nhds h1)
      filter_upwards [h2] with x hx
      have := (height_spec hU hm ha x hy).2.mp hx
      linarith
  · have hb0 : 0 < b := lt_of_le_of_lt (height_nonneg U m a x₀) hb
    have h1 := (height_spec hU hm ha x₀ hb0).1.mpr hb
    have h2 := ((continuous_anglePerHeight_station a hb0).tendsto x₀).eventually (gt_mem_nhds h1)
    filter_upwards [h2] with x hx
    exact (height_spec hU hm ha x hb0).1.mp hx

/-- [proved-standard; formal-checked] **The height tends to `0` at the ends `±L`.** -/
theorem tendsto_height_ends (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    Filter.Tendsto (height U m a) (nhds (halfLength U m a)) (nhds 0) ∧
      Filter.Tendsto (height U m a) (nhds (-halfLength U m a)) (nhds 0) := by
  have hL : 0 < halfLength U m a := ha.trans (lt_halfLength hU hm ha)
  constructor
  · have := (continuous_height hU hm ha).tendsto (halfLength U m a)
    rwa [height_eq_zero hU hm ha (by rw [abs_of_pos hL])] at this
  · have := (continuous_height hU hm ha).tendsto (-halfLength U m a)
    rwa [height_eq_zero hU hm ha (by rw [abs_neg, abs_of_pos hL])] at this

/-- [definition] The conjugate velocity `U + (m/2π)(1/(z + a) − 1/(z − a))`, the potential's `dF/dz`. -/
def ovalVelocity (U m a : ℝ) (z : ℂ) : ℂ := U + m / (2 * Real.pi) * (1 / (z + a) - 1 / (z - a))

/-- [proved-standard; formal-checked] The stream function is the imaginary part of the principal potential. -/
theorem ovalStream_eq_im (U m a : ℝ) (z : ℂ) :
    ovalStream U m a z =
      (U * z + m / (2 * Real.pi) * (Complex.log (z + a) - Complex.log (z - a))).im := by
  have e : ((m / (2 * Real.pi) : ℝ) : ℂ) = (m : ℂ) / (2 * Real.pi) := by push_cast; ring
  rw [ovalStream, ← e]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_im, Complex.log_im, sub_re, zero_mul,
    add_zero]

/-- [proved-standard; formal-checked] Off the cuts, `ovalVelocity` is the derivative of the principal potential. -/
theorem hasDerivAt_potential (U m a : ℝ) {z : ℂ} (h₁ : z + a ∈ slitPlane) (h₂ : z - a ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => U * w + m / (2 * Real.pi) * (Complex.log (w + a) - Complex.log (w - a)))
      (ovalVelocity U m a z) z := by
  have h := ((hasDerivAt_id' z).const_mul (U : ℂ)).add
    ((((hasDerivAt_id' z).add_const (a : ℂ)).clog h₁).sub
      (((hasDerivAt_id' z).sub_const (a : ℂ)).clog h₂) |>.const_mul ((m : ℂ) / (2 * Real.pi)))
  refine h.congr_deriv ?_
  rw [ovalVelocity]
  ring

/-- [proved-standard; formal-checked] At `x = ±L` on the axis, `U + (m/2π)(1/(x + a) − 1/(x − a)) = 0`. -/
theorem velocity_axis_zero (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (hx : x ^ 2 = halfLength U m a ^ 2) :
    U + m / (2 * Real.pi) * (1 / (x + a) - 1 / (x - a)) = 0 := by
  have hpi := Real.pi_pos
  rw [halfLength_sq hU hm ha] at hx
  have hq : 0 < m * a / (Real.pi * U) := by positivity
  have h1 : x + a ≠ 0 := by
    intro h; have : x = -a := by linarith
    rw [this] at hx; linarith
  have h2 : x - a ≠ 0 := by
    intro h; have : x = a := by linarith
    rw [this] at hx; linarith
  have hx' : x ^ 2 * (Real.pi * U) = a ^ 2 * (Real.pi * U) + m * a := by
    rw [hx]; field_simp
  field_simp
  linear_combination 2 * hx'

/-- [proved-standard; formal-checked] **The ends `±L` are stagnation points**: the velocity vanishes there. -/
theorem ovalVelocity_ends (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ovalVelocity U m a (halfLength U m a) = 0 ∧ ovalVelocity U m a (-halfLength U m a : ℝ) = 0 := by
  have e : ∀ x : ℝ, ovalVelocity U m a x = ((U + m / (2 * Real.pi) * (1 / (x + a) - 1 / (x - a)) : ℝ) : ℂ) := by
    intro x
    rw [ovalVelocity]
    push_cast
    ring
  rw [e, e, velocity_axis_zero hU hm ha rfl, velocity_axis_zero hU hm ha (by ring)]
  simp

/-- [proved-standard; formal-checked] **The axis beyond the segment lies on `ψ = 0`**, the points `±L` among it. -/
theorem ovalStream_axis (U m : ℝ) {a x : ℝ} (ha : 0 < a) (hx : a < |x|) : ovalStream U m a x = 0 := by
  unfold ovalStream
  rw [ofReal_im, mul_zero, zero_add, ← ofReal_add, ← ofReal_sub]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [arg_ofReal_of_nonneg (by linarith), arg_ofReal_of_nonneg (by linarith)]
    ring
  · rw [abs_of_neg h] at hx
    rw [arg_ofReal_of_neg (by linarith), arg_ofReal_of_neg (by linarith)]
    ring

/-- [proved-standard; formal-checked] **`ψ` is odd under reflection in the axis**, off the axis. -/
theorem ovalStream_conj (U m a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ovalStream U m a ((starRingEnd ℂ) z) = -ovalStream U m a z := by
  unfold ovalStream
  have h1 : (starRingEnd ℂ) z + a = (starRingEnd ℂ) (z + a) := by simp
  have h2 : (starRingEnd ℂ) z - a = (starRingEnd ℂ) (z - a) := by simp
  have hp : Complex.arg (z + a) ≠ Real.pi := fun h => hz (by simpa using (arg_eq_pi_iff.mp h).2)
  have hm : Complex.arg (z - a) ≠ Real.pi := fun h => hz (by simpa using (arg_eq_pi_iff.mp h).2)
  rw [h1, h2, arg_conj, arg_conj, if_neg hp, if_neg hm, conj_im]
  ring

/-- [proved-standard; formal-checked] For `|x| ≤ L` both `x + i Y(x)` and its mirror `x − i Y(x)` lie on `ψ = 0`. -/
theorem ovalStream_station (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {x : ℝ}
    (hx : |x| ≤ halfLength U m a) :
    ovalStream U m a (x + height U m a x * I) = 0 ∧
      ovalStream U m a (x + (-height U m a x : ℝ) * I) = 0 := by
  rcases (height_nonneg U m a x).lt_or_eq with h | h
  · have h0 := ovalStream_height hU hm ha h
    refine ⟨h0, ?_⟩
    have e : ((x : ℂ) + (-height U m a x : ℝ) * I) = (starRingEnd ℂ) (x + height U m a x * I) := by
      apply Complex.ext <;> simp
    rw [e, ovalStream_conj U m a (by simpa using h.ne'), h0, neg_zero]
  · rw [← h]
    have hL : |x| = halfLength U m a :=
      le_antisymm hx (not_lt.mp fun hlt => ((height_pos_iff hU hm ha x).mpr hlt).ne h)
    have hax : a < |x| := hL ▸ lt_halfLength hU hm ha
    simp only [ofReal_zero, zero_mul, add_zero, neg_zero]
    exact ⟨ovalStream_axis U m ha hax, ovalStream_axis U m ha hax⟩

/-! ## 5. The oval is a closed curve -/

/-- [definition] The station along the loop, `x(t) = L (4|t − 1/2| − 1)`: `L`, then `−L`, then `L`. -/
def loopStation (U m a t : ℝ) : ℝ := halfLength U m a * (4 * |t - 1 / 2| - 1)

/-- [definition] The signed height along the loop: `Y(x(t))` for `t ≤ 1/2`, `−Y(x(t))` after. -/
def loopHeight (U m a t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then height U m a (loopStation U m a t) else -height U m a (loopStation U m a t)

/-- [proved-standard; formal-checked] On the upper half, `x(t) = L (1 − 4t)`. -/
theorem loopStation_of_le {t : ℝ} (h : t ≤ 1 / 2) :
    loopStation U m a t = halfLength U m a * (1 - 4 * t) := by
  rw [loopStation, abs_of_nonpos (by linarith)]
  ring

/-- [proved-standard; formal-checked] On the lower half, `x(t) = L (4t − 3)`. -/
theorem loopStation_of_gt {t : ℝ} (h : 1 / 2 < t) :
    loopStation U m a t = halfLength U m a * (4 * t - 3) := by
  rw [loopStation, abs_of_pos (by linarith)]
  ring

/-- [proved-standard; formal-checked] For `t ∈ [0, 1]` the station stays in `[−L, L]`. -/
theorem abs_loopStation_le (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : |loopStation U m a t| ≤ halfLength U m a := by
  have hL : 0 < halfLength U m a := ha.trans (lt_halfLength hU hm ha)
  rw [abs_le]
  rcases le_or_gt t (1 / 2) with h | h
  · rw [loopStation_of_le h]; constructor <;> nlinarith
  · rw [loopStation_of_gt h]; constructor <;> nlinarith

/-- [proved-standard; formal-checked] Halfway round, the height is `0`. -/
theorem height_loopStation_half (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    height U m a (loopStation U m a (1 / 2)) = 0 := by
  have hL : 0 < halfLength U m a := ha.trans (lt_halfLength hU hm ha)
  apply height_eq_zero hU hm ha
  rw [loopStation_of_le le_rfl]
  norm_num [abs_of_pos hL]

/-- [proved-standard; formal-checked] At `L` the height is `0`. -/
theorem height_halfLength (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    height U m a (halfLength U m a) = 0 := by
  have hL : 0 < halfLength U m a := ha.trans (lt_halfLength hU hm ha)
  exact height_eq_zero hU hm ha (by rw [abs_of_pos hL])

/-- [proved-standard; formal-checked] The signed height is continuous: the two halves meet where `Y = 0`. -/
theorem continuous_loopHeight (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    Continuous (loopHeight U m a) := by
  have hc : Continuous fun t => height U m a (loopStation U m a t) :=
    (continuous_height hU hm ha).comp (by unfold loopStation; fun_prop)
  refine hc.if_le hc.neg continuous_id continuous_const fun t ht => ?_
  have ht' : t = 1 / 2 := ht
  rw [ht', height_loopStation_half hU hm ha, neg_zero]

/-- [definition] **The Rankine oval as a loop**: `x(t) + i Y(x(t))` on the upper half, its mirror below. -/
def ovalLoop (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) : C(unitInterval, ℂ) :=
  ⟨fun t => (loopStation U m a t : ℂ) + (loopHeight U m a t : ℂ) * I, by
    have h1 := continuous_loopHeight hU hm ha
    have h2 : Continuous (loopStation U m a) := by unfold loopStation; fun_prop
    fun_prop⟩

/-- [definition] The loop's value, unfolded. -/
theorem ovalLoop_apply (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    ovalLoop hU hm ha t = (loopStation U m a t : ℂ) + (loopHeight U m a t : ℂ) * I := rfl

/-- [proved-standard; formal-checked] The loop's real part is its station. -/
theorem ovalLoop_re (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    (ovalLoop hU hm ha t).re = loopStation U m a t := by
  simp [ovalLoop_apply]

/-- [proved-standard; formal-checked] The loop's imaginary part is its signed height. -/
theorem ovalLoop_im (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    (ovalLoop hU hm ha t).im = loopHeight U m a t := by
  simp [ovalLoop_apply]

/-- [proved-standard; formal-checked] The loop starts at the stagnation point `L`. -/
theorem ovalLoop_zero (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ovalLoop hU hm ha 0 = halfLength U m a := by
  have hs : loopStation U m a 0 = halfLength U m a := by rw [loopStation_of_le (by norm_num)]; ring
  rw [ovalLoop_apply, Set.Icc.coe_zero, loopHeight, if_pos (by norm_num), hs,
    height_halfLength hU hm ha]
  simp

/-- [proved-standard; formal-checked] **The loop is closed**: `γ 0 = γ 1`. -/
theorem ovalLoop_closed (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ovalLoop hU hm ha 0 = ovalLoop hU hm ha 1 := by
  have hs : loopStation U m a 1 = halfLength U m a := by rw [loopStation_of_gt (by norm_num)]; ring
  rw [ovalLoop_zero, ovalLoop_apply, Set.Icc.coe_one, loopHeight, if_neg (by norm_num), hs,
    height_halfLength hU hm ha]
  simp

/-- [proved-standard; formal-checked] Halfway round, the loop passes the stagnation point `−L`. -/
theorem ovalLoop_half (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ovalLoop hU hm ha ⟨1 / 2, by norm_num, by norm_num⟩ = -(halfLength U m a : ℂ) := by
  have hs : loopStation U m a (1 / 2) = -halfLength U m a := by
    rw [loopStation_of_le le_rfl]; ring
  rw [ovalLoop_apply]
  simp only
  rw [loopHeight, if_pos le_rfl, height_loopStation_half hU hm ha, hs]
  simp

/-- [proved-standard; formal-checked] **The loop lies on the dividing streamline**: `ψ(γ t) = 0` for every `t`. -/
theorem ovalLoop_stream (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    ovalStream U m a (ovalLoop hU hm ha t) = 0 := by
  have hx := abs_loopStation_le hU hm ha t.2.1 t.2.2
  have hs := ovalStream_station hU hm ha hx
  rw [ovalLoop_apply, loopHeight]
  split_ifs
  · exact hs.1
  · exact hs.2

/-- [proved-standard; formal-checked] **The lower half mirrors the upper half**: `γ(1 − t) = conj γ(t)`. -/
theorem ovalLoop_symm (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    ovalLoop hU hm ha (unitInterval.symm t) = (starRingEnd ℂ) (ovalLoop hU hm ha t) := by
  have hst : loopStation U m a (1 - (t : ℝ)) = loopStation U m a t := by
    rw [loopStation, loopStation, show (1 : ℝ) - t - 1 / 2 = -((t : ℝ) - 1 / 2) by ring, abs_neg]
  rw [ovalLoop_apply, ovalLoop_apply, unitInterval.coe_symm_eq, hst]
  apply Complex.ext
  · simp
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add,
      conj_im, add_zero]
    unfold loopHeight
    rw [hst]
    rcases lt_trichotomy (t : ℝ) (1 / 2) with h | h | h
    · rw [if_neg (by linarith), if_pos h.le]
    · have h0 : height U m a (loopStation U m a t) = 0 := by
        rw [h]; exact height_loopStation_half hU hm ha
      simp [h0]
    · rw [if_pos (by linarith), if_neg (not_le.mpr h), neg_neg]

/-- [proved-standard; formal-checked] **The loop is simple**: it is injective on `[0, 1)`. -/
theorem ovalLoop_injOn (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    Set.InjOn (ovalLoop hU hm ha) {t | (t : ℝ) < 1} := by
  have hL : 0 < halfLength U m a := ha.trans (lt_halfLength hU hm ha)
  have hlow : ∀ t : unitInterval, 1 / 2 < (t : ℝ) → (t : ℝ) < 1 → loopHeight U m a t < 0 := by
    intro t h1 h2
    have hx : |loopStation U m a t| < halfLength U m a := by
      rw [loopStation_of_gt h1, abs_lt]; constructor <;> nlinarith
    rw [loopHeight, if_neg (not_le.mpr h1), neg_lt_zero]
    exact (height_pos_iff hU hm ha _).mpr hx
  have hup : ∀ t : unitInterval, (t : ℝ) ≤ 1 / 2 → 0 ≤ loopHeight U m a t := by
    intro t h
    rw [loopHeight, if_pos h]
    exact height_nonneg U m a _
  intro s hs t ht hst
  have hre := congrArg Complex.re hst
  have him := congrArg Complex.im hst
  rw [ovalLoop_re, ovalLoop_re] at hre
  rw [ovalLoop_im, ovalLoop_im] at him
  change (s : ℝ) < 1 at hs
  change (t : ℝ) < 1 at ht
  apply Subtype.ext
  rcases le_or_gt (s : ℝ) (1 / 2) with h1 | h1 <;> rcases le_or_gt (t : ℝ) (1 / 2) with h2 | h2
  · rw [loopStation_of_le h1, loopStation_of_le h2] at hre
    have := mul_left_cancel₀ hL.ne' hre
    linarith
  · linarith [hup s h1, hlow t h2 ht]
  · linarith [hup t h2, hlow s h1 hs]
  · rw [loopStation_of_gt h1, loopStation_of_gt h2] at hre
    have := mul_left_cancel₀ hL.ne' hre
    linarith

/-- [proved-standard; formal-checked] `|Re γ| ≤ L`, `|Im γ| = Y(Re γ)` and `|Im γ| < m/(2U)`. -/
theorem ovalLoop_bounds (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) :
    |(ovalLoop hU hm ha t).re| ≤ halfLength U m a ∧
      |(ovalLoop hU hm ha t).im| = height U m a (ovalLoop hU hm ha t).re ∧
      |(ovalLoop hU hm ha t).im| < m / (2 * U) := by
  rw [ovalLoop_re, ovalLoop_im]
  have hY : |loopHeight U m a t| = height U m a (loopStation U m a t) := by
    rw [loopHeight]
    split_ifs
    · exact abs_of_nonneg (height_nonneg U m a _)
    · rw [abs_neg]; exact abs_of_nonneg (height_nonneg U m a _)
  exact ⟨abs_loopStation_le hU hm ha t.2.1 t.2.2, hY, hY ▸ height_lt_width hU hm ha _⟩

/-- [proved-standard; formal-checked] The loop avoids the segment `[−a, a]`, so the source and the sink. -/
theorem ovalLoop_avoids (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : unitInterval) {s : ℝ}
    (hs : |s| ≤ a) : ovalLoop hU hm ha t ≠ s := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [ovalLoop_im, ofReal_im] at him
  rw [ovalLoop_re, ofReal_re] at hre
  have hY : height U m a (loopStation U m a t) = 0 := by
    unfold loopHeight at him
    split_ifs at him
    · exact him
    · linarith
  have hx : halfLength U m a ≤ |loopStation U m a t| :=
    not_lt.mp fun hlt => ((height_pos_iff hU hm ha _).mpr hlt).ne' hY
  rw [hre] at hx
  linarith [lt_halfLength hU hm ha]

/-- [proved-standard; formal-checked] **Sufficiency (Rankine): zero net strength in a stream gives a closed dividing
streamline**, simple, through `±L`, avoiding the pair, within `|x| ≤ L` and `|y| < m/(2U)`. -/
theorem rankine_oval_closes (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧ (∀ t, ovalStream U m a (γ t) = 0) ∧
      γ 0 = halfLength U m a ∧ (∃ t, γ t = -(halfLength U m a : ℂ)) ∧
      Set.InjOn γ {t | (t : ℝ) < 1} ∧ (∀ t (s : ℝ), |s| ≤ a → γ t ≠ s) ∧
      ∀ t, |(γ t).re| ≤ halfLength U m a ∧ |(γ t).im| < m / (2 * U) :=
  ⟨ovalLoop hU hm ha, ovalLoop_closed hU hm ha, ovalLoop_stream hU hm ha, ovalLoop_zero hU hm ha,
    ⟨_, ovalLoop_half hU hm ha⟩, ovalLoop_injOn hU hm ha,
    fun t _ hs => ovalLoop_avoids hU hm ha t hs,
    fun t => ⟨(ovalLoop_bounds hU hm ha t).1, (ovalLoop_bounds hU hm ha t).2.2⟩⟩

/-! ## 6. The join to necessity: the oval winds once around the source and the sink -/

/-- [definition] The upper point over the loop's station, `u(t) = x(t) + i Y(x(t))`. -/
def upperPoint (U m a t : ℝ) : ℂ :=
  (loopStation U m a t : ℂ) + (height U m a (loopStation U m a t) : ℂ) * I

/-- [proved-standard; formal-checked] The upper point is continuous. -/
theorem continuous_upperPoint (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    Continuous (upperPoint U m a) := by
  have h1 : Continuous (loopStation U m a) := by unfold loopStation; fun_prop
  have h2 : Continuous fun t => height U m a (loopStation U m a t) :=
    (continuous_height hU hm ha).comp h1
  unfold upperPoint
  fun_prop

/-- [proved-standard; formal-checked] The upper point lies in the closed upper half-plane. -/
theorem upperPoint_sub_im_nonneg (t s : ℝ) : 0 ≤ (upperPoint U m a t - s).im := by
  simpa [upperPoint] using height_nonneg U m a (loopStation U m a t)

/-- [proved-standard; formal-checked] The upper point avoids every point of the segment. -/
theorem upperPoint_sub_ne (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) (t : ℝ) {s : ℝ} (hs : |s| ≤ a) :
    upperPoint U m a t - s ≠ 0 := by
  intro h
  have him : height U m a (loopStation U m a t) = 0 := by
    simpa [upperPoint] using congrArg Complex.im h
  have hre : loopStation U m a t - s = 0 := by
    simpa [upperPoint] using congrArg Complex.re h
  have hx : halfLength U m a ≤ |loopStation U m a t| :=
    not_lt.mp fun hlt => ((height_pos_iff hU hm ha _).mpr hlt).ne' him
  have hst : loopStation U m a t = s := by linarith
  rw [hst] at hx
  linarith [lt_halfLength hU hm ha]

/-- [proved-standard; formal-checked] The principal logarithm of `u(t) − s` is continuous: the cut is met from above. -/
theorem continuous_log_upperPoint (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a) :
    Continuous fun t => Complex.log (upperPoint U m a t - s) := by
  have hf : Continuous fun t => upperPoint U m a t - s :=
    (continuous_upperPoint hU hm ha).sub continuous_const
  refine continuous_iff_continuousAt.mpr fun t => ?_
  by_cases hw : upperPoint U m a t - s ∈ slitPlane
  · exact hf.continuousAt.clog hw
  · rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hw
    have hre : (upperPoint U m a t - s).re < 0 := by
      rcases hw.1.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext_iff.mpr ⟨by simpa using h, by simpa using hw.2⟩)
          (upperPoint_sub_ne hU hm ha t hs)
    have hc := (continuousWithinAt_log_of_re_neg_of_im_zero hre hw.2).comp
      (f := fun t => upperPoint U m a t - s) hf.continuousAt.continuousWithinAt (s := univ)
      (fun t' _ => (upperPoint_sub_im_nonneg t' s : 0 ≤ (upperPoint U m a t' - s).im))
    exact (continuousWithinAt_univ _ _).mp hc

/-- [proved-standard; formal-checked] Halfway round, the upper point is `−L`. -/
theorem upperPoint_half (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    upperPoint U m a (1 / 2) = (-halfLength U m a : ℝ) := by
  rw [upperPoint, height_loopStation_half hU hm ha, loopStation_of_le le_rfl]
  push_cast
  ring

/-- [proved-standard; formal-checked] At the start the upper point is `L`. -/
theorem upperPoint_zero (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    upperPoint U m a 0 = halfLength U m a := by
  have hs : loopStation U m a 0 = halfLength U m a := by rw [loopStation_of_le (by norm_num)]; ring
  rw [upperPoint, hs, height_halfLength hU hm ha]
  simp

/-- [proved-standard; formal-checked] At the end the upper point is `L`. -/
theorem upperPoint_one (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    upperPoint U m a 1 = halfLength U m a := by
  have hs : loopStation U m a 1 = halfLength U m a := by rw [loopStation_of_gt (by norm_num)]; ring
  rw [upperPoint, hs, height_halfLength hU hm ha]
  simp

/-- [definition] **The logarithm continued around the site `s`**: `log (u − s)`, then `conj log (u − s) + 2πi`. -/
def loopLog (U m a s t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then Complex.log (upperPoint U m a t - s)
  else (starRingEnd ℂ) (Complex.log (upperPoint U m a t - s)) + 2 * Real.pi * I

/-- [proved-standard; formal-checked] The continued logarithm is continuous: its halves meet at `log (L + s) + πi`. -/
theorem continuous_loopLog (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a) :
    Continuous (loopLog U m a s) := by
  have h := continuous_log_upperPoint hU hm ha hs
  refine h.if_le ((Complex.continuous_conj.comp h).add continuous_const) continuous_id
    continuous_const fun t ht => ?_
  have ht' : t = 1 / 2 := ht
  have hL := lt_halfLength hU hm ha
  have hneg : -halfLength U m a - s < 0 := by linarith [neg_abs_le s]
  rw [ht', upperPoint_half hU hm ha, ← ofReal_sub]
  apply Complex.ext
  · simp
  · have e : (2 * (Real.pi : ℂ) * I).im = 2 * Real.pi := by simp
    rw [add_im, conj_im, log_im, arg_ofReal_of_neg hneg, e]
    ring

/-- [proved-standard; formal-checked] On the upper half the loop is the upper point, `x(t) + i Y(x(t))`. -/
theorem ovalLoop_eq_upper (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {t : unitInterval}
    (h : (t : ℝ) ≤ 1 / 2) : ovalLoop hU hm ha t = upperPoint U m a t := by
  rw [ovalLoop_apply, loopHeight, if_pos h, upperPoint]

/-- [proved-standard; formal-checked] On the lower half the loop is the upper point's mirror, `x(t) − i Y(x(t))`. -/
theorem ovalLoop_eq_conj_upper (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {t : unitInterval}
    (h : ¬(t : ℝ) ≤ 1 / 2) : ovalLoop hU hm ha t = (starRingEnd ℂ) (upperPoint U m a t) := by
  rw [ovalLoop_apply, loopHeight, if_neg h, upperPoint]
  apply Complex.ext <;> simp

/-- [proved-standard; formal-checked] The continued logarithm lifts the loop's ratio: `exp ℓ(t) = γ(t) − s`. -/
theorem exp_loopLog (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a)
    (t : unitInterval) : Complex.exp (loopLog U m a s t) = ovalLoop hU hm ha t - s := by
  have hw := upperPoint_sub_ne hU hm ha t hs
  unfold loopLog
  split_ifs with h
  · rw [exp_log hw, ovalLoop_eq_upper hU hm ha h]
  · rw [exp_add, exp_conj, exp_log hw, exp_two_pi_mul_I, mul_one, ovalLoop_eq_conj_upper hU hm ha h,
      map_sub, conj_ofReal]

/-- [definition] The continued logarithm as a path. -/
def loopLift (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a) : C(unitInterval, ℂ) :=
  ⟨fun t => loopLog U m a s t, (continuous_loopLog hU hm ha hs).comp continuous_subtype_val⟩

/-- [proved-standard; formal-checked] **The path lifting along the oval is the continued logarithm** (`siteLift`). -/
theorem siteLift_ovalLoop (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a)
    (havoid : ∀ t, ovalLoop hU hm ha t ≠ s) :
    siteLift (ovalLoop hU hm ha) s havoid = loopLift hU hm ha hs := by
  symm
  refine (Complex.isCoveringMap_exp.eq_liftPath_iff' _).mpr ⟨funext fun t => ?_, ?_⟩
  · refine Subtype.ext ?_
    exact exp_loopLog hU hm ha hs t
  · change loopLog U m a s 0 = Complex.log (ovalLoop hU hm ha 0 - s)
    rw [loopLog, if_pos (by norm_num), ovalLoop_eq_upper hU hm ha (by norm_num)]
    rfl

/-- [proved-standard; formal-checked] **The oval winds once around each point of the segment** (`Body.winding`). -/
theorem ovalLoop_winding (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a) :
    winding (ovalLoop hU hm ha) s (fun t => ovalLoop_avoids hU hm ha t hs)
      (ovalLoop_closed hU hm ha) = 1 := by
  have hadv := siteLift_advance (ovalLoop hU hm ha) s (fun t => ovalLoop_avoids hU hm ha t hs)
    (ovalLoop_closed hU hm ha)
  rw [siteLift_ovalLoop hU hm ha hs] at hadv
  have hL := lt_halfLength hU hm ha
  have hpos : 0 ≤ halfLength U m a - s := by linarith [le_abs_self s]
  have h1 : loopLift hU hm ha hs 1 = loopLift hU hm ha hs 0 + 2 * Real.pi * I := by
    change loopLog U m a s 1 = loopLog U m a s 0 + 2 * Real.pi * I
    rw [loopLog, loopLog, if_neg (by norm_num), if_pos (by norm_num), upperPoint_one hU hm ha,
      upperPoint_zero hU hm ha, ← ofReal_sub, ← ofReal_log hpos, conj_ofReal]
  rw [h1, add_right_inj] at hadv
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn : ((winding (ovalLoop hU hm ha) s (fun t => ovalLoop_avoids hU hm ha t hs)
      (ovalLoop_closed hU hm ha) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    have := mul_right_cancel₀ h2pi (hadv.symm.trans (one_mul _).symm)
    simpa using this
  exact_mod_cast hn

/-- [proved-standard; formal-checked] The source and the sink lie on the segment `[−a, a]`. -/
theorem abs_pairSite_le (ha : 0 < a) (k : Fin 2) : |(![-a, a] k : ℝ)| ≤ a := by
  fin_cases k <;> simp [abs_of_pos ha]

/-- [proved-standard; formal-checked] For the pair, `Im F = U Im z + (m/2π)(Im ℓ₀ − Im ℓ₁)` through any lifts. -/
theorem liftedPotential_pair_im (U m : ℝ) (z : ℂ) (ℓ : Fin 2 → ℂ) :
    (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) z ℓ).im =
      U * z.im + m / (2 * Real.pi) * ((ℓ 0).im - (ℓ 1).im) := by
  have e : ∀ (r : ℝ) (w : ℂ), ((r : ℂ) / (2 * Real.pi) * w).im = r / (2 * Real.pi) * w.im := by
    intro r w
    rw [show (r : ℂ) / (2 * Real.pi) = ((r / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      im_ofReal_mul]
  simp only [liftedPotential, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_im, e, im_ofReal_mul]
  ring

/-- [proved-standard; formal-checked] **Along the oval, read through the continued lifts, `ψ` is `0`.** -/
theorem ovalLoop_potential_im (hU : 0 < U) (hm : 0 < m) (ha : 0 < a)
    (havoid : ∀ t k, ovalLoop hU hm ha t ≠ ((![-a, a] k : ℝ) : ℂ)) (t : unitInterval) :
    (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) (ovalLoop hU hm ha t)
      fun k => siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) t).im = 0 := by
  have hk : ∀ k, (siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) t).im =
      (loopLog U m a (![-a, a] k) t).im := by
    intro k
    rw [siteLift_ovalLoop hU hm ha (abs_pairSite_le ha k)]
    rfl
  rw [liftedPotential_pair_im, hk 0, hk 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hx := abs_loopStation_le hU hm ha t.2.1 t.2.2
  have hψ : ovalStream U m a (upperPoint U m a t) = 0 := (ovalStream_station hU hm ha hx).1
  have him : (upperPoint U m a t).im = height U m a (loopStation U m a t) := by simp [upperPoint]
  rw [ovalStream, him] at hψ
  have e : (2 * (Real.pi : ℂ) * I).im = 2 * Real.pi := by simp
  rw [ovalLoop_im]
  unfold loopLog loopHeight
  rw [ofReal_neg, sub_neg_eq_add]
  split_ifs with h
  · rw [log_im, log_im]
    exact hψ
  · rw [add_im, add_im, conj_im, conj_im, log_im, log_im, e]
    linear_combination -hψ

/-- [proved-standard; formal-checked] **The join to necessity**: the oval meets the hypotheses of
`closed_streamline_net_zero` (windings `1`, `ψ` constant through the lifts), which reads back `m − m = 0`. -/
theorem rankine_oval_net_zero (hU : 0 < U) (hm : 0 < m) (ha : 0 < a) :
    ∃ havoid : ∀ t k, ovalLoop hU hm ha t ≠ ((![-a, a] k : ℝ) : ℂ),
      (∀ k, winding (ovalLoop hU hm ha) _ (havoid · k) (ovalLoop_closed hU hm ha) = 1) ∧
      (∀ t, (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) (ovalLoop hU hm ha t)
          fun k => siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) t).im =
        (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) (ovalLoop hU hm ha 0)
          fun k => siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) 0).im) ∧
      ∑ k, (((![m, -m] k : ℝ) : ℂ)).re = 0 := by
  have havoid : ∀ t k, ovalLoop hU hm ha t ≠ ((![-a, a] k : ℝ) : ℂ) :=
    fun t k => ovalLoop_avoids hU hm ha t (abs_pairSite_le ha k)
  have hwind : ∀ k, winding (ovalLoop hU hm ha) _ (havoid · k) (ovalLoop_closed hU hm ha) = 1 :=
    fun k => ovalLoop_winding hU hm ha (abs_pairSite_le ha k)
  have hstream : ∀ t, (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) (ovalLoop hU hm ha t)
          fun k => siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) t).im =
        (liftedPotential U (fun k => ((![m, -m] k : ℝ) : ℂ)) (ovalLoop hU hm ha 0)
          fun k => siteLift (ovalLoop hU hm ha) ((![-a, a] k : ℝ) : ℂ) (havoid · k) 0).im :=
    fun t => (ovalLoop_potential_im hU hm ha havoid t).trans
      (ovalLoop_potential_im hU hm ha havoid 0).symm
  exact ⟨havoid, hwind, hstream, closed_streamline_net_zero U _ _ (ovalLoop hU hm ha)
    (ovalLoop_closed hU hm ha) havoid hwind hstream⟩

section Audit

#print axioms subtended_eq_mul_anglePerHeight
#print axioms anglePerHeight_strictAntiOn
#print axioms exists_root_iff
#print axioms station_existsUnique
#print axioms station_none
#print axioms continuous_height
#print axioms tendsto_height_ends
#print axioms ovalVelocity_ends
#print axioms ovalLoop_injOn
#print axioms rankine_oval_closes
#print axioms ovalLoop_winding
#print axioms rankine_oval_net_zero

end Audit

end Holonics.Physics.Fluid.RankineOval
