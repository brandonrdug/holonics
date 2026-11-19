import Mathlib

/-!
# A causal stable response is its minimum-phase face times the basins the magnitude cannot see

Source: #410's box "Information spectroscopy (#404)", its clause "for a rational causal stable `H`, `H = H_min B` with
`|H| = |H_min|` on the circle and `B` a finite Blaschke product whose degree is the winding deficit", and the record
`research/records/2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md`,
§5 ("The basins the magnitude cannot see"). The record's chart: a response `H(z)` read on the receiver's ring
`|z| = 1`, causal as a series in `z^(−k)`, stable with its poles inside the disk, minimum phase with its zeros there
too; its witness is `H = (z − 2)/(z − 1/3)`, `H_min = (2z − 1)/(z − 1/3)`, `B = (z − 2)/(2z − 1)`.

The model. A rational response in factored form, `H(z) = c ∏_(a∈Z) (z − a) / ∏_(p∈P) (z − p)` with `Z`, `P` finite
multisets of zeros and poles (`response`). Its zeros outside the closed disk, `|a| > 1`, are the hidden basins
(`outer`); the rest are `inner`. The minimum-phase face replaces each hidden factor `z − a` by `āz − 1`
(`minPhase`), which is `ā(z − 1/ā)`: the zero moved to its conjugate reciprocal `1/ā` (`reflect`) inside the disk. The
basins' factor is the finite Blaschke product `B(z) = ∏_(outer) (z − a)/(āz − 1)` (`blaschke`). The winding of a
response on the ring is `(2πi)⁻¹ ∮_(|z|=1) H′/H`, with `H′/H` Mathlib's `logDeriv` (`winding`).

[proved-standard; formal-checked] What is proved.

1. **The factorization** (`response_eq_minPhase_mul_blaschke`): `H = H_min · B` at every `z` with `āz ≠ 1` for each
   hidden zero, on the circle in particular.
2. **`B` is all-pass** (`norm_conj_mul_sub_one`, `norm_zeroProd_eq_norm_reflectProd`, `norm_blaschke`): on `|z| = 1`,
   `|āz − 1| = |z − a|`, so `|B(z)| = 1` for any zeros off the circle; hence `|H| = |H_min|` on the whole ring
   (`norm_response_eq_norm_minPhase`), with no hypothesis on `H`: the magnitude face cannot see `B`.
3. **`H_min` is minimum phase** (`reflectProd_eq`, `minPhase_eq_response`, `norm_reflect_lt_one`,
   `minPhase_zeros_le_one`): `H_min` is the response with constant `c ∏ ā` and zeros `inner Z + reflect(outer Z)`, every
   one of them in the closed disk, with the poles of `H`. Where `H` is stable its poles are inside, so `H_min` is
   minimum phase and stable.
4. **The winding counts the basins** (`logDeriv_zeroProd`, `logDeriv_response`, `circleIntegral_sub_inv_inside`,
   `circleIntegral_sub_inv_outside`, `circleIntegral_sumInv`, `winding_response`): for `c ≠ 0` and zeros and poles off
   the circle, `H′/H = Σ_Z (z − a)⁻¹ − Σ_P (z − p)⁻¹`, and the winding is the count of zeros inside less the count of
   poles inside (the argument principle for a factored rational response, from `∮ (z − a)⁻¹ = 2πi` inside and `0`
   outside, Cauchy).
5. **The degree of `B` is the winding deficit** (`winding_minPhase`, `winding_deficit`, `winding_blaschke`,
   `winding_response_eq_add`): `winding(H_min) − winding(H) = deg B`, the number of hidden basins, and
   `winding(B) = −deg B`, so `winding(H) = winding(H_min) + winding(B)`.
6. **The record's witness** (`witness_minPhase`, `witness_blaschke`, `witness_windings`): for `H = (z − 2)/(z − 1/3)`
   the construction gives `H_min = (2z − 1)/(z − 1/3)` and `B = (z − 2)/(2z − 1)`; `H` winds `−1` and `H_min` winds `0`
   (the record's "constant term `−1`, the winding of one hidden basin").

Limits. The response is given factored, over a finite multiset of zeros and poles: Beurling's inner–outer
factorization for a general `H^∞` function and the singular inner factor (the record's "mass sitting on the horizon")
are not stated. Zeros on the circle are not reflected and make the winding undefined, so the winding theorems take
every zero and pole off it. That `H_min` is determined by `|H|` on the circle, and the causal complex cepstrum of
§5 (`log H_min` one-sided, its log-magnitude and phase sharing one term list), are not proved; neither are the
receipts' aliasing checks on `N = 8` channels. Causality and stability enter only as where the poles stand: the
theorems hold for any poles off the circle.

The computational object is the helical pair interaction: a zero or a pole of a response is a basin of the pair's
transport on the receiver's ring, a basin inside the disk winds the ring's phase once, and the reflection `a ↦ 1/ā`
moves a basin across the ring without changing its magnitude face. Of the winding guide's six general objects this
touches faces and placement (the magnitude face on the ring and the basins placed in and out of the disk) and the
cell holonomy (the winding of the phase round the ring, an integer count); the helix, the pair, the tube and the
tower thread stay attached.

Consumers: the atlas row `spectro.hidden-basins`; `Transport/InformationSpectroscopy`, whose Limits named this clause
and whose `basinResponse` is one reflected factor read from inside; #410's spectroscopy box.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Transport.MinimumPhase

open Complex Metric
open scoped ComplexConjugate Real

/-! ## 1. The factored response, its minimum-phase face and its basins -/

/-- [definition] `∏_(a∈Z) (z − a)`. -/
noncomputable def zeroProd (Z : Multiset ℂ) (z : ℂ) : ℂ := (Z.map fun a => z - a).prod

/-- [definition] `∏_(a∈Z) (āz − 1)`, the reflected factors. -/
noncomputable def reflectProd (Z : Multiset ℂ) (z : ℂ) : ℂ := (Z.map fun a => conj a * z - 1).prod

/-- [definition] The rational response `H(z) = c ∏_Z (z − a) / ∏_P (z − p)`. -/
noncomputable def response (c : ℂ) (Z P : Multiset ℂ) (z : ℂ) : ℂ := c * zeroProd Z z / zeroProd P z

/-- [definition] The hidden basins: the zeros outside the closed disk. -/
noncomputable def outer (Z : Multiset ℂ) : Multiset ℂ := Z.filter fun a => 1 < ‖a‖

/-- [definition] The zeros in the closed disk. -/
noncomputable def inner (Z : Multiset ℂ) : Multiset ℂ := Z.filter fun a => ¬ 1 < ‖a‖

/-- [definition] The conjugate reciprocal `1/ā`, a zero's mirror across the ring. -/
noncomputable def reflect (a : ℂ) : ℂ := (conj a)⁻¹

/-- [definition] The minimum-phase face `H_min(z) = c ∏_inner (z − a) ∏_outer (āz − 1) / ∏_P (z − p)`. -/
noncomputable def minPhase (c : ℂ) (Z P : Multiset ℂ) (z : ℂ) : ℂ :=
  c * (zeroProd (inner Z) z * reflectProd (outer Z) z) / zeroProd P z

/-- [definition] The finite Blaschke product `B(z) = ∏_Z (z − a)/(āz − 1)` of a multiset of basins. -/
noncomputable def blaschke (Z : Multiset ℂ) (z : ℂ) : ℂ := zeroProd Z z / reflectProd Z z

@[simp] theorem zeroProd_zero (z : ℂ) : zeroProd 0 z = 1 := by simp [zeroProd]

@[simp] theorem zeroProd_cons (a : ℂ) (Z : Multiset ℂ) (z : ℂ) :
    zeroProd (a ::ₘ Z) z = (z - a) * zeroProd Z z := by
  simp [zeroProd]

theorem zeroProd_add (Z W : Multiset ℂ) (z : ℂ) : zeroProd (Z + W) z = zeroProd Z z * zeroProd W z := by
  simp [zeroProd]

@[simp] theorem reflectProd_zero (z : ℂ) : reflectProd 0 z = 1 := by simp [reflectProd]

@[simp] theorem reflectProd_cons (a : ℂ) (Z : Multiset ℂ) (z : ℂ) :
    reflectProd (a ::ₘ Z) z = (conj a * z - 1) * reflectProd Z z := by
  simp [reflectProd]

/-- [proved-standard; formal-checked] `∏ (z − a)` vanishes only at a zero. -/
theorem zeroProd_ne_zero {Z : Multiset ℂ} {z : ℂ} (h : z ∉ Z) : zeroProd Z z ≠ 0 := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    rw [Multiset.mem_cons, not_or] at h
    rw [zeroProd_cons]
    exact mul_ne_zero (sub_ne_zero.2 h.1) (ih h.2)

/-- [proved-standard; formal-checked] The zeros split into the inner and the hidden ones. -/
theorem zeroProd_inner_mul_outer (Z : Multiset ℂ) (z : ℂ) :
    zeroProd (inner Z) z * zeroProd (outer Z) z = zeroProd Z z := by
  rw [← zeroProd_add, inner, outer, add_comm, Multiset.filter_add_not]

/-- [proved-standard; formal-checked] **The factorization** `H = H_min · B`, wherever no hidden factor `āz − 1`
vanishes. -/
theorem response_eq_minPhase_mul_blaschke (c : ℂ) (Z P : Multiset ℂ) (z : ℂ)
    (h : reflectProd (outer Z) z ≠ 0) :
    response c Z P z = minPhase c Z P z * blaschke (outer Z) z := by
  rw [response, minPhase, blaschke, ← zeroProd_inner_mul_outer Z z]
  rcases eq_or_ne (zeroProd P z) 0 with hP | hP
  · simp [hP]
  · field_simp

/-! ## 2. The basins are all-pass on the ring -/

/-- [proved-standard; formal-checked] On the ring, `|āz − 1| = |z − a|`. -/
theorem norm_conj_mul_sub_one {z : ℂ} (hz : ‖z‖ = 1) (a : ℂ) : ‖conj a * z - 1‖ = ‖z - a‖ := by
  have hzz : z * conj z = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hz]
    simp
  have e : conj a * z - 1 = z * conj (a - z) := by
    rw [map_sub, mul_sub, hzz]
    ring
  rw [e, norm_mul, hz, one_mul, Complex.norm_conj, norm_sub_rev]

/-- [proved-standard; formal-checked] On the ring the zero factors and the reflected factors have one magnitude. -/
theorem norm_zeroProd_eq_norm_reflectProd {z : ℂ} (hz : ‖z‖ = 1) (Z : Multiset ℂ) :
    ‖zeroProd Z z‖ = ‖reflectProd Z z‖ := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih => rw [zeroProd_cons, reflectProd_cons, norm_mul, norm_mul, ih, norm_conj_mul_sub_one hz]

/-- [proved-standard; formal-checked] With every basin off the ring, no reflected factor vanishes on it. -/
theorem reflectProd_ne_zero {z : ℂ} (hz : ‖z‖ = 1) {Z : Multiset ℂ} (h : ∀ a ∈ Z, ‖a‖ ≠ 1) :
    reflectProd Z z ≠ 0 := by
  rw [← norm_ne_zero_iff, ← norm_zeroProd_eq_norm_reflectProd hz, norm_ne_zero_iff]
  exact zeroProd_ne_zero fun hzZ => h z hzZ hz

/-- [proved-standard; formal-checked] **`B` is all-pass**: `|B(z)| = 1` on the ring. -/
theorem norm_blaschke {z : ℂ} (hz : ‖z‖ = 1) {Z : Multiset ℂ} (h : ∀ a ∈ Z, ‖a‖ ≠ 1) :
    ‖blaschke Z z‖ = 1 := by
  rw [blaschke, norm_div, norm_zeroProd_eq_norm_reflectProd hz,
    div_self (norm_ne_zero_iff.2 (reflectProd_ne_zero hz h))]

/-- [proved-standard; formal-checked] The hidden basins stand off the ring. -/
theorem outer_off_circle (Z : Multiset ℂ) : ∀ a ∈ outer Z, ‖a‖ ≠ 1 :=
  fun _ ha => (Multiset.mem_filter.1 ha).2.ne'

/-- [proved-standard; formal-checked] **The magnitude face cannot see the basins**: `|H| = |H_min|` on the ring. -/
theorem norm_response_eq_norm_minPhase (c : ℂ) (Z P : Multiset ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖response c Z P z‖ = ‖minPhase c Z P z‖ := by
  rw [response_eq_minPhase_mul_blaschke c Z P z (reflectProd_ne_zero hz (outer_off_circle Z)), norm_mul,
    norm_blaschke hz (outer_off_circle Z), mul_one]

/-! ## 3. The minimum-phase face holds its zeros in the disk -/

/-- [proved-standard; formal-checked] `āz − 1 = ā(z − 1/ā)`, factor by factor. -/
theorem reflectProd_eq (Z : Multiset ℂ) (h : ∀ a ∈ Z, a ≠ 0) (z : ℂ) :
    reflectProd Z z = (Z.map conj).prod * zeroProd (Z.map reflect) z := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    have ha : conj a ≠ 0 := (map_ne_zero _).2 (h a (Multiset.mem_cons_self a Z))
    rw [reflectProd_cons, ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)), Multiset.map_cons,
      Multiset.prod_cons, Multiset.map_cons, zeroProd_cons, reflect]
    field_simp

/-- [proved-standard; formal-checked] `H_min` is the response with constant `c ∏ ā` and zeros
`inner Z + reflect(outer Z)`. -/
theorem minPhase_eq_response (c : ℂ) (Z P : Multiset ℂ) :
    minPhase c Z P = response (c * ((outer Z).map conj).prod) (inner Z + (outer Z).map reflect) P := by
  funext z
  have h0 : ∀ a ∈ outer Z, a ≠ 0 := fun a ha h => by
    have := (Multiset.mem_filter.1 ha).2
    rw [h, norm_zero] at this
    linarith
  rw [minPhase, response, reflectProd_eq _ h0, zeroProd_add]
  ring

/-- [proved-standard; formal-checked] The mirror of a hidden basin lies inside the disk. -/
theorem norm_reflect_lt_one {a : ℂ} (ha : 1 < ‖a‖) : ‖reflect a‖ < 1 := by
  rw [reflect, norm_inv, Complex.norm_conj]
  exact inv_lt_one_of_one_lt₀ ha

/-- [proved-standard; formal-checked] **`H_min` is minimum phase**: every zero of it lies in the closed disk. -/
theorem minPhase_zeros_le_one (Z : Multiset ℂ) : ∀ b ∈ inner Z + (outer Z).map reflect, ‖b‖ ≤ 1 := by
  intro b hb
  rcases Multiset.mem_add.1 hb with hb | hb
  · exact not_lt.1 (Multiset.mem_filter.1 hb).2
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    exact (norm_reflect_lt_one (Multiset.mem_filter.1 ha).2).le

/-! ## 4. The winding on the ring counts the basins inside -/

/-- [definition] `Σ_(a∈Z) (z − a)⁻¹`. -/
noncomputable def sumInv (Z : Multiset ℂ) (z : ℂ) : ℂ := (Z.map fun a => (z - a)⁻¹).sum

/-- [definition] The winding of a response on the ring, `(2πi)⁻¹ ∮_(|z|=1) H′/H`. -/
noncomputable def winding (f : ℂ → ℂ) : ℂ := (2 * π * I)⁻¹ * ∮ z in C(0, 1), logDeriv f z

theorem sumInv_zero : sumInv 0 = fun _ => 0 := by
  funext z
  simp [sumInv]

theorem sumInv_cons (a : ℂ) (Z : Multiset ℂ) : sumInv (a ::ₘ Z) = fun z => (z - a)⁻¹ + sumInv Z z := by
  funext z
  simp [sumInv]

/-- [proved-standard; formal-checked] `∏ (z − a)` is differentiable. -/
theorem differentiable_zeroProd (Z : Multiset ℂ) : Differentiable ℂ (zeroProd Z) := by
  induction Z using Multiset.induction_on with
  | empty =>
    rw [show zeroProd 0 = fun _ => (1 : ℂ) from funext zeroProd_zero]
    exact differentiable_const 1
  | cons a Z ih =>
    rw [show zeroProd (a ::ₘ Z) = fun z => (z - a) * zeroProd Z z from funext (zeroProd_cons a Z)]
    exact (differentiable_id.sub_const a).mul ih

/-- [proved-standard; formal-checked] `(∏ (z − a))′/∏ (z − a) = Σ (z − a)⁻¹` off the zeros. -/
theorem logDeriv_zeroProd {Z : Multiset ℂ} {z : ℂ} (h : z ∉ Z) : logDeriv (zeroProd Z) z = sumInv Z z := by
  induction Z using Multiset.induction_on with
  | empty =>
    rw [show zeroProd 0 = fun _ => (1 : ℂ) from funext zeroProd_zero, logDeriv_const, sumInv_zero]
    rfl
  | cons a Z ih =>
    rw [Multiset.mem_cons, not_or] at h
    have hm := logDeriv_mul (f := fun z => z - a) (g := zeroProd Z) z (sub_ne_zero.2 h.1)
      (zeroProd_ne_zero h.2) ((differentiable_id.sub_const a) z) (differentiable_zeroProd Z z)
    rw [show zeroProd (a ::ₘ Z) = fun z => (z - a) * zeroProd Z z from funext (zeroProd_cons a Z), hm, ih h.2,
      sumInv_cons]
    simp [logDeriv_apply]

/-- [proved-standard; formal-checked] `H′/H = Σ_Z (z − a)⁻¹ − Σ_P (z − p)⁻¹` off the zeros and poles. -/
theorem logDeriv_response {c : ℂ} (hc : c ≠ 0) {Z P : Multiset ℂ} {z : ℂ} (hZ : z ∉ Z) (hP : z ∉ P) :
    logDeriv (response c Z P) z = sumInv Z z - sumInv P z := by
  have h1 := logDeriv_div (f := fun z => c * zeroProd Z z) (g := zeroProd P) z
    (mul_ne_zero hc (zeroProd_ne_zero hZ)) (zeroProd_ne_zero hP)
    (((differentiable_zeroProd Z).const_mul c) z) (differentiable_zeroProd P z)
  have h2 := logDeriv_const_mul (f := zeroProd Z) z c hc
  beta_reduce at h1
  rw [show response c Z P = fun z => c * zeroProd Z z / zeroProd P z from rfl, h1, h2, logDeriv_zeroProd hZ,
    logDeriv_zeroProd hP]

/-- [proved-standard; formal-checked] `(z − a)⁻¹` is integrable on the ring when `a` is off it. -/
theorem circleIntegrable_sub_inv {a : ℂ} (ha : ‖a‖ ≠ 1) : CircleIntegrable (fun z => (z - a)⁻¹) 0 1 :=
  circleIntegrable_sub_inv_iff.2 (Or.inr (by simpa using ha))

/-- [proved-standard; formal-checked] A basin inside the disk winds the ring once: `∮ (z − a)⁻¹ = 2πi`. -/
theorem circleIntegral_sub_inv_inside {a : ℂ} (ha : ‖a‖ < 1) : (∮ z in C(0, 1), (z - a)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (by rwa [mem_ball_zero_iff])

/-- [proved-standard; formal-checked] A basin outside does not wind it: `∮ (z − a)⁻¹ = 0` (Cauchy). -/
theorem circleIntegral_sub_inv_outside {a : ℂ} (ha : 1 < ‖a‖) : (∮ z in C(0, 1), (z - a)⁻¹) = 0 := by
  have hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z - a ≠ 0 := fun z hz h => by
    rw [sub_eq_zero] at h
    rw [h] at hz
    linarith
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one Set.countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => hne z (mem_closedBall_zero_iff.1 hz)
  · intro z hz
    exact (differentiableAt_id.sub_const a).inv (hne z (mem_ball_zero_iff.1 hz.1).le)

/-- [proved-standard; formal-checked] `Σ (z − a)⁻¹` is integrable on the ring when every `a` is off it. -/
theorem circleIntegrable_sumInv {Z : Multiset ℂ} (h : ∀ a ∈ Z, ‖a‖ ≠ 1) : CircleIntegrable (sumInv Z) 0 1 := by
  induction Z using Multiset.induction_on with
  | empty =>
    rw [sumInv_zero]
    exact circleIntegrable_const 0 0 1
  | cons a Z ih =>
    rw [sumInv_cons]
    exact (circleIntegrable_sub_inv (h a (Multiset.mem_cons_self a Z))).add
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/-- [proved-standard; formal-checked] `∮ Σ (z − a)⁻¹ = 2πi · #{a inside}`. -/
theorem circleIntegral_sumInv {Z : Multiset ℂ} (h : ∀ a ∈ Z, ‖a‖ ≠ 1) :
    (∮ z in C(0, 1), sumInv Z z) = 2 * π * I * ((Z.filter fun a => ‖a‖ < 1).card : ℂ) := by
  induction Z using Multiset.induction_on with
  | empty => simp [sumInv, circleIntegral]
  | cons a Z ih =>
    have hZ : ∀ b ∈ Z, ‖b‖ ≠ 1 := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    have ha := h a (Multiset.mem_cons_self a Z)
    simp only [sumInv_cons]
    rw [circleIntegral.integral_add (circleIntegrable_sub_inv ha) (circleIntegrable_sumInv hZ), ih hZ]
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · rw [circleIntegral_sub_inv_inside hlt, Multiset.filter_cons_of_pos (p := fun a : ℂ => ‖a‖ < 1) Z hlt, Multiset.card_cons]
      push_cast
      ring
    · rw [circleIntegral_sub_inv_outside hgt, Multiset.filter_cons_of_neg (p := fun a : ℂ => ‖a‖ < 1) Z (not_lt.2 hgt.le), zero_add]

/-- [proved-standard; formal-checked] **The argument principle for a factored response**: with `c ≠ 0` and every zero
and pole off the ring, the winding is the count of zeros inside less the count of poles inside. -/
theorem winding_response {c : ℂ} (hc : c ≠ 0) {Z P : Multiset ℂ} (hZ : ∀ a ∈ Z, ‖a‖ ≠ 1)
    (hP : ∀ p ∈ P, ‖p‖ ≠ 1) :
    winding (response c Z P) =
      ((Z.filter fun a => ‖a‖ < 1).card : ℂ) - ((P.filter fun p => ‖p‖ < 1).card : ℂ) := by
  have hcongr : (∮ z in C(0, 1), logDeriv (response c Z P) z) = ∮ z in C(0, 1), (sumInv Z z - sumInv P z) := by
    apply circleIntegral.integral_congr zero_le_one
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    exact logDeriv_response hc (fun h => hZ z h hz1) (fun h => hP z h hz1)
  rw [winding, hcongr, circleIntegral.integral_sub (circleIntegrable_sumInv hZ) (circleIntegrable_sumInv hP),
    circleIntegral_sumInv hZ, circleIntegral_sumInv hP]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ## 5. The degree of `B` is the winding deficit -/

/-- [proved-standard; formal-checked] With every zero off the ring, the zeros inside are the inner ones. -/
theorem filter_lt_one_eq_inner {Z : Multiset ℂ} (hZ : ∀ a ∈ Z, ‖a‖ ≠ 1) :
    (Z.filter fun a => ‖a‖ < 1) = inner Z := by
  rw [inner]
  apply Multiset.filter_congr
  intro a ha
  constructor
  · intro h; exact not_lt.2 h.le
  · intro h; exact lt_of_le_of_ne (not_lt.1 h) (hZ a ha)

/-- [proved-standard; formal-checked] `H_min` winds once for every zero of `H`: its zeros are all inside. -/
theorem winding_minPhase {c : ℂ} (hc : c ≠ 0) {Z P : Multiset ℂ} (hZ : ∀ a ∈ Z, ‖a‖ ≠ 1)
    (hP : ∀ p ∈ P, ‖p‖ ≠ 1) :
    winding (minPhase c Z P) = (Z.card : ℂ) - ((P.filter fun p => ‖p‖ < 1).card : ℂ) := by
  have hconj : ((outer Z).map conj).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h
    obtain ⟨a, ha, h0⟩ := Multiset.mem_map.1 h
    rw [map_eq_zero] at h0
    have := (Multiset.mem_filter.1 ha).2
    rw [h0, norm_zero] at this
    linarith
  have hW : ∀ b ∈ inner Z + (outer Z).map reflect, ‖b‖ ≠ 1 := by
    intro b hb
    rcases Multiset.mem_add.1 hb with hb | hb
    · exact hZ b (Multiset.mem_of_mem_filter hb)
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
      exact (norm_reflect_lt_one (Multiset.mem_filter.1 ha).2).ne
  rw [minPhase_eq_response, winding_response (mul_ne_zero hc hconj) hW hP, Multiset.filter_add,
    Multiset.filter_map]
  have hin : ((inner Z).filter fun a => ‖a‖ < 1) = inner Z := by
    rw [Multiset.filter_eq_self]
    intro a ha
    exact lt_of_le_of_ne (not_lt.1 (Multiset.mem_filter.1 ha).2) (hZ a (Multiset.mem_of_mem_filter ha))
  have hout : ((outer Z).filter ((fun a => ‖a‖ < 1) ∘ reflect)) = outer Z := by
    rw [Multiset.filter_eq_self]
    intro a ha
    exact norm_reflect_lt_one (Multiset.mem_filter.1 ha).2
  rw [hin, hout, Multiset.card_add, Multiset.card_map]
  have hcard : (inner Z).card + (outer Z).card = Z.card := by
    rw [← Multiset.card_add, inner, outer, add_comm, Multiset.filter_add_not]
  rw [← hcard, Nat.cast_add]

/-- [proved-standard; formal-checked] **The degree of `B` is the winding deficit**:
`winding(H_min) − winding(H) = deg B`, the count of hidden basins. -/
theorem winding_deficit {c : ℂ} (hc : c ≠ 0) {Z P : Multiset ℂ} (hZ : ∀ a ∈ Z, ‖a‖ ≠ 1)
    (hP : ∀ p ∈ P, ‖p‖ ≠ 1) :
    winding (minPhase c Z P) - winding (response c Z P) = ((outer Z).card : ℂ) := by
  rw [winding_minPhase hc hZ hP, winding_response hc hZ hP, filter_lt_one_eq_inner hZ]
  have hcard : (inner Z).card + (outer Z).card = Z.card := by
    rw [← Multiset.card_add, inner, outer, add_comm, Multiset.filter_add_not]
  rw [← hcard]
  push_cast
  ring

/-- [proved-standard; formal-checked] `B` is a response: constant `(∏ ā)⁻¹`, zeros the basins, poles their mirrors. -/
theorem blaschke_eq_response (Z : Multiset ℂ) (h : ∀ a ∈ Z, a ≠ 0) :
    blaschke Z = response ((Z.map conj).prod)⁻¹ Z (Z.map reflect) := by
  funext z
  rw [blaschke, response, reflectProd_eq Z h]
  ring

/-- [proved-standard; formal-checked] **`B` winds backwards once per basin**: `winding(B) = −deg B`. -/
theorem winding_blaschke (Z : Multiset ℂ) : winding (blaschke (outer Z)) = -((outer Z).card : ℂ) := by
  have h0 : ∀ a ∈ outer Z, a ≠ 0 := fun a ha h => by
    have := (Multiset.mem_filter.1 ha).2
    rw [h, norm_zero] at this
    linarith
  have hconj : ((outer Z).map conj).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, h0'⟩ := Multiset.mem_map.1 hm
    rw [map_eq_zero] at h0'
    exact h0 a ha h0'
  have hR : ∀ b ∈ (outer Z).map reflect, ‖b‖ ≠ 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    exact (norm_reflect_lt_one (Multiset.mem_filter.1 ha).2).ne
  rw [blaschke_eq_response _ h0, winding_response (inv_ne_zero hconj) (outer_off_circle Z) hR,
    Multiset.filter_map]
  have hnone : ((outer Z).filter fun a => ‖a‖ < 1) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro a ha
    exact not_lt.2 (Multiset.mem_filter.1 ha).2.le
  have hall : ((outer Z).filter ((fun a => ‖a‖ < 1) ∘ reflect)) = outer Z := by
    rw [Multiset.filter_eq_self]
    intro a ha
    exact norm_reflect_lt_one (Multiset.mem_filter.1 ha).2
  rw [hnone, hall, Multiset.card_map]
  simp

/-- [proved-standard; formal-checked] The windings add along the factorization:
`winding(H) = winding(H_min) + winding(B)`. -/
theorem winding_response_eq_add {c : ℂ} (hc : c ≠ 0) {Z P : Multiset ℂ} (hZ : ∀ a ∈ Z, ‖a‖ ≠ 1)
    (hP : ∀ p ∈ P, ‖p‖ ≠ 1) :
    winding (response c Z P) = winding (minPhase c Z P) + winding (blaschke (outer Z)) := by
  rw [winding_blaschke, ← winding_deficit hc hZ hP]
  ring

/-! ## 6. The record's witness -/

theorem outer_two : outer {(2 : ℂ)} = {2} := by
  rw [outer, Multiset.filter_singleton, if_pos (by norm_num)]

theorem inner_two : inner {(2 : ℂ)} = 0 := by
  rw [inner, Multiset.filter_singleton, if_neg (by norm_num)]
  rfl

/-- [proved-standard; formal-checked] **The witness's minimum-phase face**: for `H = (z − 2)/(z − 1/3)`,
`H_min = (2z − 1)/(z − 1/3)`. -/
theorem witness_minPhase (z : ℂ) : minPhase 1 {2} {1 / 3} z = (2 * z - 1) / (z - 1 / 3) := by
  rw [minPhase, inner_two, outer_two]
  simp [zeroProd, reflectProd, map_ofNat]

/-- [proved-standard; formal-checked] **The witness's basin**: `B = (z − 2)/(2z − 1)`. -/
theorem witness_blaschke (z : ℂ) : blaschke (outer {(2 : ℂ)}) z = (z - 2) / (2 * z - 1) := by
  rw [outer_two]
  simp [blaschke, zeroProd, reflectProd, map_ofNat]

/-- [proved-standard; formal-checked] **The witness's windings**: `H` winds `−1`, `H_min` winds `0`, and the deficit is
the one hidden basin. -/
theorem witness_windings :
    winding (response 1 {(2 : ℂ)} {1 / 3}) = -1 ∧ winding (minPhase 1 {(2 : ℂ)} {1 / 3}) = 0 := by
  have hZ : ∀ a ∈ ({2} : Multiset ℂ), ‖a‖ ≠ 1 := by
    intro a ha
    rw [Multiset.mem_singleton] at ha
    subst ha
    norm_num
  have hP : ∀ p ∈ ({1 / 3} : Multiset ℂ), ‖p‖ ≠ 1 := by
    intro p hp
    rw [Multiset.mem_singleton] at hp
    subst hp
    norm_num
  have h2 : (({(2 : ℂ)} : Multiset ℂ).filter fun a => ‖a‖ < 1) = 0 := by
    rw [Multiset.filter_singleton, if_neg (by norm_num)]
    rfl
  have h3 : (({(1 / 3 : ℂ)} : Multiset ℂ).filter fun a => ‖a‖ < 1) = {1 / 3} := by
    rw [Multiset.filter_singleton, if_pos (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [winding_response one_ne_zero hZ hP, h2, h3]
    simp
  · rw [winding_minPhase one_ne_zero hZ hP, h3]
    simp

end Holonics.Transport.MinimumPhase
