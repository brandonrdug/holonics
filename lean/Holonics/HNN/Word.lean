import Holonics.HNN.Propagation

/-!
# HNN.Word: the ring's element and the power of one tick

[definition] Rebuild step 4 (#73), campaign 1, design item 1 (`docs/plans/THE_REBUILD.md`,
"Step 4 design: the HNN law"). A word is one evaluation of the ticks at one cut's fixed operands; it
opens at zero change and releases the change at its end. Within a word each ring's element is the
midpoint (Cayley) step of its reaction at the sheet-class operands,

```text
(I − ½K_r) s_r′ = (I + ½K_r) b_r + W_c,r c_r,   K_r = W_s,r + Σ_ρ σ_ρ,r A_ρ,r,
b_r = 2 v_r − s_r (the junction's storage output),   c_r = v_r − s_r (the contrast),
```

written in the drive form `s′ − b = K x̄ + W_c c`, `x̄ = ½(b + s′)` of `Holon/Cayley.drive_balance`.
`W_s` is passive, the slices `A_ρ` are skew, the sheet classes `σ_ρ ∈ {±1}` are read from the
standing, and `W_c` is the learned contrast port.

[proved-derived; formal-checked] What is proved.

1. **Isometry.** With `W_s = 0` and `W_c = 0` the element is lossless, `|s′| = |b|`, however large
   the slices (`reaction_stage_isometry`); a passive `W_s` or a nonzero `W_c` breaks it
   (`reaction_stage_isometry_needs_both`).
2. **Balance.** `½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩`, the skew slices contributing zero
   (`reaction_stage_balance`, composing `drive_balance`).
3. **The contrast port is active.** For `W_c c ≠ 0` an explicit input makes its power
   `⟨x̄, W_c c⟩` and the stage's energy change both positive, so the element is passive for every
   input exactly when `W_c = 0` (`contrastPort_active`).
4. **The element's adjoint.** With `u = (I − ½K)^(−*) g`, the tangent map pairs as
   `⟨g, δs′⟩ = ⟨2u − g, δb⟩ + ⟨W_c* u, δc⟩ + Σ_ρ δσ_ρ ⟨u, A_ρ x̄⟩`: the drive covector
   `Cayley.driveCovector`, the contrast covector and the slice covectors
   (`reaction_stage_adjoint`); a finite change of one sheet class moves the reading by exactly
   `ε⟨u₁, A_ρ x̄⟩`, with `u₁` the adjoint at the changed classes (`reaction_stage_slice_difference`).
5. **The tick's global power balance** (R2 C1, R3 C1). With
   `P = (h/4)[Σ_r Y_r|s_r|² + Σ_(r,a) G_a|a_(r←a)|²] + Σ_a E_a`, one tick of junctions, elements and
   transits changes `P` by exactly
   `−h Σ_a ⟨ω_a, D_a ω_a⟩ + (h/2) Σ_r Y_r⟨x̄_r, W_s,r x̄_r⟩ + Π_c`,
   `Π_c = (h/2) Σ_r Y_r ⟨x̄_r, W_c,r c_r⟩` (`word_tick_balance`): the junction Swing contributes
   zero (`Propagation.junctionSwing_isometry`), the element and the transit their balances
   (`reaction_stage_balance`, `Propagation.transit_balance_waves`). One conductance per contact,
   read at both ends, is load-bearing: weights read per ring at the two ends of a transmitting
   contact do not conserve the power (`word_tick_balance_needs_one_conductance`).
6. **The tick as a map, and its cone.** For an admissible medium (`Medium.Admissible`: passive
   `W_s`, skew slices, `C, D, K ⪰ 0`, positive admittances, conductances and tick length, channel
   embeddings) the local solves exist and are unique (`elementSolve_spec`, `transitSolve_spec`), so
   `fieldTick` is the tick, and its power obeys the balance (`fieldTick_balance`). A block of its
   output vanishes when the block and every block one tick carries into it vanished
   (`fieldTick_local`), so a change supported on blocks `Z` is supported after `t` ticks within `t`
   hops of `Z` on the word's ring/contact block graph `blockAdj` (`word_tick_cone`).

[open] The diamond and retention laws (`Propagation` §4, `Retention`) are proved for the abstract
`BlockOp` word, not for `fieldTick`. Writing `fieldTick` as a linear block operator family on
`blockAdj` (linear in the change at fixed operands, `Sparse blockAdj`), so that
`Propagation.release_past_diamond` and `Retention.deposit_descends` apply to the concrete word
verbatim, is owed in #62, "Step 4 (#73) owed: the diamond on the concrete tick".

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Word

open Holonics.HolonCore
open Holonics.Geometry.AffineSwing
open Holonics.HNN.Propagation
open scoped BigOperators

/-! ## 1. The ring's element -/

section Element

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Cn : Type*} [NormedAddCommGroup Cn] [InnerProductSpace ℝ Cn]
variable {ρ : Type*} [Fintype ρ]

/-- [definition] **The ring's element step** at the sheet-class operands, in the drive form
`s′ − b = K x̄ + W_c c`, `x̄ = ½(b + s′)`, `K = W_s + Σ_ρ σ_ρ A_ρ`. It is the relation
`(I − ½K) s′ = (I + ½K) b + W_c c` (`elementStep_iff`). -/
def ElementStep (Ws : E →L[ℝ] E) (A : ρ → E →L[ℝ] E) (σ : ρ → ℝ) (Wc : Cn →L[ℝ] E)
    (b : E) (c : Cn) (s' : E) : Prop :=
  s' - b = devK Ws A σ ((1 / 2 : ℝ) • (b + s')) + Wc c

/-- [definition] The element's midpoint `x̄ = ½(b + s′)`. -/
def midpoint (b s' : E) : E := (1 / 2 : ℝ) • (b + s')

omit [Fintype ρ] in
theorem elementStep_iff_aux (K : E →L[ℝ] E) (b s' w : E) :
    s' - b = K ((1 / 2 : ℝ) • (b + s')) + w ↔
      s' - (1 / 2 : ℝ) • K s' = b + (1 / 2 : ℝ) • K b + w := by
  rw [map_smul, map_add, smul_add]
  constructor <;> intro h <;> [skip; skip]
  · rw [← sub_eq_zero] at h ⊢
    rw [← h]; abel
  · rw [← sub_eq_zero] at h ⊢
    rw [← h]; abel

/-- [proved-derived; formal-checked] The drive form is the Cayley relation
`(I − ½K) s′ = (I + ½K) b + W_c c`. -/
theorem elementStep_iff (Ws : E →L[ℝ] E) (A : ρ → E →L[ℝ] E) (σ : ρ → ℝ) (Wc : Cn →L[ℝ] E)
    (b : E) (c : Cn) (s' : E) :
    ElementStep Ws A σ Wc b c s' ↔
      s' - (1 / 2 : ℝ) • devK Ws A σ s' = b + (1 / 2 : ℝ) • devK Ws A σ b + Wc c :=
  elementStep_iff_aux _ b s' _

/-- [proved-derived; formal-checked] **The element's balance** (R3 C1):
`½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩`; the skew slices contribute zero. -/
theorem reaction_stage_balance {Ws : E →L[ℝ] E} {A : ρ → E →L[ℝ] E}
    (hA : ∀ r v, inner ℝ v (A r v) = 0) (σ : ρ → ℝ) (Wc : Cn →L[ℝ] E) {b s' : E} {c : Cn}
    (hstep : ElementStep Ws A σ Wc b c s') :
    (1 / 2 : ℝ) * ‖s'‖ ^ 2 - (1 / 2 : ℝ) * ‖b‖ ^ 2 =
      inner ℝ (midpoint b s') (Ws (midpoint b s')) + inner ℝ (midpoint b s') (Wc c) :=
  drive_balance Ws A hA σ hstep

/-- [proved-derived; formal-checked] **The lossless element** (`Cay_r`): with `W_s = 0` and
`W_c = 0`, `|s′| = |b|` for every sheet-class configuration and every slice magnitude. -/
theorem reaction_stage_isometry {A : ρ → E →L[ℝ] E} (hA : ∀ r v, inner ℝ v (A r v) = 0)
    (σ : ρ → ℝ) {b s' : E} {c : Cn} (hstep : ElementStep 0 A σ (0 : Cn →L[ℝ] E) b c s') :
    ‖s'‖ = ‖b‖ := by
  have h := reaction_stage_balance hA σ 0 hstep
  simp only [_root_.zero_apply, inner_zero_right, add_zero] at h
  have hsq : ‖s'‖ ^ 2 = ‖b‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- [counterexample; formal-checked] **Both hypotheses of the isometry are load-bearing.** On `ℝ`
with no slices: the passive `W_s = −¼` takes `b = 1` to `s′ = 7/9` (a strict loss), and the contrast
port `W_c = 1` at `c = 1` takes `b = 0` to `s′ = 1` (a gain). -/
theorem reaction_stage_isometry_needs_both :
    ElementStep ((-1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (fun _ : Empty => 0) (fun _ => 0)
        (0 : ℝ →L[ℝ] ℝ) 1 0 (7 / 9) ∧ ‖(7 / 9 : ℝ)‖ < ‖(1 : ℝ)‖ ∧
      ElementStep (0 : ℝ →L[ℝ] ℝ) (fun _ : Empty => 0) (fun _ => 0)
        (ContinuousLinearMap.id ℝ ℝ) 0 1 1 ∧ ‖(0 : ℝ)‖ < ‖(1 : ℝ)‖ := by
  refine ⟨?_, by norm_num, ?_, by norm_num⟩
  · simp only [ElementStep, devK, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      _root_.smul_apply, ContinuousLinearMap.id_apply, _root_.zero_apply,
      smul_eq_mul]
    norm_num
  · simp only [ElementStep, devK, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      _root_.zero_apply, ContinuousLinearMap.id_apply, zero_add]
    norm_num

/-- [proved-derived; formal-checked] **The contrast port is an active element relation with its
power** (R3 C1). For passive `W_s` and skew slices: whenever `W_c c ≠ 0`, the input
`x̄ = t W_c c`, `t = |w|²/(|w|² + |⟨w, W_s w⟩|)`, `b = x̄ − ½K x̄ − ½W_c c`, `s′ = 2x̄ − b`
satisfies the element step with contrast power `⟨x̄, W_c c⟩ > 0` and energy change
`½|s′|² − ½|b|² > 0`. Hence the element is passive for every input (`|s′| ≤ |b|` whenever the step
holds) exactly when `W_c = 0`. -/
theorem contrastPort_active {Ws : E →L[ℝ] E} (hWs : ∀ v, inner ℝ v (Ws v) ≤ 0)
    {A : ρ → E →L[ℝ] E} (hA : ∀ r v, inner ℝ v (A r v) = 0) (σ : ρ → ℝ) (Wc : Cn →L[ℝ] E) :
    (∀ c : Cn, Wc c ≠ 0 → ∃ b s' : E, ElementStep Ws A σ Wc b c s' ∧
        0 < inner ℝ (midpoint b s') (Wc c) ∧ 0 < (1 / 2 : ℝ) * ‖s'‖ ^ 2 - (1 / 2 : ℝ) * ‖b‖ ^ 2) ∧
      ((∀ (b s' : E) (c : Cn), ElementStep Ws A σ Wc b c s' → ‖s'‖ ≤ ‖b‖) ↔ Wc = 0) := by
  have hactive : ∀ c : Cn, Wc c ≠ 0 → ∃ b s' : E, ElementStep Ws A σ Wc b c s' ∧
      0 < inner ℝ (midpoint b s') (Wc c) ∧
        0 < (1 / 2 : ℝ) * ‖s'‖ ^ 2 - (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
    intro c hc
    set w := Wc c
    set a := -inner ℝ w (Ws w)
    set nn := ‖w‖ ^ 2
    have ha : 0 ≤ a := by simp only [a]; linarith [hWs w]
    have hnn : 0 < nn := by positivity
    set t := nn / (nn + a)
    have ht : 0 < t := div_pos hnn (by linarith)
    set xb : E := t • w
    set K := devK Ws A σ
    refine ⟨xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w,
      xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w, ?_, ?_⟩
    · have hmid : (1 / 2 : ℝ) • (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w +
          (xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w)) = xb := by
        rw [show xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w + (xb + (1 / 2 : ℝ) • K xb +
          (1 / 2 : ℝ) • w) = (2 : ℝ) • xb by rw [two_smul]; abel, smul_smul]
        norm_num
      rw [ElementStep, hmid]
      rw [show xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w -
          (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w) = (2 : ℝ) • ((1 / 2 : ℝ) • K xb) +
            (2 : ℝ) • ((1 / 2 : ℝ) • w) by rw [two_smul, two_smul]; abel, smul_smul, smul_smul]
      norm_num
      rfl
    · have hmid : midpoint (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w)
          (xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w) = xb := by
        rw [midpoint, show xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w + (xb + (1 / 2 : ℝ) • K xb +
          (1 / 2 : ℝ) • w) = (2 : ℝ) • xb by rw [two_smul]; abel, smul_smul]
        norm_num
      have hstep : ElementStep Ws A σ Wc (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w) c
          (xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w) := by
        rw [ElementStep]
        rw [show (1 / 2 : ℝ) • (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w +
          (xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w)) = xb from hmid]
        rw [show xb + (1 / 2 : ℝ) • K xb + (1 / 2 : ℝ) • w -
            (xb - (1 / 2 : ℝ) • K xb - (1 / 2 : ℝ) • w) = (2 : ℝ) • ((1 / 2 : ℝ) • K xb) +
              (2 : ℝ) • ((1 / 2 : ℝ) • w) by rw [two_smul, two_smul]; abel, smul_smul, smul_smul]
        norm_num
        rfl
      have hbal := reaction_stage_balance hA σ Wc hstep
      rw [hmid] at hbal ⊢
      have hpow : inner ℝ xb w = t * nn := by
        simp only [xb, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq, nn]
      have hWsx : inner ℝ xb (Ws xb) = -(t ^ 2 * a) := by
        simp only [xb, map_smul, inner_smul_left, inner_smul_right, conj_trivial, a]
        ring
      refine ⟨by rw [hpow]; positivity, ?_⟩
      rw [hbal, hpow, hWsx]
      have : t * (nn + a) = nn := by
        simp only [t]; field_simp
      have h2 : -(t ^ 2 * a) + t * nn = t ^ 2 * nn := by linear_combination (-t) * this
      rw [h2]
      positivity
  refine ⟨hactive, ⟨fun hpass => ?_, fun hWc b s' c hstep => ?_⟩⟩
  · by_contra hne
    obtain ⟨c, hc⟩ : ∃ c, Wc c ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (ContinuousLinearMap.ext hall)
    obtain ⟨b, s', hstep, -, hgain⟩ := hactive c hc
    have := hpass b s' c hstep
    have : ‖s'‖ ^ 2 ≤ ‖b‖ ^ 2 := by gcongr
    linarith
  · have hbal := reaction_stage_balance hA σ Wc hstep
    rw [hWc, _root_.zero_apply, inner_zero_right, add_zero] at hbal
    have := hWs (midpoint b s')
    have hsq : ‖s'‖ ^ 2 ≤ ‖b‖ ^ 2 := by linarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Cn]

/-- [proved-derived; formal-checked] **The element's adjoint** (R3 C1). Let
`u − ½K* u = g` (`u = (I − ½K)^(−*) g`). A tangent `(δb, δc, δσ, δs′)` of the element step at the
midpoint `x̄`, `δs′ − δb = K(½(δb + δs′)) + W_c δc + Σ_ρ δσ_ρ A_ρ x̄`, pairs with `g` as
`⟨g, δs′⟩ = ⟨2u − g, δb⟩ + ⟨W_c* u, δc⟩ + Σ_ρ δσ_ρ ⟨u, A_ρ x̄⟩`: the drive covector
`Cayley.driveCovector u g`, the contrast covector `W_c* u` and the slice covectors
`⟨u, A_ρ x̄⟩`. -/
theorem reaction_stage_adjoint (Ws : E →L[ℝ] E) (A : ρ → E →L[ℝ] E) (σ : ρ → ℝ)
    (Wc : Cn →L[ℝ] E) {u g : E}
    (hu : u - (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint (devK Ws A σ)) u = g)
    {xb δb δs' : E} {δc : Cn} {δσ : ρ → ℝ}
    (htangent : δs' - δb = devK Ws A σ ((1 / 2 : ℝ) • (δb + δs')) + Wc δc +
      ∑ r, δσ r • A r xb) :
    inner ℝ g δs' = inner ℝ (driveCovector u g) δb +
      inner ℝ (ContinuousLinearMap.adjoint Wc u) δc + ∑ r, δσ r * inner ℝ u (A r xb) := by
  set K := devK Ws A σ
  have hrel : δs' - (1 / 2 : ℝ) • K δs' = δb + (1 / 2 : ℝ) • K δb + (Wc δc + ∑ r, δσ r • A r xb) :=
    (elementStep_iff_aux K δb δs' _).mp (by rw [htangent, add_assoc])
  have hKadj : ∀ x y : E, inner ℝ (ContinuousLinearMap.adjoint K x) y = inner ℝ x (K y) :=
    fun x y => ContinuousLinearMap.adjoint_inner_left K y x
  have h1 : inner ℝ g δs' = inner ℝ u (δs' - (1 / 2 : ℝ) • K δs') := by
    rw [← hu, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hKadj]
    simp
  have h2 : inner ℝ (u - g) δb = (1 / 2 : ℝ) * inner ℝ u (K δb) := by
    have hug : u - g = (1 / 2 : ℝ) • ContinuousLinearMap.adjoint K u := by
      rw [← hu, sub_sub_cancel]
    rw [hug, inner_smul_left, hKadj, conj_trivial]
  rw [h1, hrel]
  simp only [inner_add_right, inner_smul_right, inner_sum, ContinuousLinearMap.adjoint_inner_left,
    driveCovector, inner_sub_left, inner_smul_left, conj_trivial]
  rw [inner_sub_left] at h2
  linarith

omit [FiniteDimensional ℝ Cn] in
/-- [proved-derived; formal-checked] **A finite change of one sheet class** (the slice covector
at the declared lock chart). If `s′` and `s₁′` are the element steps at classes `σ` and
`σ₁ = σ + ε e_ρ` from the same `b, c`, and `u₁ − ½K₁* u₁ = g` at the changed classes, then
`⟨g, s₁′ − s′⟩ = ε ⟨u₁, A_ρ x̄⟩` exactly, with `x̄` the base midpoint. -/
theorem reaction_stage_slice_difference [DecidableEq ρ] (Ws : E →L[ℝ] E) (A : ρ → E →L[ℝ] E)
    (σ : ρ → ℝ) (Wc : Cn →L[ℝ] E) (r₀ : ρ) (ε : ℝ) {b s' s₁' u₁ g : E} {c : Cn}
    (hstep : ElementStep Ws A σ Wc b c s')
    (hstep₁ : ElementStep Ws A (σ + ε • Pi.single r₀ 1) Wc b c s₁')
    (hu₁ : u₁ - (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint (devK Ws A (σ + ε • Pi.single r₀ 1))) u₁ = g) :
    inner ℝ g (s₁' - s') = ε * inner ℝ u₁ (A r₀ (midpoint b s')) := by
  set K₁ := devK Ws A (σ + ε • Pi.single r₀ 1) with hK₁
  have hK : K₁ = devK Ws A σ + ε • A r₀ := by
    have hsum : ∑ r, (σ + ε • (Pi.single r₀ 1 : ρ → ℝ)) r • A r = ∑ r, σ r • A r + ε • A r₀ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single r₀ (fun r _ hr => by simp [Pi.single_eq_of_ne hr]) (by simp)]
      simp
    rw [hK₁, devK, devK, hsum, add_assoc]
  have e1 : s₁' - b = K₁ (midpoint b s₁') + Wc c := hstep₁
  have e0 : s' - b = devK Ws A σ (midpoint b s') + Wc c := hstep
  have hx : midpoint b s₁' - (1 / 2 : ℝ) • (s₁' - s') = midpoint b s' := by
    simp only [midpoint]
    module
  have hdiff : (s₁' - s') - (1 / 2 : ℝ) • K₁ (s₁' - s') = ε • A r₀ (midpoint b s') := by
    calc (s₁' - s') - (1 / 2 : ℝ) • K₁ (s₁' - s')
        = (s₁' - b) - (s' - b) - (1 / 2 : ℝ) • K₁ (s₁' - s') := by abel
      _ = K₁ (midpoint b s₁') - devK Ws A σ (midpoint b s') - (1 / 2 : ℝ) • K₁ (s₁' - s') := by
          rw [e1, e0]; abel
      _ = K₁ (midpoint b s₁' - (1 / 2 : ℝ) • (s₁' - s')) - devK Ws A σ (midpoint b s') := by
          simp only [map_sub, map_smul]; abel
      _ = ε • A r₀ (midpoint b s') := by
          rw [hx, hK, _root_.add_apply, add_sub_cancel_left]
          rfl
  have hKadj : ∀ x y : E, inner ℝ (ContinuousLinearMap.adjoint K₁ x) y = inner ℝ x (K₁ y) :=
    fun x y => ContinuousLinearMap.adjoint_inner_left K₁ y x
  have := congrArg (fun v => inner ℝ u₁ v) hdiff
  rw [inner_sub_right, inner_smul_right, inner_smul_right] at this
  rw [← hu₁, inner_sub_left, inner_smul_left, hKadj, conj_trivial]
  linarith

end Element

/-! ## 2. One tick of a field and its global power -/

section Tick

variable {Ring Contact ρ : Type*} [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [Fintype ρ]
variable {V : Ring → Type*} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type*} [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)]
  [∀ a, FiniteDimensional ℝ (Ch a)]
variable (endRing : Contact × Bool → Ring)

/-- [definition] The contact ports of ring `r`: the ends `(a, g-end)` or `(a, h-end)` of the
contacts `a` at `r` (`true` is the contact's `g` end, `false` its `h` end). -/
abbrev Port (r : Ring) := {e : Contact × Bool // endRing e = r}

/-- [definition] The arriving wave `a_(r←a)` at a port of ring `r`, read in ring `r`'s nodes. -/
def portWave (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring) (p : Port endRing r) : V r :=
  p.2 ▸ arr p.1

variable {endRing}

/-- [definition] Ring `r`'s junction anchor `v_r`: one conductance `G_a` per contact, read at both
ends (R2 C1). -/
def ringAnchor (Y : Ring → ℝ) (G : Contact → ℝ) (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring) : V r :=
  anchor (Y r) (fun p : Port endRing r => G p.1.1) (s r) (portWave endRing arr r)

/-- [definition] The junction's storage output `b_r = 2 v_r − s_r`. -/
def storageWave (Y : Ring → ℝ) (G : Contact → ℝ) (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring) : V r :=
  swing (ringAnchor Y G s arr r) (s r)

/-- [definition] The ring's contrast `c_r = v_r − s_r`. -/
def contrast (Y : Ring → ℝ) (G : Contact → ℝ) (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring) : V r :=
  ringAnchor Y G s arr r - s r

/-- [definition] The wave `o_(r→a) = 2 v_r − a_(r←a)` leaving the junction at each contact end. -/
def endOut (Y : Ring → ℝ) (G : Contact → ℝ) (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) (e : Contact × Bool) : V (endRing e) :=
  swing (ringAnchor Y G s arr (endRing e)) (arr e)

/-- [definition] The waves the transits return to the rings at the tick's end. -/
def endArrive (channel : (e : Contact × Bool) → Ch e.1 →L[ℝ] V (endRing e)) (G : Contact → ℝ)
    (o : (e : Contact × Bool) → V (endRing e)) (ω : (a : Contact) → Ch a) :
    (e : Contact × Bool) → V (endRing e)
  | (a, true) => arriveG (channel (a, true)) (G a) (o (a, true)) (ω a)
  | (a, false) => arriveH (channel (a, false)) (G a) (o (a, false)) (ω a)

/-- [definition] **The field's global power**
`P = (h/4)[Σ_r Y_r|s_r|² + Σ_(r,a) G_a|a_(r←a)|²] + Σ_a E_a`. -/
def fieldPower (Y : Ring → ℝ) (G : Contact → ℝ) (h : ℝ) (C K : (a : Contact) → Ch a →L[ℝ] Ch a)
    (s : (r : Ring) → V r) (arr : (e : Contact × Bool) → V (endRing e))
    (u w : (a : Contact) → Ch a) : ℝ :=
  h / 4 * (∑ r, Y r * ‖s r‖ ^ 2 + ∑ e, G e.1 * ‖arr e‖ ^ 2) +
    ∑ a, contactEnergy (C a) (K a) (u a) (w a)

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)] in
theorem norm_portWave (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring)
    (p : Port endRing r) : ‖portWave endRing arr r p‖ = ‖arr p.1‖ := by
  obtain ⟨e, he⟩ := p
  subst he
  rfl

omit [Fintype Ring] [∀ r, FiniteDimensional ℝ (V r)] in
theorem norm_portOut (Y : Ring → ℝ) (G : Contact → ℝ) (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) (r : Ring) (p : Port endRing r) :
    ‖portOut (Y r) (fun p : Port endRing r => G p.1.1) (s r) (portWave endRing arr r) p‖ =
      ‖endOut Y G s arr p.1‖ := by
  obtain ⟨e, he⟩ := p
  subst he
  rfl

theorem sum_ends {M : Type*} [AddCommMonoid M] (f : Contact × Bool → M) :
    ∑ e, f e = ∑ a, (f (a, true) + f (a, false)) := by
  rw [Fintype.sum_prod_type]
  simp

/-- [proved-derived; formal-checked] **The tick's global power balance** (R2 C1, R3 C1). One tick
of junction Swings, ring elements and contact transits changes the field's power by exactly the
contacts' dissipation, the passive element terms and the contrast ports' power:
`P(t+1) = P(t) − h Σ_a ⟨ω_a, D_a ω_a⟩ + (h/2) Σ_r Y_r ⟨x̄_r, W_s,r x̄_r⟩ + Π_c`,
`Π_c = (h/2) Σ_r Y_r ⟨x̄_r, W_c,r c_r⟩`. The junctions contribute zero
(`Propagation.junctionSwing_isometry`), the elements their drive balances
(`reaction_stage_balance`), and the transits their two-port balances
(`Propagation.transit_balance_waves`); each contact's single conductance `G_a` weights its waves at
both of its ends. -/
theorem word_tick_balance (channel : (e : Contact × Bool) → Ch e.1 →L[ℝ] V (endRing e))
    (Y : Ring → ℝ) (G : Contact → ℝ) (h : ℝ)
    (Ws : (r : Ring) → V r →L[ℝ] V r) (A : (r : Ring) → ρ → V r →L[ℝ] V r) (σ : Ring → ρ → ℝ)
    (Wc : (r : Ring) → V r →L[ℝ] V r) (C D K : (a : Contact) → Ch a →L[ℝ] Ch a)
    (s s' : (r : Ring) → V r) (arr : (e : Contact × Bool) → V (endRing e))
    (u w ω : (a : Contact) → Ch a)
    (hsum : ∀ r, admittanceSum (Y r) (fun p : Port endRing r => G p.1.1) ≠ 0)
    (hA : ∀ r i v, inner ℝ v (A r i v) = 0)
    (helem : ∀ r, ElementStep (Ws r) (A r) (σ r) (Wc r) (storageWave Y G s arr r)
      (contrast Y G s arr r) (s' r))
    (hC : ∀ a x y, inner ℝ (C a x) y = inner ℝ x (C a y))
    (hK : ∀ a x y, inner ℝ (K a x) y = inner ℝ x (K a y))
    (hι : ∀ e, IsChannelEmbedding (channel e)) (hG : ∀ a, G a ≠ 0)
    (htransit : ∀ a, TransitSolves (C a) (D a) (K a) (G a) h (u a) (w a)
      (ContinuousLinearMap.adjoint (channel (a, true)) (endOut Y G s arr (a, true)))
      (ContinuousLinearMap.adjoint (channel (a, false)) (endOut Y G s arr (a, false))) (ω a)) :
    fieldPower Y G h C K s' (endArrive channel G (endOut Y G s arr) ω)
        (fun a => u a + h • ω a) (fun a => (2 : ℝ) • ω a - w a) =
      fieldPower Y G h C K s arr u w - h * ∑ a, inner ℝ (ω a) (D a (ω a)) +
        h / 2 * ∑ r, Y r * inner ℝ (midpoint (storageWave Y G s arr r) (s' r))
          (Ws r (midpoint (storageWave Y G s arr r) (s' r))) +
        h / 2 * ∑ r, Y r * inner ℝ (midpoint (storageWave Y G s arr r) (s' r))
          (Wc r (contrast Y G s arr r)) := by
  set o := endOut Y G s arr
  set b := storageWave Y G s arr
  set arr' := endArrive channel G o ω
  -- the junctions contribute zero
  have hJ : ∑ r, Y r * ‖b r‖ ^ 2 + ∑ e, G e.1 * ‖o e‖ ^ 2 =
      ∑ r, Y r * ‖s r‖ ^ 2 + ∑ e, G e.1 * ‖arr e‖ ^ 2 := by
    rw [← Fintype.sum_fiberwise endRing (fun e => G e.1 * ‖o e‖ ^ 2),
      ← Fintype.sum_fiberwise endRing (fun e => G e.1 * ‖arr e‖ ^ 2), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hr := junctionSwing_isometry (Y r) (fun p : Port endRing r => G p.1.1) (hsum r) (s r)
      (portWave endRing arr r)
    simp only [norm_portOut, norm_portWave] at hr
    exact hr
  -- the elements
  have hE : ∀ r, ‖s' r‖ ^ 2 = ‖b r‖ ^ 2 +
      2 * inner ℝ (midpoint (b r) (s' r)) (Ws r (midpoint (b r) (s' r))) +
      2 * inner ℝ (midpoint (b r) (s' r)) (Wc r (contrast Y G s arr r)) := by
    intro r
    have := reaction_stage_balance (hA r) (σ r) (Wc r) (helem r)
    linarith
  -- the transits
  have hT : ∀ a, contactEnergy (C a) (K a) (u a + h • ω a) ((2 : ℝ) • ω a - w a) -
      contactEnergy (C a) (K a) (u a) (w a) + h * inner ℝ (ω a) (D a (ω a)) =
        h / 4 * (G a * ‖o (a, true)‖ ^ 2 + G a * ‖o (a, false)‖ ^ 2 -
          (G a * ‖arr' (a, true)‖ ^ 2 + G a * ‖arr' (a, false)‖ ^ 2)) := by
    intro a
    rw [transit_balance_waves (C a) (D a) (K a) (hC a) (hK a) (hι (a, true)) (hι (a, false))
      (hG a) (htransit a)]
    simp only [arr', endArrive]
    ring
  have hTsum := Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hT a
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← sum_ends (fun e => G e.1 * ‖o e‖ ^ 2),
    ← sum_ends (fun e => G e.1 * ‖arr' e‖ ^ 2)] at hTsum
  have hEsum : ∑ r, Y r * ‖s' r‖ ^ 2 = ∑ r, Y r * ‖b r‖ ^ 2 +
      2 * ∑ r, Y r * inner ℝ (midpoint (b r) (s' r)) (Ws r (midpoint (b r) (s' r))) +
      2 * ∑ r, Y r * inner ℝ (midpoint (b r) (s' r)) (Wc r (contrast Y G s arr r)) := by
    simp only [hE, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun r _ => by ring
    · exact Finset.sum_congr rfl fun r _ => by ring
  simp only [fieldPower]
  rw [hEsum]
  linear_combination (h / 4) * hJ + hTsum

/-- [counterexample; formal-checked] **One conductance per contact is load-bearing** (R2 C1). On a
constitution-free contact between two one-dimensional rings the transit is pure transmission: the
wave `1` leaving the `g` end arrives at the `h` end. Weighting the ends by per-ring conductances
`1` and `2` (the first design's per-ring exponent), the weighted power is `1` before the transit and
`2` after it. With one conductance per contact it is conserved. -/
theorem word_tick_balance_needs_one_conductance :
    let ι := ContinuousLinearMap.id ℝ ℝ
    let ω : ℝ := (1 / 2 : ℝ) * (ContinuousLinearMap.adjoint ι 1 - ContinuousLinearMap.adjoint ι 0)
    TransitSolves (0 : ℝ →L[ℝ] ℝ) 0 0 1 1 0 0 (ContinuousLinearMap.adjoint ι 1)
        (ContinuousLinearMap.adjoint ι 0) ω ∧
      arriveG ι 1 1 ω = 0 ∧ arriveH ι 1 0 ω = 1 ∧
      (1 : ℝ) * ‖(1 : ℝ)‖ ^ 2 + 2 * ‖(0 : ℝ)‖ ^ 2 ≠
        1 * ‖arriveG ι 1 1 ω‖ ^ 2 + 2 * ‖arriveH ι 1 0 ω‖ ^ 2 ∧
      (1 : ℝ) * ‖(1 : ℝ)‖ ^ 2 + 1 * ‖(0 : ℝ)‖ ^ 2 =
        1 * ‖arriveG ι 1 1 ω‖ ^ 2 + 1 * ‖arriveH ι 1 0 ω‖ ^ 2 := by
  intro ι ω
  have hadj : ∀ x : ℝ, ContinuousLinearMap.adjoint ι x = x := by
    intro x
    simp [ι, ContinuousLinearMap.adjoint_id]
  have hω : ω = 1 / 2 := by simp only [ω, hadj]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [TransitSolves, transitOperator, hω, hadj]
    norm_num
  · simp only [arriveG, hω, ι, ContinuousLinearMap.id_apply]; norm_num
  · simp only [arriveH, hω, ι, ContinuousLinearMap.id_apply]; norm_num
  · simp only [arriveG, arriveH, hω, ι, ContinuousLinearMap.id_apply]; norm_num
  · simp only [arriveG, arriveH, hω, ι, ContinuousLinearMap.id_apply]; norm_num

/-! ### The tick as a map, and its causal cone on the ring/contact blocks -/

/-- [definition] **The medium at a cut**: every operand of a tick, fixed within a word — the
channels, admittances and conductances, the tick length, each ring's element at its sheet
classes, and each contact's constitution. -/
structure Medium (endRing : Contact × Bool → Ring) (V : Ring → Type*)
    [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)] (Ch : Contact → Type*)
    [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)] (ρ : Type*) where
  channel : (e : Contact × Bool) → Ch e.1 →L[ℝ] V (endRing e)
  Y : Ring → ℝ
  G : Contact → ℝ
  h : ℝ
  Ws : (r : Ring) → V r →L[ℝ] V r
  A : (r : Ring) → ρ → V r →L[ℝ] V r
  σ : Ring → ρ → ℝ
  Wc : (r : Ring) → V r →L[ℝ] V r
  C : (a : Contact) → Ch a →L[ℝ] Ch a
  D : (a : Contact) → Ch a →L[ℝ] Ch a
  K : (a : Contact) → Ch a →L[ℝ] Ch a

/-- [definition] The medium's declared admissibility (campaign 1): passive `W_s`, skew slices,
contacts carried as squares (`C, D, K ⪰ 0`, `C, K` symmetric), positive admittances,
conductances and tick length, and channel embeddings. -/
structure Medium.Admissible (μ : Medium endRing V Ch ρ) : Prop where
  Ws_passive : ∀ r v, inner ℝ v (μ.Ws r v) ≤ 0
  A_skew : ∀ r i v, inner ℝ v (μ.A r i v) = 0
  C_psd : ∀ a v, 0 ≤ inner ℝ v (μ.C a v)
  D_psd : ∀ a v, 0 ≤ inner ℝ v (μ.D a v)
  K_psd : ∀ a v, 0 ≤ inner ℝ v (μ.K a v)
  C_symm : ∀ a x y, inner ℝ (μ.C a x) y = inner ℝ x (μ.C a y)
  K_symm : ∀ a x y, inner ℝ (μ.K a x) y = inner ℝ x (μ.K a y)
  Y_pos : ∀ r, 0 < μ.Y r
  G_pos : ∀ a, 0 < μ.G a
  h_pos : 0 < μ.h
  channel : ∀ e, IsChannelEmbedding (μ.channel e)

/-- [definition] **The change inside a word**: the storage waves, the arriving waves at every
contact end, and the contacts' displacements and slip rates. -/
structure Change (endRing : Contact × Bool → Ring) (V : Ring → Type*) (Ch : Contact → Type*) where
  s : (r : Ring) → V r
  arr : (e : Contact × Bool) → V (endRing e)
  u : (a : Contact) → Ch a
  w : (a : Contact) → Ch a

/-- [definition] The element's local solve (unique for an admissible medium). -/
def elementSolve (μ : Medium endRing V Ch ρ) (r : Ring) (b c : V r) : V r :=
  Classical.epsilon fun s' => ElementStep (μ.Ws r) (μ.A r) (μ.σ r) (μ.Wc r) b c s'

/-- [definition] The contact's local solve `M_a ω = …` (unique for an admissible medium). -/
def transitSolve (μ : Medium endRing V Ch ρ) (a : Contact) (u w αg αh : Ch a) : Ch a :=
  Classical.epsilon fun ω => TransitSolves (μ.C a) (μ.D a) (μ.K a) (μ.G a) μ.h u w αg αh ω

/-- [definition] The slip rates of one tick's transits. -/
def tickSlip (μ : Medium endRing V Ch ρ) (X : Change endRing V Ch) (a : Contact) : Ch a :=
  transitSolve μ a (X.u a) (X.w a)
    (ContinuousLinearMap.adjoint (μ.channel (a, true)) (endOut μ.Y μ.G X.s X.arr (a, true)))
    (ContinuousLinearMap.adjoint (μ.channel (a, false)) (endOut μ.Y μ.G X.s X.arr (a, false)))

/-- [definition] **One tick of the word**: junction Swings, ring elements, contact transits. -/
def fieldTick (μ : Medium endRing V Ch ρ) (X : Change endRing V Ch) : Change endRing V Ch where
  s r := elementSolve μ r (storageWave μ.Y μ.G X.s X.arr r) (contrast μ.Y μ.G X.s X.arr r)
  arr := endArrive μ.channel μ.G (endOut μ.Y μ.G X.s X.arr) (tickSlip μ X)
  u a := X.u a + μ.h • tickSlip μ X a
  w a := (2 : ℝ) • tickSlip μ X a - X.w a

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] in
theorem elementSolve_spec {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (r : Ring) (b c : V r) :
    ElementStep (μ.Ws r) (μ.A r) (μ.σ r) (μ.Wc r) b c (elementSolve μ r b c) ∧
      ∀ s', ElementStep (μ.Ws r) (μ.A r) (μ.σ r) (μ.Wc r) b c s' → s' = elementSolve μ r b c := by
  have hwd := (tick_well_defined (μ.Ws r) (hμ.Ws_passive r) (μ.A r) (hμ.A_skew r) (μ.σ r) (μ.Wc r)
    (0 : ℝ →L[ℝ] ℝ) 0 0 (fun v => by simp) (fun v => by simp) (fun v => by simp) one_pos
    one_pos).1 b c
  obtain ⟨s₀, hs₀, huniq⟩ := hwd
  have hex : ∃ s', ElementStep (μ.Ws r) (μ.A r) (μ.σ r) (μ.Wc r) b c s' :=
    ⟨s₀, (elementStep_iff _ _ _ _ _ _ _).mpr hs₀⟩
  have hspec := Classical.epsilon_spec hex
  refine ⟨hspec, fun s' hs' => ?_⟩
  rw [huniq s' ((elementStep_iff _ _ _ _ _ _ _).mp hs')]
  exact (huniq _ ((elementStep_iff _ _ _ _ _ _ _).mp hspec)).symm

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [Fintype ρ] in
theorem transitSolve_spec {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (a : Contact)
    (u w αg αh : Ch a) :
    TransitSolves (μ.C a) (μ.D a) (μ.K a) (μ.G a) μ.h u w αg αh (transitSolve μ a u w αg αh) ∧
      ∀ ω, TransitSolves (μ.C a) (μ.D a) (μ.K a) (μ.G a) μ.h u w αg αh ω →
        ω = transitSolve μ a u w αg αh := by
  have hwd := (tick_well_defined (0 : ℝ →L[ℝ] ℝ) (fun v => by simp) (fun _ : Empty => 0)
    (fun i => i.elim) (fun _ => 0) 0 (μ.C a) (μ.D a) (μ.K a) (hμ.C_psd a) (hμ.D_psd a)
    (hμ.K_psd a) (hμ.G_pos a) hμ.h_pos).2.2
    ((2 : ℝ) • μ.C a w + μ.h • (αg - αh) - μ.h • μ.K a u)
  obtain ⟨ω₀, hω₀, huniq⟩ := hwd
  have hspec := Classical.epsilon_spec (p := fun ω => TransitSolves (μ.C a) (μ.D a) (μ.K a)
    (μ.G a) μ.h u w αg αh ω) ⟨ω₀, hω₀⟩
  exact ⟨hspec, fun ω hω => (huniq ω hω).trans (huniq _ hspec).symm⟩

/-- [proved-derived; formal-checked] **The tick map's global power balance**: `word_tick_balance`
for the tick map of an admissible medium, whose local solves exist and are unique
(`tick_well_defined`). -/
theorem fieldTick_balance {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (X : Change endRing V Ch) :
    fieldPower μ.Y μ.G μ.h μ.C μ.K (fieldTick μ X).s (fieldTick μ X).arr (fieldTick μ X).u
        (fieldTick μ X).w =
      fieldPower μ.Y μ.G μ.h μ.C μ.K X.s X.arr X.u X.w -
        μ.h * ∑ a, inner ℝ (tickSlip μ X a) (μ.D a (tickSlip μ X a)) +
        μ.h / 2 * ∑ r, μ.Y r * inner ℝ (midpoint (storageWave μ.Y μ.G X.s X.arr r)
            ((fieldTick μ X).s r)) (μ.Ws r (midpoint (storageWave μ.Y μ.G X.s X.arr r)
              ((fieldTick μ X).s r))) +
        μ.h / 2 * ∑ r, μ.Y r * inner ℝ (midpoint (storageWave μ.Y μ.G X.s X.arr r)
            ((fieldTick μ X).s r)) (μ.Wc r (contrast μ.Y μ.G X.s X.arr r)) := by
  refine word_tick_balance μ.channel μ.Y μ.G μ.h μ.Ws μ.A μ.σ μ.Wc μ.C μ.D μ.K X.s
    (fieldTick μ X).s X.arr X.u X.w (tickSlip μ X) (fun r => ?_) hμ.A_skew
    (fun r => (elementSolve_spec hμ r _ _).1) hμ.C_symm hμ.K_symm hμ.channel
    (fun a => (hμ.G_pos a).ne') (fun a => (transitSolve_spec hμ a _ _ _ _).1)
  exact (add_pos_of_pos_of_nonneg (hμ.Y_pos r)
    (Finset.sum_nonneg fun p _ => (hμ.G_pos p.1.1).le)).ne'

variable (endRing) in
/-- [definition] **The word's block graph**: blocks are rings (storage with the waves they receive)
and contacts (their state); one tick carries a ring into itself, into every ring sharing a contact
with it and into its contacts, and a contact into itself and its two rings. -/
def blockAdj : Ring ⊕ Contact → Ring ⊕ Contact → Prop
  | .inl r', .inl r => r' = r ∨ ∃ a b b', endRing (a, b) = r' ∧ endRing (a, b') = r
  | .inr a, .inl r => ∃ b, endRing (a, b) = r
  | .inl r, .inr a => ∃ b, endRing (a, b) = r
  | .inr a, .inr a' => a = a'

/-- [definition] A change vanishes on a block. -/
def BlockZero (X : Change endRing V Ch) : Ring ⊕ Contact → Prop
  | .inl r => X.s r = 0 ∧ ∀ e, endRing e = r → X.arr e = 0
  | .inr a => X.u a = 0 ∧ X.w a = 0

omit [Fintype Ring] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, InnerProductSpace ℝ (Ch a)]
  [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem ringAnchor_zero (Y : Ring → ℝ) (G : Contact → ℝ) (X : Change endRing V Ch) (r : Ring)
    (hr : BlockZero X (.inl r)) : ringAnchor Y G X.s X.arr r = 0 := by
  obtain ⟨hs, harr⟩ := hr
  have hp : ∀ p : Port endRing r, portWave endRing X.arr r p = 0 := by
    rintro ⟨e, he⟩
    subst he
    exact harr e rfl
  simp [ringAnchor, anchor, hs, hp]

omit [Fintype Ring] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, InnerProductSpace ℝ (Ch a)]
  [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem endOut_zero (Y : Ring → ℝ) (G : Contact → ℝ) (X : Change endRing V Ch) (e : Contact × Bool)
    (hr : BlockZero X (.inl (endRing e))) : endOut Y G X.s X.arr e = 0 := by
  rw [endOut, ringAnchor_zero Y G X _ hr, hr.2 e rfl]
  simp [Holonics.Geometry.AffineSwing.swing]

omit [Fintype Ring] [Fintype ρ] in
theorem tickSlip_zero {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (X : Change endRing V Ch)
    (a : Contact) (ha : BlockZero X (.inr a)) (hg : BlockZero X (.inl (endRing (a, true))))
    (hh : BlockZero X (.inl (endRing (a, false)))) : tickSlip μ X a = 0 := by
  obtain ⟨hu, hw⟩ := ha
  have hzero : TransitSolves (μ.C a) (μ.D a) (μ.K a) (μ.G a) μ.h (X.u a) (X.w a)
      (ContinuousLinearMap.adjoint (μ.channel (a, true)) (endOut μ.Y μ.G X.s X.arr (a, true)))
      (ContinuousLinearMap.adjoint (μ.channel (a, false)) (endOut μ.Y μ.G X.s X.arr (a, false)))
      0 := by
    rw [TransitSolves, endOut_zero _ _ X _ hg, endOut_zero _ _ X _ hh, hu, hw]
    simp
  exact ((transitSolve_spec hμ a _ _ _ _).2 0 hzero).symm

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **One tick moves a change one block hop.** A block of the
tick's output vanishes when the block and every block one tick carries into it vanished
(`elementSolve_spec`, `transitSolve_spec`: the local solves of zero data are zero). -/
theorem fieldTick_local {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (X : Change endRing V Ch)
    (y : Ring ⊕ Contact) (hy : BlockZero X y)
    (hnb : ∀ z, blockAdj endRing z y → BlockZero X z) : BlockZero (fieldTick μ X) y := by
  cases y with
  | inl r =>
    have hc : contrast μ.Y μ.G X.s X.arr r = 0 := by
      rw [contrast, ringAnchor_zero _ _ X r hy, hy.1, sub_zero]
    have hb : storageWave μ.Y μ.G X.s X.arr r = 0 := by
      rw [storageWave, ringAnchor_zero _ _ X r hy, hy.1]
      simp [Holonics.Geometry.AffineSwing.swing]
    have hs : (fieldTick μ X).s r = 0 := by
      change elementSolve μ r _ _ = 0
      rw [hb, hc]
      refine ((elementSolve_spec hμ r 0 0).2 0 ?_).symm
      simp [ElementStep]
    refine ⟨hs, ?_⟩
    rintro ⟨a, b⟩ he
    have hslip : tickSlip μ X a = 0 := by
      refine tickSlip_zero hμ X a (hnb (.inr a) ⟨b, he⟩) ?_ ?_
      · exact hnb (.inl _) (Or.inr ⟨a, true, b, rfl, he⟩)
      · exact hnb (.inl _) (Or.inr ⟨a, false, b, rfl, he⟩)
    cases b with
    | true =>
      change arriveG _ _ (endOut μ.Y μ.G X.s X.arr (a, true)) (tickSlip μ X a) = 0
      rw [endOut_zero _ _ X _ (he ▸ hy), hslip, arriveG]
      simp
    | false =>
      change arriveH _ _ (endOut μ.Y μ.G X.s X.arr (a, false)) (tickSlip μ X a) = 0
      rw [endOut_zero _ _ X _ (he ▸ hy), hslip, arriveH]
      simp
  | inr a =>
    have hslip : tickSlip μ X a = 0 :=
      tickSlip_zero hμ X a hy (hnb (.inl _) ⟨true, rfl⟩) (hnb (.inl _) ⟨false, rfl⟩)
    refine ⟨?_, ?_⟩
    · change X.u a + μ.h • tickSlip μ X a = 0
      rw [hy.1, hslip]; simp
    · change (2 : ℝ) • tickSlip μ X a - X.w a = 0
      rw [hy.2, hslip]; simp

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The causal cone of the word** (§8.1). For an admissible
medium, a change vanishing off the blocks `Z` vanishes, after `t` ticks, off the blocks within `t`
hops of `Z` on the word's block graph: a change moves one contact per tick, and there is no global
solve. -/
theorem word_tick_cone {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (X : Change endRing V Ch)
    {Z : Set (Ring ⊕ Contact)} (hX : ∀ y, y ∉ Z → BlockZero X y) (t : ℕ) :
    ∀ y, y ∉ reachWithin (blockAdj endRing) Z t → BlockZero ((fieldTick μ)^[t] X) y := by
  induction t with
  | zero =>
    intro y hy
    exact hX y fun hyZ => hy ⟨y, hyZ, 0, le_rfl, ReachIn.refl y⟩
  | succ t ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    refine fieldTick_local hμ _ y (ih y fun h => hy (reachWithin_mono (Nat.le_succ t) h)) ?_
    intro z hz
    exact ih z fun h => hy (reachWithin_step h hz)

end Tick

section Audit

#print axioms reaction_stage_balance
#print axioms reaction_stage_isometry
#print axioms reaction_stage_isometry_needs_both
#print axioms contrastPort_active
#print axioms reaction_stage_adjoint
#print axioms reaction_stage_slice_difference
#print axioms word_tick_balance
#print axioms word_tick_balance_needs_one_conductance
#print axioms fieldTick_balance
#print axioms fieldTick_local
#print axioms word_tick_cone

end Audit

end Holonics.HNN.Word
