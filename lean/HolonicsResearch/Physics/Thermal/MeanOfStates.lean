import Mathlib

/-!
# The saving of a mean of states, a rate as a window, and a lap-mean difference as its weights

[proved-derived] Issue #410 (three boxes, from #666). The source is the record of November 11
(`research/records/2026-11-11_A_DEPOSITS_RATE_IS_A_TEMPERATURE_ITS_STANDING_SPREAD_IS_SHED_BY_A_MEAN_OF_STATES_AND_LAP_ENDS_ARE_DRAWS_THAT_DO_NOT_REMEMBER_EACH_OTHER.md`,
§2 item 6 and §4); atlas `deposition.rate-temperature-standing-spread`, `deposition.lap-mean-quarter-floor`,
`tower.field-lap-mean`.

What is proved.

1. **The saving of a mean of states** (`saving_eq_ordered_pairs`, `saving_eq_unordered_pairs`). On a quadratic code
   `c(θ) = c₀ + g(θ) + ½ B(θ, θ)`, the code at the mean of `n` states stands under the mean of their `n` codes by
   `1/(4n²)` times the sum over ordered pairs of `q_ij = B(θ_i − θ_j, θ_i − θ_j)`, which is `1/(2n²)` times the sum
   over unordered pairs. The linear part and the constant leave the saving (`saving_eq_curvature`); two states read
   `q/8` and three the sum of three `q` over 18 (`saving_two`, `saving_three`), the record's readings. The identity
   needs no symmetry of `B`: only the symmetric part of a stiffness enters a quadratic code.
2. **The mean of the saving** (`mean_saving`). For `n` draws whose centred second moments are
   `E[(θ_i − μ)_a (θ_j − μ)_b] = δ_ij Σ_ab` under a linear mean `E`, the mean of the saving is `(1 − 1/n)` of the
   standing cost `½ tr(HΣ)`; a mean of a pair's curvature is `2 tr(HΣ)`, four times the standing cost
   (`mean_travel`). With the stepped descent's stationary law, `2 tr(HΣ) = tr(CP)`
   (`Physics/Thermal/LinearDiffusion.two_mul_trace_stiffness_covariance`), the mean saving is `(1 − 1/n)·¼ tr(CP)`
   (`mean_saving_of_stepped_descent`).
3. **A rate is a window** (`standing_cost_at_information_equality`, `trace_diagonal_mul`, `rate_is_window`,
   `entry_window`). Under the information equality the stationary covariance is `½P`
   (`Physics/Thermal/LinearDiffusion.stationary_half_step_of_noise_eq_stiffness`), so the standing cost is
   `¼ tr(PH)`; for a diagonal step it is `d/(2n)` times `n/2` times the mean over entries of `P_ii H_ii`, and one
   entry's standing cost is the least excess `1/(2w)` of an estimate from `w = 2/(P_ii H_ii)` sites.
4. **A lap-mean difference is its weights** (`abel_rising`, `abel_falling`, `lapSum_succ_sub`, `lapMean_succ_sub`).
   For a walk `X t = Σ_(u<t) ε u` read at lap means `M k = (1/n) Σ_(j<n) X (k n + j + 1)`,
   `n (M (k+1) − M k) = Σ_(i<n) i ε (k n + i) + Σ_(i<n) (n − i) ε ((k+1) n + i)`. For increments with
   `E[ε_u ε_v] = δ_uv v` the difference has the second moment `v (Σ_(i<n) i² + Σ_(i<n) (i+1)²)` at the scale `n²`
   and two successive differences share `v Σ_(i<n) i (n − i)` (`lapDiff_second_moment`, `lapDiff_shared_moment`,
   `sum_falling_sq`, `lap_second_moment`, `lap_shared_moment`): the own and shared weights whose sums
   `Physics/Thermal/LapMean` holds (`six_mul_own`, `six_mul_shared`, `own_eq_four_mul_shared_add`).

Limits. Statement 2 takes the draws' second moments as its hypothesis: independent draws of one law with mean `μ`
and covariance `Σ` satisfy it, and that the stationary law of `Physics/Thermal/LinearDiffusion` is such a law is that
module's. `E` is any real-linear functional on the functions of the sample (a finite weighted mean, or an integral
restricted to the functions it is linear on); no measure is constructed. Statement 3's least excess `d/(2n)` (the
Cramér–Rao chart) is cited and not formalized. Statement 4's moments are second moments about zero: for increments
of mean zero they are the variance and the covariance. The code is quadratic throughout; a code that is not
quadratic moves these at the next order in the spread.

The computational object is the helical pair interaction: a state is a constitution's material, a pair of states a
contact whose curvature along their travel is `q_ij`, and the mean of states the reading that sheds the standing
spread. Of the winding guide's six general objects this touches the pair (the pair of states and its curvature) and
the tube (the lap, the span a mean is taken over); the helix, faces and placement, cell holonomy and tower thread stay
attached.

Consumers: #410's boxes "The saving of a mean of states", "A rate is a window" and "A lap-mean difference is its
weights"; the engine's reading `holonics_engine::field::MaterialMean` and the host ruler `tools/state_travel.py mean`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Thermal.MeanOfStates

open Finset Matrix

/-! ## 1. The saving of a mean of states -/

section Saving

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {κ : Type*}

/-- [definition] A quadratic code: a constant, a linear part and half a bilinear form. -/
noncomputable def code (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : V) : ℝ :=
  c₀ + g θ + 1 / 2 * B θ θ

/-- [definition] The code's curvature along the travel between two states, `q_ij = B(θ_i − θ_j, θ_i − θ_j)`. -/
def travel (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) (i j : κ) : ℝ := B (θ i - θ j) (θ i - θ j)

/-- [proved-standard] A pair's curvature does not depend on the pair's order. -/
theorem travel_symm (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) (i j : κ) : travel B θ i j = travel B θ j i := by
  unfold travel
  rw [← neg_sub (θ j) (θ i)]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- [proved-standard] A state has no travel to itself. -/
theorem travel_self (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) (i : κ) : travel B θ i i = 0 := by
  unfold travel
  simp

variable [Fintype κ]

/-- [definition] The mean of a finite family of states. -/
noncomputable def meanState (θ : κ → V) : V := (Fintype.card κ : ℝ)⁻¹ • ∑ i, θ i

/-- [definition] The saving of a mean of states: the mean of the states' codes less the code at their mean. -/
noncomputable def saving (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ i, code c₀ g B (θ i) - code c₀ g B (meanState θ)

/-- [proved-standard] The sum of the curvature over ordered pairs:
`Σ_ij q_ij = 2n Σ_i B(θ_i, θ_i) − 2 B(Σθ, Σθ)`. -/
theorem sum_travel (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) :
    ∑ i, ∑ j, travel B θ i j =
      2 * (Fintype.card κ : ℝ) * ∑ i, B (θ i) (θ i) - 2 * B (∑ i, θ i) (∑ i, θ i) := by
  have hSS : B (∑ i, θ i) (∑ j, θ j) = ∑ i, ∑ j, B (θ i) (θ j) := by
    calc B (∑ i, θ i) (∑ j, θ j) = ∑ j, B (∑ i, θ i) (θ j) := map_sum _ _ _
      _ = ∑ j, ∑ i, B (θ i) (θ j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum, LinearMap.sum_apply]
      _ = ∑ i, ∑ j, B (θ i) (θ j) := Finset.sum_comm
  have h1 : ∀ i j, travel B θ i j = B (θ i) (θ i) - B (θ i) (θ j) - B (θ j) (θ i) + B (θ j) (θ j) := by
    intro i j
    unfold travel
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have e1 : ∑ i, ∑ _j : κ, B (θ i) (θ i) = (Fintype.card κ : ℝ) * ∑ i, B (θ i) (θ i) := by
    simp [Finset.mul_sum]
  have e3 : ∑ i, ∑ j, B (θ j) (θ i) = B (∑ i, θ i) (∑ i, θ i) := by
    rw [Finset.sum_comm]
    exact hSS.symm
  have e4 : ∑ _i : κ, ∑ j, B (θ j) (θ j) = (Fintype.card κ : ℝ) * ∑ j, B (θ j) (θ j) := by
    simp
  calc ∑ i, ∑ j, travel B θ i j
      = ∑ i, ∑ j, (B (θ i) (θ i) - B (θ i) (θ j) - B (θ j) (θ i) + B (θ j) (θ j)) := by
        simp_rw [h1]
    _ = (∑ i, ∑ _j : κ, B (θ i) (θ i)) - (∑ i, ∑ j, B (θ i) (θ j)) - (∑ i, ∑ j, B (θ j) (θ i)) +
          ∑ _i : κ, ∑ j, B (θ j) (θ j) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
        rw [e1, ← hSS, e3, e4]
        ring

/-- [proved-derived] **The saving of a mean of states, over ordered pairs**: the code at the mean of `n` states stands
under the mean of their `n` codes by `1/(4n²)` times the sum over ordered pairs of the curvature along their travel. -/
theorem saving_eq_ordered_pairs [Nonempty κ] (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) :
    saving c₀ g B θ = 1 / (4 * (Fintype.card κ : ℝ) ^ 2) * ∑ i, ∑ j, travel B θ i j := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmean : code c₀ g B (meanState θ) =
      c₀ + (Fintype.card κ : ℝ)⁻¹ * g (∑ i, θ i) +
        1 / 2 * ((Fintype.card κ : ℝ)⁻¹ * ((Fintype.card κ : ℝ)⁻¹ * B (∑ i, θ i) (∑ i, θ i))) := by
    unfold code meanState
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hcodes : ∑ i, code c₀ g B (θ i) =
      (Fintype.card κ : ℝ) * c₀ + g (∑ i, θ i) + 1 / 2 * ∑ i, B (θ i) (θ i) := by
    unfold code
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, map_sum]
    simp
  unfold saving
  rw [hmean, hcodes, sum_travel]
  field_simp
  ring

/-- [proved-derived] **The constant and the linear part leave the saving**: it is the saving of the curvature alone. -/
theorem saving_eq_curvature [Nonempty κ] (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) :
    saving c₀ g B θ = saving 0 0 B θ := by
  rw [saving_eq_ordered_pairs, saving_eq_ordered_pairs]

/-- [proved-standard] A symmetric reading with no diagonal sums over ordered pairs to twice its sum over unordered
pairs. -/
theorem sum_ordered_eq_two_mul_unordered [LinearOrder κ] (q : κ → κ → ℝ) (hsymm : ∀ i j, q i j = q j i)
    (hdiag : ∀ i, q i i = 0) :
    ∑ i, ∑ j, q i j = 2 * ∑ p ∈ (Finset.univ : Finset (κ × κ)).filter (fun p => p.1 < p.2), q p.1 p.2 := by
  have hpt : ∀ p : κ × κ,
      q p.1 p.2 = (if p.1 < p.2 then q p.1 p.2 else 0) + (if p.2 < p.1 then q p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · rw [h, hdiag, if_neg (lt_irrefl _), add_zero]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  have hswap : ∑ p : κ × κ, (if p.2 < p.1 then q p.1 p.2 else 0) =
      ∑ p : κ × κ, (if p.1 < p.2 then q p.1 p.2 else 0) := by
    rw [← Equiv.sum_comp (Equiv.prodComm κ κ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    show (if p.1 < p.2 then q p.2 p.1 else 0) = if p.1 < p.2 then q p.1 p.2 else 0
    rw [hsymm]
  calc ∑ i, ∑ j, q i j = ∑ p : κ × κ, q p.1 p.2 := (Fintype.sum_prod_type' _).symm
    _ = ∑ p : κ × κ, (if p.1 < p.2 then q p.1 p.2 else 0) +
          ∑ p : κ × κ, (if p.2 < p.1 then q p.1 p.2 else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => hpt p
    _ = _ := by
        rw [hswap, Finset.sum_filter]
        ring

/-- [proved-derived] **The saving of a mean of states, over unordered pairs**: `Σ_(i<j) q_ij / (2n²)`. -/
theorem saving_eq_unordered_pairs [Nonempty κ] [LinearOrder κ] (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : κ → V) :
    saving c₀ g B θ = 1 / (2 * (Fintype.card κ : ℝ) ^ 2) *
      ∑ p ∈ (Finset.univ : Finset (κ × κ)).filter (fun p => p.1 < p.2), travel B θ p.1 p.2 := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [saving_eq_ordered_pairs,
    sum_ordered_eq_two_mul_unordered (travel B θ) (travel_symm B θ) (travel_self B θ)]
  field_simp
  ring

/-- [proved-derived] **Two states read `q/8`.** -/
theorem saving_two (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : Fin 2 → V) :
    saving c₀ g B θ = travel B θ 0 1 / 8 := by
  rw [saving_eq_ordered_pairs]
  simp only [Fin.sum_univ_two, Fintype.card_fin, travel_self, travel_symm B θ 1 0]
  norm_num
  ring

/-- [proved-derived] **Three states read the sum of their three `q` over 18.** -/
theorem saving_three (c₀ : ℝ) (g : V →ₗ[ℝ] ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (θ : Fin 3 → V) :
    saving c₀ g B θ = (travel B θ 0 1 + travel B θ 0 2 + travel B θ 1 2) / 18 := by
  rw [saving_eq_ordered_pairs]
  simp only [Fin.sum_univ_three, Fintype.card_fin, travel_self, travel_symm B θ 1 0, travel_symm B θ 2 0,
    travel_symm B θ 2 1]
  norm_num
  ring

end Saving

/-! ## 2. The mean of the saving -/

section MeanSaving

variable {Ω : Type*} {d : Type*} [Fintype d] [DecidableEq d] {κ : Type*} [Fintype κ] [DecidableEq κ]

private theorem mean_sum {α : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (s : Finset α) (f : α → Ω → ℝ) :
    E (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, E (f a) := by
  have h : (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, f a := by
    funext ω
    rw [Finset.sum_apply]
  rw [h, map_sum]

private theorem mean_const_mul (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (f : Ω → ℝ) :
    E (fun ω => c * f ω) = c * E f := by
  have h : (fun ω => c * f ω) = c • f := by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul]
  rw [h, map_smul, smul_eq_mul]

private theorem mean_four (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f₁ f₂ f₃ f₄ : Ω → ℝ) :
    E (fun ω => f₁ ω - f₂ ω - f₃ ω + f₄ ω) = E f₁ - E f₂ - E f₃ + E f₄ := by
  have h : (fun ω => f₁ ω - f₂ ω - f₃ ω + f₄ ω) = f₁ - f₂ - f₃ + f₄ := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply]
  rw [h, map_add, map_sub, map_sub]

/-- [definition] The stiffness `H` as the bilinear form `(x, y) ↦ xᵀ H y`. -/
noncomputable def stiffness (H : Matrix d d ℝ) : (d → ℝ) →ₗ[ℝ] (d → ℝ) →ₗ[ℝ] ℝ := Matrix.toLinearMap₂' ℝ H

/-- [definition] The draws' second-moment hypothesis: about the common mean `μ` the draws are uncorrelated with
each other and each has the covariance `S`. -/
def Uncorrelated (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (θ : κ → Ω → d → ℝ) (μ : d → ℝ) (S : Matrix d d ℝ) : Prop :=
  ∀ i j a b, E (fun ω => (θ i ω a - μ a) * (θ j ω b - μ b)) = if i = j then S a b else 0

omit [Fintype d] [DecidableEq d] [Fintype κ] in
/-- [proved-standard] Under the hypothesis the covariance is symmetric. -/
theorem Uncorrelated.symm [Nonempty κ] {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {θ : κ → Ω → d → ℝ} {μ : d → ℝ}
    {S : Matrix d d ℝ} (h : Uncorrelated E θ μ S) (a b : d) : S a b = S b a := by
  obtain ⟨i⟩ := ‹Nonempty κ›
  have h1 := h i i a b
  have h2 := h i i b a
  rw [if_pos rfl] at h1 h2
  rw [← h1, ← h2]
  congr 1
  funext ω
  ring

omit [Fintype κ] in
/-- [proved-derived] **The mean of a pair's curvature**: for two different draws it is `2 tr(HΣ)`, four times the
standing cost `½ tr(HΣ)`; a draw has no travel to itself. -/
theorem mean_travel [Nonempty κ] {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {θ : κ → Ω → d → ℝ} {μ : d → ℝ} {S : Matrix d d ℝ}
    (h : Uncorrelated E θ μ S) (H : Matrix d d ℝ) (i j : κ) :
    E (fun ω => travel (stiffness H) (fun k => θ k ω) i j) = if i = j then 0 else 2 * (H * S).trace := by
  have hpt : ∀ ω, travel (stiffness H) (fun k => θ k ω) i j =
      ∑ a, ∑ b, H a b * ((θ i ω a - μ a) * (θ i ω b - μ b) - (θ i ω a - μ a) * (θ j ω b - μ b) -
        (θ j ω a - μ a) * (θ i ω b - μ b) + (θ j ω a - μ a) * (θ j ω b - μ b)) := by
    intro ω
    unfold travel stiffness
    rw [Matrix.toLinearMap₂'_apply']
    simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have htr : (H * S).trace = ∑ a, ∑ b, H a b * S a b := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h.symm b a]
  simp_rw [hpt]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, mean_four, h i i, h i j, h j i, h j j]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ j = i := fun e => hij e.symm
    simp only [if_true, if_neg hij, if_neg hji, htr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- [proved-derived] **The mean of the saving**: for `n` draws with the second moments of `Uncorrelated`, the mean of
the saving of their mean is `(1 − 1/n)` of the standing cost `½ tr(HΣ)`. -/
theorem mean_saving [Nonempty κ] {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {θ : κ → Ω → d → ℝ} {μ : d → ℝ} {S : Matrix d d ℝ}
    (h : Uncorrelated E θ μ S) (c₀ : ℝ) (g : (d → ℝ) →ₗ[ℝ] ℝ) (H : Matrix d d ℝ) :
    E (fun ω => saving c₀ g (stiffness H) (fun k => θ k ω)) =
      (1 - 1 / (Fintype.card κ : ℝ)) * (1 / 2 * (H * S).trace) := by
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp_rw [saving_eq_ordered_pairs]
  rw [mean_const_mul, mean_sum]
  simp_rw [mean_sum, mean_travel h H]
  have hsum : ∑ i : κ, ∑ j : κ, (if i = j then (0 : ℝ) else 2 * (H * S).trace) =
      ((Fintype.card κ : ℝ) ^ 2 - (Fintype.card κ : ℝ)) * (2 * (H * S).trace) := by
    have hrow : ∀ i : κ, ∑ j : κ, (if i = j then (0 : ℝ) else 2 * (H * S).trace) =
        ((Fintype.card κ : ℝ) - 1) * (2 * (H * S).trace) := by
      intro i
      have hsplit : ∀ j : κ, (if i = j then (0 : ℝ) else 2 * (H * S).trace) =
          2 * (H * S).trace - (if i = j then 2 * (H * S).trace else 0) := by
        intro j
        split_ifs <;> ring
      simp_rw [hsplit]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      simp
      ring
    simp_rw [hrow]
    simp
    ring
  rw [hsum]
  field_simp
  ring

/-- [proved-derived] **The mean saving of a stepped descent's states**: with the stationary law of a descent that
steps by `P` on covectors of noise `C`, where `2 tr(HΣ) = tr(CP)`
(`Physics/Thermal/LinearDiffusion.two_mul_trace_stiffness_covariance`), the mean of the saving is
`(1 − 1/n)·¼ tr(CP)`, the stiffness absent. -/
theorem mean_saving_of_stepped_descent [Nonempty κ] {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {θ : κ → Ω → d → ℝ} {μ : d → ℝ}
    {S : Matrix d d ℝ} (h : Uncorrelated E θ μ S) (c₀ : ℝ) (g : (d → ℝ) →ₗ[ℝ] ℝ) (H C P : Matrix d d ℝ)
    (hstat : 2 * (H * S).trace = (C * P).trace) :
    E (fun ω => saving c₀ g (stiffness H) (fun k => θ k ω)) =
      (1 - 1 / (Fintype.card κ : ℝ)) * (1 / 4 * (C * P).trace) := by
  rw [mean_saving h, ← hstat]
  ring

end MeanSaving

/-! ## 3. A rate is a window -/

section Window

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- [proved-derived] **The standing cost at the information equality**: with the stationary covariance `½P`
(`Physics/Thermal/LinearDiffusion.stationary_half_step_of_noise_eq_stiffness`), `½ tr(HΣ) = ¼ tr(PH)`. -/
theorem standing_cost_at_information_equality (P H : Matrix d d ℝ) :
    1 / 2 * (H * ((1 / 2 : ℝ) • P)).trace = 1 / 4 * (P * H).trace := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm H P, smul_eq_mul]
  ring

/-- [proved-standard] The trace of a diagonal step against a stiffness is the sum over entries of `P_ii H_ii`. -/
theorem trace_diagonal_mul (p : d → ℝ) (H : Matrix d d ℝ) :
    (Matrix.diagonal p * H).trace = ∑ i, p i * H i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

/-- [proved-derived] **A rate is a window**: the standing cost `¼ tr(PH)` of a diagonal step, taken against the least
excess `d/(2n)` of `d` entries estimated from `n` sites, is `n/2` times the mean over entries of `P_ii H_ii`. -/
theorem rate_is_window [Nonempty d] (p : d → ℝ) (H : Matrix d d ℝ) {n : ℝ} (hn : n ≠ 0) :
    1 / 4 * (Matrix.diagonal p * H).trace =
      (Fintype.card d : ℝ) / (2 * n) * (n / 2 * ((Fintype.card d : ℝ)⁻¹ * ∑ i, p i * H i i)) := by
  have hd : (Fintype.card d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [trace_diagonal_mul]
  field_simp
  ring

/-- [proved-derived] **An entry reads its last `2/(P_ii H_ii)` sections**: one entry's standing cost `¼ P_ii H_ii` is
the least excess `1/(2w)` of an estimate from `w = 2/(P_ii H_ii)` sites. -/
theorem entry_window (p h : ℝ) : 1 / 4 * (p * h) = 1 / (2 * (2 / (p * h))) := by
  field_simp
  ring

end Window

/-! ## 4. A lap-mean difference is its weights -/

section LapMean

variable {R : Type*} [CommRing R]

/-- [definition] A walk: the sum of its first `t` increments. -/
def walk (ε : ℕ → R) (t : ℕ) : R := ∑ u ∈ range t, ε u

/-- [definition] A lap's sum of the walk's states after each of its `n` steps; the lap mean is this over `n`. -/
def lapSum (ε : ℕ → R) (n k : ℕ) : R := ∑ j ∈ range n, walk ε (k * n + j + 1)

/-- [proved-standard] Summation by parts with rising weights:
`Σ_(i<m) i (a (i+1) − a i) = m a m − Σ_(i<m) a (i+1)`. -/
theorem abel_rising (a : ℕ → R) (m : ℕ) :
    ∑ i ∈ range m, (i : R) * (a (i + 1) - a i) = m * a m - ∑ i ∈ range m, a (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    push_cast
    ring

/-- [proved-standard] Summation by parts with falling weights:
`Σ_(i<m) (c − i) (b (i+1) − b i) = (c − m) b m − c b 0 + Σ_(i<m) b (i+1)`. -/
theorem abel_falling (c : R) (b : ℕ → R) (m : ℕ) :
    ∑ i ∈ range m, (c - i) * (b (i + 1) - b i) = (c - m) * b m - c * b 0 + ∑ i ∈ range m, b (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    push_cast
    ring

/-- [proved-standard] A walk's step is its increment. -/
theorem walk_succ_sub (ε : ℕ → R) (t : ℕ) : walk ε (t + 1) - walk ε t = ε t := by
  unfold walk
  rw [sum_range_succ]
  ring

/-- [proved-derived] **A lap-mean difference is its weights**, at the scale of the lap's length: the difference of
two successive lap sums is `Σ_(i<n) i ε (k n + i) + Σ_(i<n) (n − i) ε ((k+1) n + i)`. -/
theorem lapSum_succ_sub (ε : ℕ → R) (n k : ℕ) :
    lapSum ε n (k + 1) - lapSum ε n k =
      ∑ i ∈ range n, (i : R) * ε (k * n + i) + ∑ i ∈ range n, ((n : R) - i) * ε ((k + 1) * n + i) := by
  have h1 : ∑ i ∈ range n, (i : R) * ε (k * n + i) =
      n * walk ε (k * n + n) - ∑ i ∈ range n, walk ε (k * n + (i + 1)) := by
    rw [← abel_rising (fun i => walk ε (k * n + i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← walk_succ_sub ε (k * n + i)]
    rfl
  have h2 : ∑ i ∈ range n, ((n : R) - i) * ε ((k + 1) * n + i) =
      ((n : R) - n) * walk ε ((k + 1) * n + n) - n * walk ε ((k + 1) * n + 0) +
        ∑ i ∈ range n, walk ε ((k + 1) * n + (i + 1)) := by
    rw [← abel_falling (n : R) (fun i => walk ε ((k + 1) * n + i)) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← walk_succ_sub ε ((k + 1) * n + i)]
    rfl
  have hk : (k + 1) * n + 0 = k * n + n := by ring
  rw [h1, h2, hk]
  unfold lapSum
  simp only [add_assoc]
  ring

/-- [proved-derived] **A lap-mean difference is its weights**: over a field, with `M k = (1/n) Σ_(j<n) X (k n + j + 1)`,
`n (M (k+1) − M k) = Σ_(i<n) i ε (k n + i) + Σ_(i<n) (n − i) ε ((k+1) n + i)`. -/
theorem lapMean_succ_sub {K : Type*} [Field K] (ε : ℕ → K) (n k : ℕ) (hn : (n : K) ≠ 0) :
    (n : K) * ((n : K)⁻¹ * lapSum ε n (k + 1) - (n : K)⁻¹ * lapSum ε n k) =
      ∑ i ∈ range n, (i : K) * ε (k * n + i) + ∑ i ∈ range n, ((n : K) - i) * ε ((k + 1) * n + i) := by
  rw [← lapSum_succ_sub]
  field_simp

end LapMean

/-! ## 5. The second moments of a lap-mean difference -/

section LapMoments

variable {Ω : Type*}

/-- [definition] The difference of two successive lap sums as its weights, at the offset `c` of the first lap: rising
weights on the lap at `c` and falling weights on the lap at `c + n`. -/
def lapDiff (ε : ℕ → Ω → ℝ) (n c : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, (i : ℝ) * ε (c + i) ω + ∑ i ∈ range n, ((n : ℝ) - i) * ε (c + n + i) ω

/-- [proved-derived] The difference of the lap sums `k + 1` and `k` of a sample's walk is `lapDiff` at `c = k n`. -/
theorem lapSum_succ_sub_eq_lapDiff (ε : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    lapSum (fun u => ε u ω) n (k + 1) - lapSum (fun u => ε u ω) n k = lapDiff ε n (k * n) ω := by
  rw [lapSum_succ_sub]
  unfold lapDiff
  have hidx : ∀ i, (k + 1) * n + i = k * n + n + i := fun i => by ring
  simp_rw [hidx]

/-- [definition] The increments' hypothesis: uncorrelated, each of the second moment `v`. -/
def UncorrelatedIncrements (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (ε : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  ∀ a b, E (fun ω => ε a ω * ε b ω) = if a = b then v else 0

private theorem mean_add4 (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f₁ f₂ f₃ f₄ : Ω → ℝ) :
    E (fun ω => f₁ ω + f₂ ω + f₃ ω + f₄ ω) = E f₁ + E f₂ + E f₃ + E f₄ := by
  have h : (fun ω => f₁ ω + f₂ ω + f₃ ω + f₄ ω) = f₁ + f₂ + f₃ + f₄ := by
    funext ω
    simp only [Pi.add_apply]
  rw [h, map_add, map_add, map_add]

private theorem mean_pair {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {ε : ℕ → Ω → ℝ} {v : ℝ} (hE : UncorrelatedIncrements E ε v)
    (n c c' : ℕ) (a b : ℕ → ℝ) :
    E (fun ω => (∑ i ∈ range n, a i * ε (c + i) ω) * (∑ j ∈ range n, b j * ε (c' + j) ω)) =
      v * ∑ i ∈ range n, ∑ j ∈ range n, (if c + i = c' + j then a i * b j else 0) := by
  have hE' : ∀ x y, E (fun ω => ε x ω * ε y ω) = if x = y then v else 0 := hE
  have hpt : ∀ ω, (∑ i ∈ range n, a i * ε (c + i) ω) * (∑ j ∈ range n, b j * ε (c' + j) ω) =
      ∑ i ∈ range n, ∑ j ∈ range n, (a i * b j) * (ε (c + i) ω * ε (c' + j) ω) := by
    intro ω
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, hE']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

private theorem dsum_diag (n c : ℕ) (a b : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if c + i = c + j then a i * b j else 0) = ∑ i ∈ range n, a i * b i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Nat.add_left_cancel_iff]
  rw [Finset.sum_ite_eq, if_pos hi]

private theorem dsum_off (n c c' : ℕ) (h : c + n ≤ c' ∨ c' + n ≤ c) (a b : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if c + i = c' + j then a i * b j else 0) = 0 := by
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  rw [if_neg]
  omega

/-- [proved-derived] **The own weight is the difference's second moment**: for uncorrelated increments of one second
moment `v`, the lap difference at the scale of the lap's length has the second moment
`v (Σ_(i<n) i² + Σ_(i<n) (n − i)²)`. -/
theorem lapDiff_second_moment {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {ε : ℕ → Ω → ℝ} {v : ℝ}
    (hE : UncorrelatedIncrements E ε v) (n c : ℕ) :
    E (fun ω => lapDiff ε n c ω * lapDiff ε n c ω) =
      v * (∑ i ∈ range n, (i : ℝ) ^ 2 + ∑ i ∈ range n, ((n : ℝ) - i) ^ 2) := by
  have hpt : ∀ ω, lapDiff ε n c ω * lapDiff ε n c ω =
      (∑ i ∈ range n, (i : ℝ) * ε (c + i) ω) * (∑ j ∈ range n, (j : ℝ) * ε (c + j) ω) +
      (∑ i ∈ range n, (i : ℝ) * ε (c + i) ω) * (∑ j ∈ range n, ((n : ℝ) - j) * ε (c + n + j) ω) +
      (∑ i ∈ range n, ((n : ℝ) - i) * ε (c + n + i) ω) * (∑ j ∈ range n, (j : ℝ) * ε (c + j) ω) +
      (∑ i ∈ range n, ((n : ℝ) - i) * ε (c + n + i) ω) *
        (∑ j ∈ range n, ((n : ℝ) - j) * ε (c + n + j) ω) := by
    intro ω
    unfold lapDiff
    ring
  have hAA := mean_pair hE n c c (fun i => (i : ℝ)) (fun j => (j : ℝ))
  have hAB := mean_pair hE n c (c + n) (fun i => (i : ℝ)) (fun j => (n : ℝ) - j)
  have hBA := mean_pair hE n (c + n) c (fun i => (n : ℝ) - i) (fun j => (j : ℝ))
  have hBB := mean_pair hE n (c + n) (c + n) (fun i => (n : ℝ) - i) (fun j => (n : ℝ) - j)
  rw [dsum_diag] at hAA hBB
  rw [dsum_off n c (c + n) (Or.inl le_rfl)] at hAB
  rw [dsum_off n (c + n) c (Or.inr le_rfl)] at hBA
  simp_rw [hpt]
  rw [mean_add4, hAA, hAB, hBA, hBB]
  have e1 : ∑ i ∈ range n, (i : ℝ) * (i : ℝ) = ∑ i ∈ range n, (i : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i ∈ range n, ((n : ℝ) - i) * ((n : ℝ) - i) = ∑ i ∈ range n, ((n : ℝ) - i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

/-- [proved-derived] **The shared weight is the mean product of two successive differences**: they share one lap's
increments at the weights `n − i` and `i`, so their mean product is `v Σ_(i<n) i (n − i)`. -/
theorem lapDiff_shared_moment {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {ε : ℕ → Ω → ℝ} {v : ℝ}
    (hE : UncorrelatedIncrements E ε v) (n c : ℕ) :
    E (fun ω => lapDiff ε n c ω * lapDiff ε n (c + n) ω) = v * ∑ i ∈ range n, (i : ℝ) * ((n : ℝ) - i) := by
  have hpt : ∀ ω, lapDiff ε n c ω * lapDiff ε n (c + n) ω =
      (∑ i ∈ range n, (i : ℝ) * ε (c + i) ω) * (∑ j ∈ range n, (j : ℝ) * ε (c + n + j) ω) +
      (∑ i ∈ range n, (i : ℝ) * ε (c + i) ω) * (∑ j ∈ range n, ((n : ℝ) - j) * ε (c + n + n + j) ω) +
      (∑ i ∈ range n, ((n : ℝ) - i) * ε (c + n + i) ω) * (∑ j ∈ range n, (j : ℝ) * ε (c + n + j) ω) +
      (∑ i ∈ range n, ((n : ℝ) - i) * ε (c + n + i) ω) *
        (∑ j ∈ range n, ((n : ℝ) - j) * ε (c + n + n + j) ω) := by
    intro ω
    unfold lapDiff
    ring
  have hAA := mean_pair hE n c (c + n) (fun i => (i : ℝ)) (fun j => (j : ℝ))
  have hAB := mean_pair hE n c (c + n + n) (fun i => (i : ℝ)) (fun j => (n : ℝ) - j)
  have hBA := mean_pair hE n (c + n) (c + n) (fun i => (n : ℝ) - i) (fun j => (j : ℝ))
  have hBB := mean_pair hE n (c + n) (c + n + n) (fun i => (n : ℝ) - i) (fun j => (n : ℝ) - j)
  rw [dsum_off n c (c + n) (Or.inl le_rfl)] at hAA
  rw [dsum_off n c (c + n + n) (Or.inl (by omega))] at hAB
  rw [dsum_diag] at hBA
  rw [dsum_off n (c + n) (c + n + n) (Or.inl le_rfl)] at hBB
  simp_rw [hpt]
  rw [mean_add4, hAA, hAB, hBA, hBB]
  have e1 : ∑ i ∈ range n, ((n : ℝ) - i) * (i : ℝ) = ∑ i ∈ range n, (i : ℝ) * ((n : ℝ) - i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1]
  ring

/-- [proved-standard] The falling weights' squares are the squares of `i + 1`: `Σ_(i<n) (n − i)² = Σ_(i<n) (i + 1)²`. -/
theorem sum_falling_sq (n : ℕ) : ∑ i ∈ range n, ((n : ℝ) - i) ^ 2 = ∑ i ∈ range n, ((i : ℝ) + 1) ^ 2 := by
  rw [← Finset.sum_range_reflect (fun i => ((i : ℝ) + 1) ^ 2) n]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have h1 : i ≤ n - 1 := by omega
  have h2 : 1 ≤ n := by omega
  show ((n : ℝ) - i) ^ 2 = (((n - 1 - i : ℕ) : ℝ) + 1) ^ 2
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_one]
  ring

/-- [proved-derived] **The second moment of a lap-mean difference**, at the scale of the lap's length: for
uncorrelated increments of one second moment `v` it is `v` times the own weight `Σ_(i<n) i² + Σ_(i<n) (i + 1)²`
of `Physics/Thermal/LapMean.six_mul_own`. -/
theorem lap_second_moment {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {ε : ℕ → Ω → ℝ} {v : ℝ}
    (hE : UncorrelatedIncrements E ε v) (n k : ℕ) :
    E (fun ω => (lapSum (fun u => ε u ω) n (k + 1) - lapSum (fun u => ε u ω) n k) ^ 2) =
      v * (∑ i ∈ range n, (i : ℝ) ^ 2 + ∑ i ∈ range n, ((i : ℝ) + 1) ^ 2) := by
  have hpt : ∀ ω, (lapSum (fun u => ε u ω) n (k + 1) - lapSum (fun u => ε u ω) n k) ^ 2 =
      lapDiff ε n (k * n) ω * lapDiff ε n (k * n) ω := fun ω => by
    rw [lapSum_succ_sub_eq_lapDiff, sq]
  simp_rw [hpt]
  rw [lapDiff_second_moment hE, sum_falling_sq]

/-- [proved-derived] **The mean product of two successive lap-mean differences**, at the scale of the lap's length:
`v` times the shared weight `Σ_(i<n) i (n − i)` of `Physics/Thermal/LapMean.six_mul_shared`. -/
theorem lap_shared_moment {E : (Ω → ℝ) →ₗ[ℝ] ℝ} {ε : ℕ → Ω → ℝ} {v : ℝ}
    (hE : UncorrelatedIncrements E ε v) (n k : ℕ) :
    E (fun ω => (lapSum (fun u => ε u ω) n (k + 1) - lapSum (fun u => ε u ω) n k) *
        (lapSum (fun u => ε u ω) n (k + 1 + 1) - lapSum (fun u => ε u ω) n (k + 1))) =
      v * ∑ i ∈ range n, (i : ℝ) * ((n : ℝ) - i) := by
  have hpt : ∀ ω, (lapSum (fun u => ε u ω) n (k + 1) - lapSum (fun u => ε u ω) n k) *
        (lapSum (fun u => ε u ω) n (k + 1 + 1) - lapSum (fun u => ε u ω) n (k + 1)) =
      lapDiff ε n (k * n) ω * lapDiff ε n (k * n + n) ω := fun ω => by
    rw [lapSum_succ_sub_eq_lapDiff, lapSum_succ_sub_eq_lapDiff, Nat.succ_mul]
  simp_rw [hpt]
  rw [lapDiff_shared_moment hE]

end LapMoments

end Holonics.Physics.Thermal.MeanOfStates
