import Holonics.Holon.Cayley
import Holonics.Objects.CommitRebase
import Holonics.HNN.LatticeDeposit

/-!
# HNN.WordSensitivity: passive Cayley words, the lattice certificate across loci, the counterfactual trajectory

[proved-derived; formal-checked] The box of #410: "Word sensitivity and the counterfactual
trajectory bound: `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)` through the declared deposition, transient and
inverse charts, active ports and junctions (`HNN/LatticeDeposit.remainder_below_grain` covers one
linear locus)." Sources: the obligation of the record of September 25 on the classical loss and the
deposition remainder, in `research/records/`,
`2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md`
(its Obligations): "the word-level certificate of the lattice rule, `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`, with `K_ℓ` the
word's sensitivity from locus `ℓ` to the logits. Passivity gives `‖dCay‖ ≤ ‖dK‖` when the element's
symmetric part is `⪯ 0`; the active contrast port needs its own bound. It joins
`Objects/CommitRebase`"; and the `[open]` paragraph of `HNN/LatticeDeposit`, where the
counterfactual bound `Σ_(i<n) K^(n−1−i) r_i` "remains owed". Atlas rows:
`holon.passive-cayley-contraction`, `holon.cayley-isometry`, `receipt.commit-chain-residual`,
`receipt.telephone-chain-budget`, `hnn.release-since-founding`, `hnn.carried-gram-posdef`,
`hnn.chart-release-read` and `hnn.contact-tolerance-gain-scope` (whose scope names the all-word
contraction and the changing sensitivity as owed).

[definition] The setting. `E` is a real inner-product space (finite-dimensional where an inverse
is named), an element is `K : E →L[ℝ] E`, and `K` is passive when `⟪v, K v⟫ ≤ 0` for every `v`
(its symmetric part `⪯ 0`). The Cayley step at `h ≥ 0`,
`Cay_h(K) = (I − (h/2)K)⁻¹(I + (h/2)K) = 2(I − (h/2)K)⁻¹ − I`, is stated on vectors as the relation
`IsCayleyStep h K A`, `(I − (h/2)K)(A p) = (I + (h/2)K)p`, which names no inverse, and in finite
dimension as the operator `cay h K` (through `Ring.inverse`). A word is the composite
`A_(n−1) ∘ ⋯ ∘ A_0` of its steps (`word`). Norms are vector norms; an operator-norm statement is the
vector statement for every `v`, as in `Holon/Cayley`. A carried value is released only by
partition at its declared tolerance, with its remainder accounted (`HNN/LatticeDeposit`); here the
remainder's reach through a word and a read is bounded.

[proved-derived; formal-checked] What is proved.

1. **Passivity gives `‖dCay‖ ≤ h‖dK‖`** (`cayley_step_sensitivity_at`, `cayley_step_sensitivity`,
   `IsCayleyStep.sensitivity`). Two Cayley steps at `h` from one `p` satisfy
   `(I − (h/2)K₁)(y₁ − y₂) = (h/2)(K₁ − K₂)(y₂ + p)`; with `K₁` passive alone,
   `‖y₁ − y₂‖ ≤ (h/2)‖(K₁ − K₂)(y₂ + p)‖`, and with `K₂` passive too and `‖(K₁ − K₂)w‖ ≤ L‖w‖`,
   `‖y₁ − y₂‖ ≤ hL‖p‖`. Each element is passive; their difference carries no sign. The steps
   reuse `Holon/Cayley.resolvent_bound` and `cayley_contraction` at `h • K` (`passive_smul`,
   `resolvent_step_bound`, `cayley_step_contraction`): a passive step is `1`-Lipschitz and a
   contraction (`IsCayleyStep.lipschitz`, `IsCayleyStep.norm_le`), and a skew step keeps the norm
   (`IsCayleyStep.norm_eq_of_skew`). In finite dimension (`denom_isUnit`, from
   `Holon/Cayley.cayley_bijective`): `Cay_h(K) = 2(I − (h/2)K)⁻¹ − I` (`cay_eq`),
   `Cay_h(K₁) − Cay_h(K₂) = h(I − (h/2)K₁)⁻¹(K₁ − K₂)(I − (h/2)K₂)⁻¹` (`cay_sub_cay`), `cay h K`
   satisfies the relation (`cay_isCayleyStep`), `‖Cay_h(K)‖ ≤ 1` (`norm_cay_le`) and
   `‖Cay_h(K₁) − Cay_h(K₂)‖ ≤ h‖K₁ − K₂‖` (`norm_cay_sub_le`); at `h = 1` the record's
   `‖dCay‖ ≤ ‖dK‖`.
2. **A word telescopes** (`norm_word_le`, `word_sensitivity`, `linear_word_sensitivity`,
   `contraction_word_sensitivity`). With `A_i` `ρ_i`-Lipschitz, `‖B_i u‖ ≤ ρ_i‖u‖` and
   `‖A_i u − B_i u‖ ≤ L_i‖u‖`, `‖(A_(n−1)⋯A_0 − B_(n−1)⋯B_0)v‖ ≤ Σ_i (∏_(j≠i) ρ_j) L_i ‖v‖`, by
   `Transport/AccumulatedReceiverDefect.distance_le_budget` (the telephone chain) with the defect
   `L_i ∏_(j<i) ρ_j ‖v‖` entering at locus `i`. An active locus's `ρ_i > 1` enters every other
   locus's sensitivity: that is the active port's own bound. For contractions the bound is
   `(Σ_i L_i)‖v‖`, and a word of passive Cayley steps has sensitivity `Σ_i h_i‖dK_i‖`, with no growth
   in the word's length (`passive_word_sensitivity`; the operator form `cay_word_sensitivity`).
3. **The read across loci** (`read_hybrid`, `read_within_certificate`). A read `R` over a finite
   family of loci whose change at one locus is at most `K_ℓ` times that locus's change, at every
   base point, satisfies `‖R x − R x′‖ ≤ Σ_ℓ K_ℓ‖x_ℓ − x′_ℓ‖` (the loci changed one at a time in a
   fixed order); with `‖x_ℓ − x′_ℓ‖ ≤ 2^(−L_ℓ)` and the certificate `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`
   the read moves by less than half the receiver's grain `1/L_R`. On loci carried by
   `HNN/LatticeDeposit` (`carried_entry_within_unit`, `carried_locus_within_unit`,
   `carried_read_within_certificate`): each carried locus, read in the sup norm, is within
   `2^(−L_ℓ)` of the accumulation of what reached it (`within_one_unit_since_founding`), so under the
   certificate the read of the carried loci is within `1/(2L_R)` of the read of their accumulations.
   `remainder_below_grain` is the case of one linear locus.
4. **The receiver's grain** (`gridIndex`, `gridIndex_sub_le_one`, `grid_point_sub_le`,
   `gridIndex_eq_of_margin`, `margin_strict_witness`). Reading `r` at the nearest point of `uℤ`
   (`round(r/u)`, ties upward): `|r − r′| < u/2` gives readings that differ by at most one grain
   point, and they agree when `r′` stands farther than `|r − r′|` from every tie `(k + ½)u`; the
   margin is strict (at distance equal to `|r − r′|` a tie read upward separates them). Under the
   certificate the receiver's reading of the carried word is the reading of the accumulation or its
   neighbour (`reading_within_neighbour`), and is that reading wherever the accumulation's read
   stands farther than `Σ_ℓ K_ℓ 2^(−L_ℓ)` from every tie (`reading_same_with_margin`).
5. **The counterfactual trajectory** (`counterfactual_trajectory`, `passive_trajectory`,
   `passive_trajectory_within`, `cayley_trajectory_within`). For `x_(i+1) = F_i(x_i) + r_i` and
   `y_(i+1) = F_i(y_i)` with `F_i` `K_i`-Lipschitz,
   `‖x_n − y_n‖ ≤ ‖x_0 − y_0‖ ∏_(i<n) K_i + Σ_(i<n) ‖r_i‖ ∏_(i<j<n) K_j` (`distance_le_budget`; at a
   constant `K` the `Objects/CommitRebase.commit_chain_residual` bound). For a passive word
   (`K_i ≤ 1`) this is `‖x_0 − y_0‖ + Σ_i ‖r_i‖`, and from one start with residuals summing below
   `u/2` the carried trajectory stays within `u/2` at every length. The releases of one carried
   entry since its founding sum below `u/2` in absolute value, `Σ_k |e_k| < u/2` (`releaseAt`,
   `released_eq_sum_releaseAt`, `abs_releaseAt_sum_le`, `abs_releaseAt_sum_lt`,
   `abs_releaseAt_sum_lt_real`: the per-deposit bound `release_bounded` and the Kraft tail
   `gamma_window_lt_one`), which is the form a Lipschitz propagation consumes, where
   `release_bounded_since_founding` bounds the signed sum. So a trajectory of `1`-Lipschitz maps
   whose residual at step `k` is at most the entry's `k`-th release stays within `2^(−L)/2` of the
   unrounded one at every length (`carried_trajectory_within_half_unit`): the `[open]` bound of
   `HNN/LatticeDeposit`, closed for passive words.
6. **Witnesses** (`skew_inner`, `rotation_isCayleyStep`, `scalar_isCayleyStep`, `active_half_step`,
   `word_scalar`, `word_scalar_first`, `active_word_witness`, `active_word_exceeds`). On
   `EuclideanSpace ℝ (Fin 2)` the skew `K = [[0, 1], [−1, 0]]` is passive and its Cayley step at
   `h = 1` is the rotation `[[3/5, 4/5], [−4/5, 3/5]]`, of norm one. The active `K = ½·I` (with
   `⟪v, Kv⟫ = ½‖v‖² > 0`) has `Cay_1(K) = (5/3)·I`, of gain `5/3`; a word of `n + 1` such steps whose
   first step is changed by `ε` changes by `ε(5/3)ⁿ‖v‖`, the active bound of item 2 attained, and
   for `n ≥ 1`, `ε > 0`, `v ≠ 0` above the `ε‖v‖` a word of contractions allows: passivity is
   load-bearing in item 2.

What is not claimed.

- The sensitivities `K_ℓ` of the engine's own deposition, transient and inverse charts, active
  ports and junctions as numbers: they are hypotheses here (a read's per-locus bound, a step's
  `‖(K_i − K′_i)w‖ ≤ L_i‖w‖`, a map's Lipschitz constant), as is any bound for a nonlinear chart
  beyond its Lipschitz constant.
- That the engine's deposit map is `1`-Lipschitz, or that a trajectory's residual is an entry's
  release: both enter `carried_trajectory_within_half_unit` as hypotheses. `carry_accounting`
  moves a carried total `value + rem` by the update less the release for a declared list of
  updates; a deposit map computed at the carried operands is not built here. For maps of gain
  above one `counterfactual_trajectory` gives the product form and no length-free bound.
- A passivation of an active port (a certified shift, `Holon/Cayley.shift_passive_iff`): the
  active port enters only through its gain.

The computational object is the helical pair interaction read on the word: each step is the
implicit-midpoint step of a pair's reaction, whose skew part turns (the rotation, the norm kept),
whose passive symmetric part dissipates (the norm never raised), and whose active part pumps (a
gain above one that every other locus's sensitivity carries). Of the winding guide's six general
objects this touches the pair (the step and its passivity), the tube (the word as a clocked span,
and the carried trajectory against the unrounded one along it), faces and placement (the
receiver's read at its grain, the ties and the margin) and the tower thread (the releases of the
locus's refining lattices, read through `HNN/LatticeDeposit`); the helix and the cell holonomy stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.WordSensitivity

open Holonics.HolonCore Holonics.Transport.AccumulatedReceiverDefect

/-! ## 1. The passive Cayley step at a step size `h` -/

section Step

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-standard; formal-checked] A passive element stays passive under a nonnegative step size. -/
theorem passive_smul {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    ∀ v, inner ℝ v ((h • K) v) ≤ 0 := by
  intro v
  rw [smul_apply, inner_smul_right]
  nlinarith [hK v]

/-- [proved-standard; formal-checked] The half step of `h • K` is the step `h / 2` of `K`. -/
theorem half_smul_apply (K : E →L[ℝ] E) (h : ℝ) (v : E) :
    (1 / 2 : ℝ) • (h • K) v = (h / 2) • K v := by
  rw [smul_apply, smul_smul]
  congr 1
  ring

/-- [proved-derived; formal-checked] **`‖(I − (h/2)K)⁻¹‖ ≤ 1`** for passive `K` and `h ≥ 0`:
`y − (h/2) K y = f` implies `‖y‖ ≤ ‖f‖` (`Holon/Cayley.resolvent_bound` at `h • K`). -/
theorem resolvent_step_bound {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h)
    {y f : E} (hy : y - (h / 2) • K y = f) : ‖y‖ ≤ ‖f‖ :=
  resolvent_bound (h • K) (passive_smul hK hh) (by rw [half_smul_apply]; exact hy)

/-- [definition] **`A` is a Cayley step of `K` at `h`**: `(I − (h/2)K)(A p) = (I + (h/2)K) p` for
every `p`, which says `A = (I − (h/2)K)⁻¹(I + (h/2)K)` without naming the inverse. -/
def IsCayleyStep (h : ℝ) (K : E →L[ℝ] E) (A : E → E) : Prop :=
  ∀ p, A p - (h / 2) • K (A p) = p + (h / 2) • K p

/-- [proved-derived; formal-checked] **The Cayley step at `h` of a passive `K` does not increase the
norm** (`Holon/Cayley.cayley_contraction` at `h • K`). -/
theorem cayley_step_contraction {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ}
    (hh : 0 ≤ h) {y p : E} (hy : y - (h / 2) • K y = p + (h / 2) • K p) : ‖y‖ ≤ ‖p‖ :=
  cayley_contraction (h • K) (passive_smul hK hh) (by rw [half_smul_apply, half_smul_apply]; exact hy)

/-- [proved-derived; formal-checked] A Cayley step of a passive `K` is `1`-Lipschitz: the relation
is linear, so the difference of two steps is the step of the difference. -/
theorem IsCayleyStep.lipschitz {h : ℝ} {K : E →L[ℝ] E} {A : E → E} (hA : IsCayleyStep h K A)
    (hK : ∀ v, inner ℝ v (K v) ≤ 0) (hh : 0 ≤ h) (p p' : E) : ‖A p - A p'‖ ≤ ‖p - p'‖ := by
  refine cayley_step_contraction hK hh ?_
  have h1 := hA p
  have h2 := hA p'
  rw [map_sub, map_sub]
  linear_combination (norm := module) h1 - h2

/-- [proved-derived; formal-checked] A Cayley step of a passive `K` is a contraction. -/
theorem IsCayleyStep.norm_le {h : ℝ} {K : E →L[ℝ] E} {A : E → E} (hA : IsCayleyStep h K A)
    (hK : ∀ v, inner ℝ v (K v) ≤ 0) (hh : 0 ≤ h) (p : E) : ‖A p‖ ≤ ‖p‖ :=
  cayley_step_contraction hK hh (hA p)

/-- [proved-standard; formal-checked] **A skew element's Cayley step keeps the norm**: with
`⟪v, K v⟫ = 0`, `⟪y + p, y − p⟫ = (h/2)⟪y + p, K(y + p)⟫ = 0`, so `‖y‖ = ‖p‖`. -/
theorem IsCayleyStep.norm_eq_of_skew {h : ℝ} {K : E →L[ℝ] E} {A : E → E} (hA : IsCayleyStep h K A)
    (hK : ∀ v, inner ℝ v (K v) = 0) (p : E) : ‖A p‖ = ‖p‖ := by
  have hrel : A p - p = (h / 2) • K (A p + p) := by
    have := hA p
    rw [map_add, smul_add]
    linear_combination (norm := module) this
  have h1 : inner ℝ (A p + p) (A p - p) = ‖A p‖ ^ 2 - ‖p‖ ^ 2 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm (A p) p]
    ring
  have h2 : inner ℝ (A p + p) (A p - p) = 0 := by
    rw [hrel, inner_smul_right, hK, mul_zero]
  have h3 : ‖A p‖ ^ 2 = ‖p‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-- [proved-derived; formal-checked] **The difference of two Cayley steps, one side passive.** If
`y₁` and `y₂` are the Cayley steps at `h` of `K₁` and `K₂` from the same `p`, then
`(I − (h/2)K₁)(y₁ − y₂) = (h/2)(K₁ − K₂)(y₂ + p)`, and with `K₁` passive
`‖y₁ − y₂‖ ≤ (h/2)‖(K₁ − K₂)(y₂ + p)‖`. The difference `K₁ − K₂` carries no sign hypothesis. -/
theorem cayley_step_sensitivity_at {K₁ K₂ : E →L[ℝ] E} (hK₁ : ∀ v, inner ℝ v (K₁ v) ≤ 0) {h : ℝ}
    (hh : 0 ≤ h) {p y₁ y₂ : E} (h₁ : y₁ - (h / 2) • K₁ y₁ = p + (h / 2) • K₁ p)
    (h₂ : y₂ - (h / 2) • K₂ y₂ = p + (h / 2) • K₂ p) :
    ‖y₁ - y₂‖ ≤ h / 2 * ‖(K₁ - K₂) (y₂ + p)‖ := by
  have hrel : (y₁ - y₂) - (h / 2) • K₁ (y₁ - y₂) = (h / 2) • (K₁ - K₂) (y₂ + p) := by
    rw [map_sub, sub_apply, map_add, map_add]
    linear_combination (norm := module) h₁ - h₂
  calc ‖y₁ - y₂‖ ≤ ‖(h / 2) • (K₁ - K₂) (y₂ + p)‖ := resolvent_step_bound hK₁ hh hrel
    _ = h / 2 * ‖(K₁ - K₂) (y₂ + p)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]

/-- [proved-derived; formal-checked] **Passivity gives `‖dCay‖ ≤ h‖dK‖`.** For passive `K₁`, `K₂`,
`h ≥ 0` and `‖(K₁ − K₂) w‖ ≤ L‖w‖` for every `w`, the Cayley steps at `h` from the same `p` differ by
at most `h L ‖p‖`. Each element is passive; their difference need not be. -/
theorem cayley_step_sensitivity {K₁ K₂ : E →L[ℝ] E} (hK₁ : ∀ v, inner ℝ v (K₁ v) ≤ 0)
    (hK₂ : ∀ v, inner ℝ v (K₂ v) ≤ 0) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hdK : ∀ w, ‖(K₁ - K₂) w‖ ≤ L * ‖w‖) {p y₁ y₂ : E}
    (h₁ : y₁ - (h / 2) • K₁ y₁ = p + (h / 2) • K₁ p)
    (h₂ : y₂ - (h / 2) • K₂ y₂ = p + (h / 2) • K₂ p) : ‖y₁ - y₂‖ ≤ h * L * ‖p‖ := by
  have hsum : ‖y₂ + p‖ ≤ ‖(2 : ℝ) • p‖ := by
    refine resolvent_step_bound hK₂ hh ?_
    rw [map_add, smul_add]
    linear_combination (norm := module) h₂
  rw [norm_smul, Real.norm_two] at hsum
  calc ‖y₁ - y₂‖ ≤ h / 2 * ‖(K₁ - K₂) (y₂ + p)‖ := cayley_step_sensitivity_at hK₁ hh h₁ h₂
    _ ≤ h / 2 * (L * ‖y₂ + p‖) := mul_le_mul_of_nonneg_left (hdK _) (by linarith)
    _ ≤ h / 2 * (L * (2 * ‖p‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hL) (by linarith)
    _ = h * L * ‖p‖ := by ring

/-- [proved-derived; formal-checked] `cayley_step_sensitivity` on two Cayley steps as maps. -/
theorem IsCayleyStep.sensitivity {h L : ℝ} {K₁ K₂ : E →L[ℝ] E} {A₁ A₂ : E → E}
    (hA₁ : IsCayleyStep h K₁ A₁) (hA₂ : IsCayleyStep h K₂ A₂) (hK₁ : ∀ v, inner ℝ v (K₁ v) ≤ 0)
    (hK₂ : ∀ v, inner ℝ v (K₂ v) ≤ 0) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hdK : ∀ w, ‖(K₁ - K₂) w‖ ≤ L * ‖w‖) (p : E) : ‖A₁ p - A₂ p‖ ≤ h * L * ‖p‖ :=
  cayley_step_sensitivity hK₁ hK₂ hh hL hdK (hA₁ p) (hA₂ p)

end Step

/-! ## 2. The operator form in finite dimension -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- [definition] The denominator `I − (h/2)K` of the Cayley step. -/
def denom (h : ℝ) (K : E →L[ℝ] E) : E →L[ℝ] E := 1 - (h / 2) • K

/-- [definition] The resolvent `(I − (h/2)K)⁻¹` (`Ring.inverse`, a unit for passive `K`). -/
def resolvent (h : ℝ) (K : E →L[ℝ] E) : E →L[ℝ] E := Ring.inverse (denom h K)

/-- [definition] The Cayley step `Cay_h(K) = (I − (h/2)K)⁻¹(I + (h/2)K)`. -/
def cay (h : ℝ) (K : E →L[ℝ] E) : E →L[ℝ] E := resolvent h K * (1 + (h / 2) • K)

/-- [proved-derived; formal-checked] In finite dimension `I − (h/2)K` is a unit for passive `K` and
`h ≥ 0` (`Holon/Cayley.cayley_bijective` at `h • K`). -/
theorem denom_isUnit {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    IsUnit (denom h K) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hb := cayley_bijective (h • K) (passive_smul hK hh)
  convert hb using 1
  funext v
  simp only [denom, sub_apply, one_apply_eq_self,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
  rw [half_smul_apply, smul_apply]

/-- [proved-standard; formal-checked] `Cay_h(K) = 2(I − (h/2)K)⁻¹ − I`. -/
theorem cay_eq {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    cay h K = (2 : ℝ) • resolvent h K - 1 := by
  have hu := Ring.inverse_mul_cancel _ (denom_isUnit hK hh)
  have hplus : (1 : E →L[ℝ] E) + (h / 2) • K = (2 : ℝ) • 1 - denom h K := by
    simp only [denom]
    module
  rw [cay, hplus, mul_sub, mul_smul_comm, mul_one, resolvent, hu]

/-- [proved-standard; formal-checked] **The difference of two Cayley steps** (the resolvent identity):
`Cay_h(K₁) − Cay_h(K₂) = h (I − (h/2)K₁)⁻¹ (K₁ − K₂) (I − (h/2)K₂)⁻¹` for passive `K₁`, `K₂`. -/
theorem cay_sub_cay {K₁ K₂ : E →L[ℝ] E} (hK₁ : ∀ v, inner ℝ v (K₁ v) ≤ 0)
    (hK₂ : ∀ v, inner ℝ v (K₂ v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    cay h K₁ - cay h K₂ = h • (resolvent h K₁ * (K₁ - K₂) * resolvent h K₂) := by
  have hl := Ring.inverse_mul_cancel _ (denom_isUnit hK₁ hh)
  have hr := Ring.mul_inverse_cancel _ (denom_isUnit hK₂ hh)
  have hdiff : denom h K₂ - denom h K₁ = (h / 2) • (K₁ - K₂) := by
    simp only [denom]
    module
  have hres : resolvent h K₁ - resolvent h K₂ =
      resolvent h K₁ * (denom h K₂ - denom h K₁) * resolvent h K₂ := by
    rw [mul_sub, sub_mul, mul_assoc, resolvent, resolvent, hr, mul_one, hl, one_mul]
  rw [cay_eq hK₁ hh, cay_eq hK₂ hh, sub_sub_sub_cancel_right, ← smul_sub, hres, hdiff,
    mul_smul_comm, smul_mul_assoc, smul_smul]
  congr 1
  ring

/-- [proved-derived; formal-checked] `Cay_h(K)` is a Cayley step of `K` at `h` (`IsCayleyStep`). -/
theorem cay_isCayleyStep {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    IsCayleyStep h K (cay h K) := by
  intro p
  have hu := Ring.mul_inverse_cancel _ (denom_isUnit hK hh)
  have hD : ∀ w, w - (h / 2) • K w = denom h K w := fun w => by
    simp [denom]
  rw [hD, cay, mul_apply_eq_comp, ← mul_apply_eq_comp (denom h K), resolvent,
    hu, one_apply_eq_self]
  simp

/-- [proved-derived; formal-checked] **`‖Cay_h(K)‖ ≤ 1`** for passive `K`, in the operator norm. -/
theorem norm_cay_le {K : E →L[ℝ] E} (hK : ∀ v, inner ℝ v (K v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    ‖cay h K‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by
    rw [one_mul]
    exact (cay_isCayleyStep hK hh).norm_le hK hh p

/-- [proved-derived; formal-checked] **`‖Cay_h(K₁) − Cay_h(K₂)‖ ≤ h‖K₁ − K₂‖`** for passive `K₁`,
`K₂`, in the operator norm; at `h = 1` the record's `‖dCay‖ ≤ ‖dK‖`. -/
theorem norm_cay_sub_le {K₁ K₂ : E →L[ℝ] E} (hK₁ : ∀ v, inner ℝ v (K₁ v) ≤ 0)
    (hK₂ : ∀ v, inner ℝ v (K₂ v) ≤ 0) {h : ℝ} (hh : 0 ≤ h) :
    ‖cay h K₁ - cay h K₂‖ ≤ h * ‖K₁ - K₂‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hh (norm_nonneg _)) fun p => by
    rw [sub_apply]
    exact (cay_isCayleyStep hK₁ hh).sensitivity (cay_isCayleyStep hK₂ hh) hK₁ hK₂ hh
      (norm_nonneg _) (fun w => (K₁ - K₂).le_opNorm w) p

end Operator

/-! ## 3. A word of steps telescopes -/

section Word

/-- [definition] **The word** `A_(n−1) ∘ ⋯ ∘ A_0` of the steps `A_0, A_1, …`. -/
def word {X : Type*} (A : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | n + 1 => A n ∘ word A n

/-- [definition] The empty word is the identity. -/
@[simp] theorem word_zero {X : Type*} (A : ℕ → X → X) (v : X) : word A 0 v = v := rfl

/-- [definition] The word of `n + 1` steps applies step `n` last. -/
@[simp] theorem word_succ {X : Type*} (A : ℕ → X → X) (n : ℕ) (v : X) :
    word A (n + 1) v = A n (word A n v) := rfl

variable {X : Type*} [NormedAddCommGroup X]

/-- [proved-standard; formal-checked] A word of steps of gains `ρ_j` has gain at most `∏ ρ_j`. -/
theorem norm_word_le (B : ℕ → X → X) (ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hB : ∀ i u, ‖B i u‖ ≤ ρ i * ‖u‖) (n : ℕ) (v : X) :
    ‖word B n v‖ ≤ (∏ j ∈ Finset.range n, ρ j) * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [word_succ, Finset.prod_range_succ]
    calc ‖B n (word B n v)‖ ≤ ρ n * ‖word B n v‖ := hB n _
      _ ≤ ρ n * ((∏ j ∈ Finset.range n, ρ j) * ‖v‖) := mul_le_mul_of_nonneg_left ih (hρ n)
      _ = (∏ j ∈ Finset.range n, ρ j) * ρ n * ‖v‖ := by ring

/-- [proved-standard; formal-checked] The loci other than `i` are those before it and those after it. -/
theorem prod_erase_eq (f : ℕ → ℝ) {i n : ℕ} (hi : i < n) :
    ∏ j ∈ (Finset.range n).erase i, f j =
      (∏ j ∈ Finset.range i, f j) * ∏ j ∈ Finset.Ico (i + 1) n, f j := by
  have hdisj : Disjoint (Finset.range i) (Finset.Ico (i + 1) n) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range, Finset.mem_Ico] at hj hj'
    omega
  rw [← Finset.prod_union hdisj]
  congr 1
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  omega

/-- [proved-derived; formal-checked] **A word telescopes** (the hybrid over its loci). With `A_i`
`ρ_i`-Lipschitz, `‖B_i u‖ ≤ ρ_i‖u‖` and `‖A_i u − B_i u‖ ≤ L_i‖u‖`,
`‖(A_(n−1)⋯A_0 − B_(n−1)⋯B_0) v‖ ≤ Σ_(i<n) (∏_(j≠i) ρ_j) L_i ‖v‖`
(`Transport/AccumulatedReceiverDefect.distance_le_budget`, the telephone chain, with the defect
`L_i ∏_(j<i) ρ_j ‖v‖` at locus `i`). -/
theorem word_sensitivity (A B : ℕ → X → X) (ρ L : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hL : ∀ i, 0 ≤ L i) (hA : ∀ i u u', ‖A i u - A i u'‖ ≤ ρ i * ‖u - u'‖)
    (hB : ∀ i u, ‖B i u‖ ≤ ρ i * ‖u‖) (hAB : ∀ i u, ‖A i u - B i u‖ ≤ L i * ‖u‖) (n : ℕ)
    (v : X) :
    ‖word A n v - word B n v‖ ≤
      (∑ i ∈ Finset.range n, (∏ j ∈ (Finset.range n).erase i, ρ j) * L i) * ‖v‖ := by
  have hbud := distance_le_budget A B (fun k => word A k v) (fun k => word B k v) ρ
    (fun k => L k * ((∏ j ∈ Finset.range k, ρ j) * ‖v‖)) 0 (by simp) (fun _ => rfl)
    (fun _ => rfl) hρ
    (fun k => mul_nonneg (hL k) (mul_nonneg (Finset.prod_nonneg fun j _ => hρ j) (norm_nonneg v)))
    hA (fun k => (hAB k _).trans (mul_le_mul_of_nonneg_left (norm_word_le B ρ hρ hB k v) (hL k))) n
  refine hbud.trans (le_of_eq ?_)
  simp only [expansion, zero_mul, zero_add, ← Finset.range_eq_Ico]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [prod_erase_eq ρ (Finset.mem_range.mp hi)]
  ring

/-- [proved-derived; formal-checked] **A word of contractions telescopes:** with every `A_i`
`1`-Lipschitz, `‖B_i u‖ ≤ ‖u‖` and `‖A_i u − B_i u‖ ≤ L_i‖u‖`, the words differ by at most
`(Σ_(i<n) L_i)‖v‖`, with no growth in the word's length. -/
theorem contraction_word_sensitivity (A B : ℕ → X → X) (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hA : ∀ i u u', ‖A i u - A i u'‖ ≤ ‖u - u'‖) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (hAB : ∀ i u, ‖A i u - B i u‖ ≤ L i * ‖u‖) (n : ℕ) (v : X) :
    ‖word A n v - word B n v‖ ≤ (∑ i ∈ Finset.range n, L i) * ‖v‖ := by
  have h := word_sensitivity A B (fun _ => 1) L (fun _ => zero_le_one) hL
    (fun i u u' => by rw [one_mul]; exact hA i u u') (fun i u => by rw [one_mul]; exact hB i u)
    hAB n v
  simpa only [Finset.prod_const_one, one_mul] using h

/-- [proved-derived; formal-checked] **The linear form** (the record's maps): for continuous linear
`A_i`, `B_i` with `‖A_i u‖ ≤ ρ_i‖u‖`, `‖B_i u‖ ≤ ρ_i‖u‖` and `‖(A_i − B_i) u‖ ≤ L_i‖u‖`, the words
differ by at most `Σ_i (∏_(j≠i) ρ_j) L_i ‖v‖`; an active locus's `ρ_i > 1` enters every other
locus's sensitivity. -/
theorem linear_word_sensitivity [NormedSpace ℝ X] (A B : ℕ → X →L[ℝ] X) (ρ L : ℕ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hA : ∀ i u, ‖A i u‖ ≤ ρ i * ‖u‖)
    (hB : ∀ i u, ‖B i u‖ ≤ ρ i * ‖u‖) (hAB : ∀ i u, ‖(A i - B i) u‖ ≤ L i * ‖u‖) (n : ℕ) (v : X) :
    ‖word (fun i => ⇑(A i)) n v - word (fun i => ⇑(B i)) n v‖ ≤
      (∑ i ∈ Finset.range n, (∏ j ∈ (Finset.range n).erase i, ρ j) * L i) * ‖v‖ :=
  word_sensitivity _ _ ρ L hρ hL (fun i u u' => by rw [← map_sub]; exact hA i _) hB
    (fun i u => by rw [← sub_apply]; exact hAB i u) n v

end Word

/-! ## 4. A word of passive Cayley steps -/

section PassiveWord

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **A word of passive Cayley steps has sensitivity
`Σ_i h_i‖dK_i‖`.** Steps `A_i`, `B_i` that are Cayley steps at `h_i ≥ 0` of passive `K_i`, `K'_i`
with `‖(K_i − K'_i) w‖ ≤ L_i‖w‖` give words within `(Σ_(i<n) h_i L_i)‖v‖`: no growth in the word's
length. -/
theorem passive_word_sensitivity (A B : ℕ → E → E) (K K' : ℕ → E →L[ℝ] E) (h L : ℕ → ℝ)
    (hA : ∀ i, IsCayleyStep (h i) (K i) (A i)) (hB : ∀ i, IsCayleyStep (h i) (K' i) (B i))
    (hK : ∀ i v, inner ℝ v (K i v) ≤ 0) (hK' : ∀ i v, inner ℝ v (K' i v) ≤ 0)
    (hh : ∀ i, 0 ≤ h i) (hL : ∀ i, 0 ≤ L i) (hdK : ∀ i w, ‖(K i - K' i) w‖ ≤ L i * ‖w‖)
    (n : ℕ) (v : E) :
    ‖word A n v - word B n v‖ ≤ (∑ i ∈ Finset.range n, h i * L i) * ‖v‖ :=
  contraction_word_sensitivity A B (fun i => h i * L i) (fun i => mul_nonneg (hh i) (hL i))
    (fun i => (hA i).lipschitz (hK i) (hh i)) (fun i => (hB i).norm_le (hK' i) (hh i))
    (fun i => (hA i).sensitivity (hB i) (hK i) (hK' i) (hh i) (hL i) (hdK i)) n v

/-- [proved-derived; formal-checked] **The operator form:** in finite dimension the words of the
Cayley steps `Cay_(h_i)(K_i)` and `Cay_(h_i)(K'_i)` of passive elements differ by at most
`(Σ_(i<n) h_i‖K_i − K'_i‖)‖v‖`. -/
theorem cay_word_sensitivity [FiniteDimensional ℝ E] (K K' : ℕ → E →L[ℝ] E) (h : ℕ → ℝ)
    (hK : ∀ i v, inner ℝ v (K i v) ≤ 0) (hK' : ∀ i v, inner ℝ v (K' i v) ≤ 0)
    (hh : ∀ i, 0 ≤ h i) (n : ℕ) (v : E) :
    ‖word (fun i => ⇑(cay (h i) (K i))) n v - word (fun i => ⇑(cay (h i) (K' i))) n v‖ ≤
      (∑ i ∈ Finset.range n, h i * ‖K i - K' i‖) * ‖v‖ :=
  passive_word_sensitivity _ _ K K' h (fun i => ‖K i - K' i‖)
    (fun i => cay_isCayleyStep (hK i) (hh i)) (fun i => cay_isCayleyStep (hK' i) (hh i)) hK hK' hh
    (fun _ => norm_nonneg _) (fun i w => (K i - K' i).le_opNorm w) n v

end PassiveWord

/-! ## 5. The read across loci -/

section Read

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ ℓ, NormedAddCommGroup (V ℓ)]
  {F : Type*} [NormedAddCommGroup F]

/-- [proved-standard; formal-checked] **The hybrid over loci.** A read `R` whose change at one
locus is at most `K_ℓ` times that locus's change, at every base point, satisfies
`‖R x − R x′‖ ≤ Σ_ℓ K_ℓ‖x_ℓ − x′_ℓ‖`: the loci are changed one at a time along a fixed order of
`ι` (Finset induction, the hybrid `s.piecewise x′ x`). -/
theorem read_hybrid (R : (∀ ℓ, V ℓ) → F) (K : ι → ℝ)
    (hR : ∀ (x : ∀ ℓ, V ℓ) (ℓ : ι) (e : V ℓ), ‖R (Function.update x ℓ e) - R x‖ ≤ K ℓ * ‖e - x ℓ‖)
    (x x' : ∀ ℓ, V ℓ) : ‖R x - R x'‖ ≤ ∑ ℓ, K ℓ * ‖x ℓ - x' ℓ‖ := by
  have key : ∀ s : Finset ι,
      ‖R (s.piecewise x' x) - R x‖ ≤ ∑ ℓ ∈ s, K ℓ * ‖x ℓ - x' ℓ‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert ha]
      have h1 := hR (s.piecewise x' x) a (x' a)
      rw [Finset.piecewise_eq_of_notMem s x' x ha, norm_sub_rev (x' a)] at h1
      calc ‖R (Function.update (s.piecewise x' x) a (x' a)) - R x‖
          ≤ ‖R (Function.update (s.piecewise x' x) a (x' a)) - R (s.piecewise x' x)‖ +
              ‖R (s.piecewise x' x) - R x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K a * ‖x a - x' a‖ + ∑ ℓ ∈ s, K ℓ * ‖x ℓ - x' ℓ‖ := add_le_add h1 ih
  have h := key Finset.univ
  rw [Finset.piecewise_univ] at h
  rwa [norm_sub_rev]

/-- [proved-derived; formal-checked] **The word-level certificate of the lattice rule.** With every
locus within one grain unit, `‖x_ℓ − x′_ℓ‖ ≤ 2^(−L_ℓ)`, nonnegative sensitivities and
`Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`, the read moves by less than `1/(2L_R)`: under half the receiver's
grain `1/L_R`. -/
theorem read_within_certificate (R : (∀ ℓ, V ℓ) → F) (K : ι → ℝ) (hK : ∀ ℓ, 0 ≤ K ℓ)
    (hR : ∀ (x : ∀ ℓ, V ℓ) (ℓ : ι) (e : V ℓ), ‖R (Function.update x ℓ e) - R x‖ ≤ K ℓ * ‖e - x ℓ‖)
    (Lw : ι → ℕ) (x x' : ∀ ℓ, V ℓ) (hx : ∀ ℓ, ‖x ℓ - x' ℓ‖ ≤ ((2 : ℝ) ^ Lw ℓ)⁻¹) {LR : ℝ}
    (hcert : ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ < 1 / (2 * LR)) : ‖R x - R x'‖ < 1 / (2 * LR) :=
  calc ‖R x - R x'‖ ≤ ∑ ℓ, K ℓ * ‖x ℓ - x' ℓ‖ := read_hybrid R K hR x x'
    _ ≤ ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ :=
        Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hx ℓ) (hK ℓ)
    _ < 1 / (2 * LR) := hcert

end Read

/-! ## 6. Carried loci: the lattice rule's deviation, read through the sup norm -/

section Carried

open Holonics.HNN.LatticeDeposit

/-- [proved-derived; formal-checked] One carried entry, read in `ℝ`, is within one grain unit
`2^(−L)` of the accumulation of what reached it (`LatticeDeposit.within_one_unit_since_founding`). -/
theorem carried_entry_within_unit {L : ℕ} {Ent : Type*} (s : Carried L Ent)
    (Δs : List (Ent → ℚ)) (i : Ent) :
    |((run s Δs).value i : ℝ) - ((s.value i + s.rem i + (Δs.map (· i)).sum : ℚ) : ℝ)| <
      ((2 : ℝ) ^ L)⁻¹ := by
  have h := Rat.cast_lt (K := ℝ) |>.mpr (within_one_unit_since_founding s Δs i)
  unfold unit at h
  rwa [Rat.cast_abs, Rat.cast_sub, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] at h

/-- [definition] A locus's carried entries after its run, read in `ℝ`. -/
def carriedRead {L : ℕ} {Ent : Type*} (s : Carried L Ent) (Δs : List (Ent → ℚ)) : Ent → ℝ :=
  fun i => ((run s Δs).value i : ℝ)

/-- [definition] A locus's accumulation of what reached it (start, remainder and updates), in `ℝ`. -/
def accumulatedRead {L : ℕ} {Ent : Type*} (s : Carried L Ent) (Δs : List (Ent → ℚ)) : Ent → ℝ :=
  fun i => ((s.value i + s.rem i + (Δs.map (· i)).sum : ℚ) : ℝ)

/-- [proved-derived; formal-checked] A carried locus of finitely many entries is within one grain
unit of its accumulation in the sup norm. -/
theorem carried_locus_within_unit {L : ℕ} {Ent : Type*} [Fintype Ent] (s : Carried L Ent)
    (Δs : List (Ent → ℚ)) : ‖carriedRead s Δs - accumulatedRead s Δs‖ < ((2 : ℝ) ^ L)⁻¹ := by
  rw [pi_norm_lt_iff (by positivity)]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact carried_entry_within_unit s Δs i

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ent : ι → Type*} [∀ ℓ, Fintype (Ent ℓ)]
  {F : Type*} [NormedAddCommGroup F]

/-- [proved-derived; formal-checked] **The certificate on carried loci.** Each locus `ℓ` carried on
its lattice `2^(−L_ℓ)ℤ` since its founding, a read with per-locus sensitivities `K_ℓ ≥ 0` in the
sup norm, and `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`: the read of the carried loci is within `1/(2L_R)` of
the read of their accumulations. -/
theorem carried_read_within_certificate (Lw : ι → ℕ) (s : ∀ ℓ, Carried (Lw ℓ) (Ent ℓ))
    (Δs : ∀ ℓ, List (Ent ℓ → ℚ)) (R : (∀ ℓ, Ent ℓ → ℝ) → F) (K : ι → ℝ) (hK : ∀ ℓ, 0 ≤ K ℓ)
    (hR : ∀ (x : ∀ ℓ, Ent ℓ → ℝ) (ℓ : ι) (e : Ent ℓ → ℝ),
      ‖R (Function.update x ℓ e) - R x‖ ≤ K ℓ * ‖e - x ℓ‖) {LR : ℝ}
    (hcert : ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ < 1 / (2 * LR)) :
    ‖R (fun ℓ => carriedRead (s ℓ) (Δs ℓ)) - R (fun ℓ => accumulatedRead (s ℓ) (Δs ℓ))‖ <
      1 / (2 * LR) :=
  read_within_certificate R K hK hR Lw _ _
    (fun ℓ => (carried_locus_within_unit (s ℓ) (Δs ℓ)).le) hcert

end Carried

/-! ## 7. The receiver's grain -/

section Grain

/-- [definition] **The receiver's reading at the grain `u`**: the index of the nearest point of
`uℤ`, ties upward (`round`). -/
def gridIndex (u r : ℝ) : ℤ := round (r / u)

/-- [proved-standard; formal-checked] **Within half a grain, the reading is the same or its
neighbour:** `|r − r′| < u/2` gives `|round(r/u) − round(r′/u)| ≤ 1`. -/
theorem gridIndex_sub_le_one {u r r' : ℝ} (hu : 0 < u) (h : |r - r'| < u / 2) :
    |gridIndex u r - gridIndex u r'| ≤ 1 := by
  unfold gridIndex
  have h1 := abs_sub_round (r / u)
  have h2 := abs_sub_round (r' / u)
  have h3 : |r / u - r' / u| < 1 / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hu, div_lt_iff₀ hu]
    linarith
  have h4 : |((round (r / u) - round (r' / u) : ℤ) : ℝ)| < 2 := by
    push_cast
    calc |(round (r / u) : ℝ) - round (r' / u)|
        = |-(r / u - round (r / u)) + (r / u - r' / u) + (r' / u - round (r' / u))| := by
          congr 1
          ring
      _ ≤ |-(r / u - round (r / u))| + |r / u - r' / u| + |r' / u - round (r' / u)| :=
          abs_add_three _ _ _
      _ < 2 := by rw [abs_neg]; linarith
  rw [← Int.cast_abs] at h4
  have h5 : |round (r / u) - round (r' / u)| < 2 := by exact_mod_cast h4
  omega

/-- [proved-standard; formal-checked] On the grain points: `|round(r/u)u − round(r′/u)u| ≤ u`. -/
theorem grid_point_sub_le {u r r' : ℝ} (hu : 0 < u) (h : |r - r'| < u / 2) :
    |(gridIndex u r : ℝ) * u - gridIndex u r' * u| ≤ u := by
  rw [← sub_mul, abs_mul, abs_of_pos hu]
  have h1 := gridIndex_sub_le_one hu h
  have h2 : |((gridIndex u r - gridIndex u r' : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  push_cast at h2
  nlinarith

/-- [proved-standard; formal-checked] **With margin, the reading is the same:** if `r′` stands
farther than `|r − r′|` from every tie `(k + ½)u`, then `round(r/u) = round(r′/u)`. -/
theorem gridIndex_eq_of_margin {u r r' : ℝ} (hu : 0 < u)
    (h : ∀ k : ℤ, |r - r'| < |r' - (k + 1 / 2) * u|) : gridIndex u r = gridIndex u r' := by
  unfold gridIndex
  set n := round (r' / u) with hn
  have hc := (round_eq_iff.mp hn.symm)
  rw [Set.mem_Ico, le_div_iff₀ hu, div_lt_iff₀ hu] at hc
  have hup := h n
  have hdown := h (n - 1)
  push_cast at hdown
  rw [abs_of_neg (show r' - ((n : ℝ) + 1 / 2) * u < 0 by linarith)] at hup
  rw [abs_of_nonneg (show 0 ≤ r' - ((n : ℝ) - 1 + 1 / 2) * u by linarith)] at hdown
  have h1 := le_abs_self (r - r')
  have h2 := neg_abs_le (r - r')
  refine round_eq_iff.mpr ?_
  rw [Set.mem_Ico, le_div_iff₀ hu, div_lt_iff₀ hu]
  constructor <;> linarith

/-- [proved-standard; formal-checked] **The margin is strict.** At the grain `1`, `3/10` stands at
distance `1/5 = |3/10 − 1/2|` from the tie `1/2` and farther from every other tie, yet
`round(3/10) = 0` and `round(1/2) = 1`: a tie is read upward. -/
theorem margin_strict_witness :
    (∀ k : ℤ, |(3 / 10 : ℝ) - 1 / 2| ≤ |(3 / 10 : ℝ) - (k + 1 / 2) * 1|) ∧
      gridIndex 1 (3 / 10) ≠ gridIndex 1 (1 / 2) := by
  refine ⟨fun k => ?_, ?_⟩
  · rcases le_or_gt 0 k with hk | hk
    · have : (0 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_neg (by norm_num), abs_of_neg (by linarith)]
      linarith
    · have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast Int.lt_iff_add_one_le.mp hk
      rw [abs_of_neg (by norm_num), abs_of_pos (by linarith)]
      linarith
  · unfold gridIndex
    rw [div_one, div_one]
    have h1 : round (3 / 10 : ℝ) = 0 := round_eq_iff.mpr (by norm_num)
    have h2 : round (1 / 2 : ℝ) = 1 := round_eq_iff.mpr (by norm_num)
    rw [h1, h2]
    norm_num

end Grain

/-! ## 8. The certificate read at the receiver's grain -/

section Reading

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ ℓ, NormedAddCommGroup (V ℓ)]

/-- [proved-derived; formal-checked] **Under the certificate the receiver reads the same point or
its neighbour.** A scalar read with per-locus sensitivities `K_ℓ ≥ 0`, loci within `2^(−L_ℓ)`, and
`Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`: at the grain `1/L_R` the two readings differ by at most one. -/
theorem reading_within_neighbour (R : (∀ ℓ, V ℓ) → ℝ) (K : ι → ℝ) (hK : ∀ ℓ, 0 ≤ K ℓ)
    (hR : ∀ (x : ∀ ℓ, V ℓ) (ℓ : ι) (e : V ℓ), ‖R (Function.update x ℓ e) - R x‖ ≤ K ℓ * ‖e - x ℓ‖)
    (Lw : ι → ℕ) (x x' : ∀ ℓ, V ℓ) (hx : ∀ ℓ, ‖x ℓ - x' ℓ‖ ≤ ((2 : ℝ) ^ Lw ℓ)⁻¹) {LR : ℝ}
    (hLR : 0 < LR) (hcert : ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ < 1 / (2 * LR)) :
    |gridIndex (1 / LR) (R x) - gridIndex (1 / LR) (R x')| ≤ 1 := by
  refine gridIndex_sub_le_one (by positivity) ?_
  have h := read_within_certificate R K hK hR Lw x x' hx hcert
  rw [Real.norm_eq_abs] at h
  calc |R x - R x'| < 1 / (2 * LR) := h
    _ = 1 / LR / 2 := by ring

/-- [proved-derived; formal-checked] **With margin the receiver reads the same point.** If the
read `R x′` stands farther than `Σ_ℓ K_ℓ 2^(−L_ℓ)` from every tie `(k + ½)/L_R`, the reading of
`x` at the grain `1/L_R` is the reading of `x′`. -/
theorem reading_same_with_margin (R : (∀ ℓ, V ℓ) → ℝ) (K : ι → ℝ) (hK : ∀ ℓ, 0 ≤ K ℓ)
    (hR : ∀ (x : ∀ ℓ, V ℓ) (ℓ : ι) (e : V ℓ), ‖R (Function.update x ℓ e) - R x‖ ≤ K ℓ * ‖e - x ℓ‖)
    (Lw : ι → ℕ) (x x' : ∀ ℓ, V ℓ) (hx : ∀ ℓ, ‖x ℓ - x' ℓ‖ ≤ ((2 : ℝ) ^ Lw ℓ)⁻¹) {LR : ℝ}
    (hLR : 0 < LR)
    (hmargin : ∀ k : ℤ, ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ < |R x' - (k + 1 / 2) * (1 / LR)|) :
    gridIndex (1 / LR) (R x) = gridIndex (1 / LR) (R x') := by
  refine gridIndex_eq_of_margin (by positivity) fun k => ?_
  have h := read_hybrid R K hR x x'
  rw [Real.norm_eq_abs] at h
  have hs : ∑ ℓ, K ℓ * ‖x ℓ - x' ℓ‖ ≤ ∑ ℓ, K ℓ * ((2 : ℝ) ^ Lw ℓ)⁻¹ :=
    Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hx ℓ) (hK ℓ)
  linarith [hmargin k]

end Reading

/-! ## 9. The counterfactual trajectory -/

section Trajectory

variable {X : Type*} [NormedAddCommGroup X]

/-- [proved-derived; formal-checked] **The counterfactual trajectory bound.** The carried
trajectory `x_(i+1) = F_i(x_i) + r_i` and the trajectory `y_(i+1) = F_i(y_i)` of the same
`K_i`-Lipschitz maps satisfy
`‖x_n − y_n‖ ≤ ‖x_0 − y_0‖ ∏_(i<n) K_i + Σ_(i<n) ‖r_i‖ ∏_(i<j<n) K_j`
(`Transport/AccumulatedReceiverDefect.distance_le_budget`; at a constant `K` and `x_0 = y_0` the
`Objects/CommitRebase.commit_chain_residual` bound `Σ_(i<n) K^(n−1−i) ‖r_i‖`). -/
theorem counterfactual_trajectory (F : ℕ → X → X) (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i)
    (lip : ∀ i a b, ‖F i a - F i b‖ ≤ K i * ‖a - b‖) (r x y : ℕ → X)
    (hx : ∀ i, x (i + 1) = F i (x i) + r i) (hy : ∀ i, y (i + 1) = F i (y i)) (n : ℕ) :
    ‖x n - y n‖ ≤ ‖x 0 - y 0‖ * ∏ i ∈ Finset.range n, K i +
      ∑ i ∈ Finset.range n, ‖r i‖ * ∏ j ∈ Finset.Ico (i + 1) n, K j := by
  have h := distance_le_budget F (fun i z => F i z + r i) y x K (fun i => ‖r i‖) ‖y 0 - x 0‖
    le_rfl hy hx hK (fun i => norm_nonneg _) lip (fun i => by simp) n
  rw [norm_sub_rev] at h
  refine h.trans (le_of_eq ?_)
  simp only [expansion, ← Finset.range_eq_Ico, norm_sub_rev (y 0)]

/-- [proved-derived; formal-checked] **A passive trajectory adds its residuals:** with every `F_i`
`1`-Lipschitz, `‖x_n − y_n‖ ≤ ‖x_0 − y_0‖ + Σ_(i<n) ‖r_i‖`, whatever the length. -/
theorem passive_trajectory (F : ℕ → X → X) (lip : ∀ i a b, ‖F i a - F i b‖ ≤ ‖a - b‖)
    (r x y : ℕ → X) (hx : ∀ i, x (i + 1) = F i (x i) + r i) (hy : ∀ i, y (i + 1) = F i (y i))
    (n : ℕ) : ‖x n - y n‖ ≤ ‖x 0 - y 0‖ + ∑ i ∈ Finset.range n, ‖r i‖ := by
  have h := counterfactual_trajectory F (fun _ => 1) (fun _ => zero_le_one)
    (fun i a b => by rw [one_mul]; exact lip i a b) r x y hx hy n
  simpa only [Finset.prod_const_one, mul_one] using h

/-- [proved-derived; formal-checked] **Within half a unit at every length:** a passive trajectory
started at `x_0 = y_0` whose residuals sum below `u/2` stays within `u/2` of the unrounded one. -/
theorem passive_trajectory_within (F : ℕ → X → X) (lip : ∀ i a b, ‖F i a - F i b‖ ≤ ‖a - b‖)
    (r x y : ℕ → X) (hx : ∀ i, x (i + 1) = F i (x i) + r i) (hy : ∀ i, y (i + 1) = F i (y i))
    (h0 : x 0 = y 0) {u : ℝ} (n : ℕ) (hr : ∑ i ∈ Finset.range n, ‖r i‖ < u / 2) :
    ‖x n - y n‖ < u / 2 := by
  have h := passive_trajectory F lip r x y hx hy n
  rw [h0, sub_self, norm_zero, zero_add] at h
  exact h.trans_lt hr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **A carried word of passive Cayley steps** stays within `u/2`
of the unrounded word when its residuals sum below `u/2` (`IsCayleyStep.lipschitz`). -/
theorem cayley_trajectory_within (A : ℕ → E → E) (K : ℕ → E →L[ℝ] E) (h : ℕ → ℝ)
    (hA : ∀ i, IsCayleyStep (h i) (K i) (A i)) (hK : ∀ i v, inner ℝ v (K i v) ≤ 0)
    (hh : ∀ i, 0 ≤ h i) (r x y : ℕ → E) (hx : ∀ i, x (i + 1) = A i (x i) + r i)
    (hy : ∀ i, y (i + 1) = A i (y i)) (h0 : x 0 = y 0) {u : ℝ} (n : ℕ)
    (hr : ∑ i ∈ Finset.range n, ‖r i‖ < u / 2) : ‖x n - y n‖ < u / 2 :=
  passive_trajectory_within A (fun i => (hA i).lipschitz (hK i) (hh i)) r x y hx hy h0 n hr

end Trajectory

/-! ## 10. The releases since the founding, summed in norm -/

section Releases

open Holonics.HNN.LatticeDeposit

variable {L : ℕ} {Ent : Type*}

/-- [definition] The residual the `k`-th deposit of a run releases at an entry (zero past the
run's end). -/
noncomputable def releaseAt : Carried L Ent → List (Ent → ℚ) → ℕ → Ent → ℚ
  | _, [], _, _ => 0
  | s, Δ :: _, 0, i => release s Δ i
  | s, Δ :: Δs, k + 1, i => releaseAt (carry s Δ) Δs k i

/-- [proved-derived; formal-checked] The per-deposit releases sum to `LatticeDeposit.released`. -/
theorem released_eq_sum_releaseAt (s : Carried L Ent) (Δs : List (Ent → ℚ)) (i : Ent) :
    released s Δs i = ∑ k ∈ Finset.range Δs.length, releaseAt s Δs k i := by
  induction Δs generalizing s with
  | nil => simp [released]
  | cons Δ Δs ih =>
    rw [List.length_cons, Finset.sum_range_succ', released, ih (carry s Δ)]
    simp only [releaseAt]
    ring

/-- [proved-derived; formal-checked] The releases of a run, summed in absolute value, are bounded by
the weights of the clocks it advanced through (`LatticeDeposit.released_le`'s argument, term by term). -/
theorem abs_releaseAt_sum_le (s : Carried L Ent) (Δs : List (Ent → ℚ)) (i : Ent) (n : ℕ) :
    ∑ k ∈ Finset.range n, |releaseAt s Δs k i| ≤
      unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (run s Δs).clock, gammaWeight m := by
  have hnn : ∀ (t : Carried L Ent) (a : ℕ),
      0 ≤ unit L / 2 * ∑ m ∈ Finset.Ioc t.clock a, gammaWeight m := fun t a =>
    mul_nonneg (by have := unit_pos L; positivity) (Finset.sum_nonneg fun m _ => gammaWeight_nonneg m)
  induction Δs generalizing s n with
  | nil =>
    have h0 : ∀ k, releaseAt s [] k i = 0 := fun k => by cases k <;> rfl
    simp only [h0, abs_zero, Finset.sum_const_zero]
    exact hnn s _
  | cons Δ Δs ih =>
    have hrun : run s (Δ :: Δs) = run (carry s Δ) Δs := rfl
    cases n with
    | zero => simpa using hnn s _
    | succ n =>
      rw [Finset.sum_range_succ', hrun]
      have hs : ∀ k, releaseAt s (Δ :: Δs) (k + 1) i = releaseAt (carry s Δ) Δs k i :=
        fun k => rfl
      have h0 : releaseAt s (Δ :: Δs) 0 i = release s Δ i := rfl
      simp only [hs, h0]
      have hrest := ih (carry s Δ) n
      by_cases hΔ : Δ = 0
      · subst hΔ
        rw [carry_zero] at hrest ⊢
        rw [release_zero, abs_zero, add_zero]
        exact hrest
      · have hclock := carry_clock_of_ne (s := s) hΔ
        have hge := run_clock_ge (carry s Δ) Δs
        rw [hclock] at hrest hge
        have hone := release_bounded s Δ i
        rw [half_fine_unit] at hone
        have hsplit : ∑ m ∈ Finset.Ioc s.clock (run (carry s Δ) Δs).clock, gammaWeight m =
            gammaWeight (s.clock + 1) +
              ∑ m ∈ Finset.Ioc (s.clock + 1) (run (carry s Δ) Δs).clock, gammaWeight m := by
          rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ s.clock) hge, Nat.Ioc_succ_singleton,
            Finset.sum_singleton]
        rw [hsplit, mul_add]
        linarith

/-- [proved-derived; formal-checked] **The releases since the founding sum below half a unit in
absolute value:** `Σ_k |e_k| < u/2` over any run (the Kraft tail of
`LatticeDeposit.gamma_window_lt_one`), the form a Lipschitz propagation consumes. -/
theorem abs_releaseAt_sum_lt (s : Carried L Ent) (Δs : List (Ent → ℚ)) (i : Ent) (n : ℕ) :
    ∑ k ∈ Finset.range n, |releaseAt s Δs k i| < unit L / 2 := by
  have hu : 0 < unit L / 2 := by have := unit_pos L; positivity
  calc ∑ k ∈ Finset.range n, |releaseAt s Δs k i|
      ≤ unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (run s Δs).clock, gammaWeight m :=
        abs_releaseAt_sum_le s Δs i n
    _ < unit L / 2 * 1 := mul_lt_mul_of_pos_left (gamma_window_lt_one _ _) hu
    _ = unit L / 2 := mul_one _

/-- [proved-derived; formal-checked] `abs_releaseAt_sum_lt` read in `ℝ`. -/
theorem abs_releaseAt_sum_lt_real (s : Carried L Ent) (Δs : List (Ent → ℚ)) (i : Ent) (n : ℕ) :
    ∑ k ∈ Finset.range n, |(releaseAt s Δs k i : ℝ)| < ((2 : ℝ) ^ L)⁻¹ / 2 := by
  have h := Rat.cast_lt (K := ℝ) |>.mpr (abs_releaseAt_sum_lt s Δs i n)
  unfold unit at h
  push_cast at h
  exact h

variable {X : Type*} [NormedAddCommGroup X]

/-- [proved-derived; formal-checked] **The `[open]` bound of `LatticeDeposit`, closed for passive
words.** A trajectory of `1`-Lipschitz maps whose residual at step `k` is at most the `k`-th release
of a carried entry stays within `2^(−L)/2` of the unrounded trajectory from the same start, at every
length. -/
theorem carried_trajectory_within_half_unit (F : ℕ → X → X)
    (lip : ∀ i a b, ‖F i a - F i b‖ ≤ ‖a - b‖) (r x y : ℕ → X)
    (hx : ∀ i, x (i + 1) = F i (x i) + r i) (hy : ∀ i, y (i + 1) = F i (y i)) (h0 : x 0 = y 0)
    (s : Carried L Ent) (Δs : List (Ent → ℚ)) (i : Ent)
    (hr : ∀ k, ‖r k‖ ≤ |(releaseAt s Δs k i : ℝ)|) (n : ℕ) :
    ‖x n - y n‖ < ((2 : ℝ) ^ L)⁻¹ / 2 :=
  passive_trajectory_within F lip r x y hx hy h0 n
    ((Finset.sum_le_sum fun k _ => hr k).trans_lt (abs_releaseAt_sum_lt_real s Δs i n))

end Releases

/-! ## 11. Witnesses: a skew element turns, an active element grows -/

section Witness

/-- [definition] The skew element `K = [[0, 1], [−1, 0]]` on the plane. -/
def skewLin : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 ![x.ofLp 1, -x.ofLp 0]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- [definition] The skew element as a continuous linear map. -/
def skew : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap skewLin

/-- [definition] The skew element's action `(a, b) ↦ (b, −a)`. -/
theorem skew_apply (x : EuclideanSpace ℝ (Fin 2)) : skew x = WithLp.toLp 2 ![x.ofLp 1, -x.ofLp 0] :=
  rfl

/-- [proved-standard; formal-checked] The skew element is skew, so passive: `⟪v, K v⟫ = 0`. -/
theorem skew_inner (v : EuclideanSpace ℝ (Fin 2)) : inner ℝ v (skew v) = 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, skew_apply]
  simp
  ring

/-- [definition] The rotation `[[3/5, 4/5], [−4/5, 3/5]]`. -/
def rotation (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![3 / 5 * p.ofLp 0 + 4 / 5 * p.ofLp 1, -(4 / 5) * p.ofLp 0 + 3 / 5 * p.ofLp 1]

/-- [proved-standard; formal-checked] **The skew element's Cayley step at `h = 1` is the rotation
`[[3/5, 4/5], [−4/5, 3/5]]`**, and it keeps the norm (`IsCayleyStep.norm_eq_of_skew`). -/
theorem rotation_isCayleyStep :
    IsCayleyStep 1 skew rotation ∧ ∀ p, ‖rotation p‖ = ‖p‖ := by
  have hC : IsCayleyStep 1 skew rotation := by
    intro p
    ext i
    fin_cases i <;> simp [skew_apply, rotation] <;> ring
  exact ⟨hC, hC.norm_eq_of_skew skew_inner⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-standard; formal-checked] The Cayley step at `h = 1` of the scalar element `k·I`,
`k ≠ 2`, is `((2 + k)/(2 − k))·I`. -/
theorem scalar_isCayleyStep {k : ℝ} (hk : k ≠ 2) :
    IsCayleyStep 1 (k • ContinuousLinearMap.id ℝ E) (fun p => ((2 + k) / (2 - k)) • p) := by
  intro p
  have h2 : (2 : ℝ) - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  rw [← sub_smul, show p + (1 / 2 * k) • p = (1 + 1 / 2 * k) • p by rw [add_smul, one_smul]]
  congr 1
  field_simp

/-- [proved-standard; formal-checked] **The active element `½·I`:** not passive
(`⟪v, ½v⟫ = ½‖v‖² > 0` for `v ≠ 0`), and its Cayley step at `h = 1` is `(5/3)·I`, of gain `5/3 > 1`. -/
theorem active_half_step :
    (∀ v : E, v ≠ 0 → 0 < inner ℝ v (((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E) v)) ∧
      IsCayleyStep 1 ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ E) (fun p => (5 / 3 : ℝ) • p) ∧
      ∀ p : E, ‖(5 / 3 : ℝ) • p‖ = 5 / 3 * ‖p‖ := by
  refine ⟨fun v hv => ?_, ?_, fun p => ?_⟩
  · rw [smul_apply, ContinuousLinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq]
    have := norm_pos_iff.mpr hv
    positivity
  · have h := scalar_isCayleyStep (E := E) (k := 1 / 2) (by norm_num)
    convert h using 3
    norm_num
  · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]

/-- [proved-standard; formal-checked] The word of `n` steps `c·I` is `cⁿ·I`. -/
theorem word_scalar (c : ℝ) (n : ℕ) (v : E) : word (fun _ p => c • p) n v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [word_succ, ih, smul_smul, pow_succ, mul_comm]

/-- [proved-standard; formal-checked] The word of `c·I` steps whose first step is `(c + ε)·I`. -/
theorem word_scalar_first (c ε : ℝ) (n : ℕ) (v : E) :
    word (fun i p => if i = 0 then (c + ε) • p else c • p) (n + 1) v = (c ^ n * (c + ε)) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [word_succ, ih, if_neg (Nat.succ_ne_zero n), smul_smul, pow_succ]
    ring_nf

/-- [proved-derived; formal-checked] **Passivity is load-bearing in the word's bound.** Steps of
gain `5/3` (the Cayley step of `½·I`) whose first step is changed by `ε`: the words of length
`n + 1` differ by `ε (5/3)ⁿ ‖v‖`, the active bound `Σ_i (∏_(j≠i) ρ_j) L_i` attained, against the
`ε‖v‖` a word of contractions allows. -/
theorem active_word_witness (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (v : E) :
    ‖word (fun _ p => (5 / 3 : ℝ) • p) (n + 1) v -
        word (fun i p => if i = 0 then (5 / 3 + ε : ℝ) • p else (5 / 3 : ℝ) • p) (n + 1) v‖ =
      ε * (5 / 3) ^ n * ‖v‖ := by
  rw [word_scalar, word_scalar_first, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have : (5 / 3 : ℝ) ^ (n + 1) - (5 / 3) ^ n * (5 / 3 + ε) = -(ε * (5 / 3) ^ n) := by ring
  rw [this, abs_neg, abs_of_nonneg (by positivity)]

/-- [proved-derived; formal-checked] With `ε > 0`, `v ≠ 0` and `n ≥ 1` the active word's change
exceeds the bound `ε‖v‖` of a word of contractions. -/
theorem active_word_exceeds (ε : ℝ) (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) {v : E} (hv : v ≠ 0) :
    ε * ‖v‖ < ‖word (fun _ p => (5 / 3 : ℝ) • p) (n + 1) v -
        word (fun i p => if i = 0 then (5 / 3 + ε : ℝ) • p else (5 / 3 : ℝ) • p) (n + 1) v‖ := by
  rw [active_word_witness ε hε.le n v]
  have hpow : 1 < (5 / 3 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hvn := norm_pos_iff.mpr hv
  have := mul_lt_mul_of_pos_left hpow hε
  nlinarith

end Witness

end Holonics.HNN.WordSensitivity
