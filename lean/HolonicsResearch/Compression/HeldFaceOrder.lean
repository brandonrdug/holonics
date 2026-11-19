import Mathlib

/-!
# A held face's gain is the same in every reading order, and a release that holds its faces lies in their fibres

[proved-standard] The source is #410's box "The held face's reading order" (record
`research/records/2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md`,
§3 and §6; atlas `radix.held-face-reading-order`, `arith.near-miss-kept-face-fibre`), part done in #519 by
`Mathematics/CheapConvolution` (the face of a word read leading first is the fold `x ↦ b x + d`). This file supplies
the two clauses that file left: the fibre of the kept faces, and the chain rule.

The model. A finite space `Ω` carries a mass `μ ≥ 0` (any finite measure: nothing asks it to sum to one). A variable
is a function `X : Ω → α` into a type with decidable equality; `mass μ X x` is the mass of `X = x`, the entropy is
`H(X) = Σ_x −P(x) log P(x)` over the values `X` takes (`Real.negMulLog`), and the conditional entropy
`H(X | Y) = Σ_y P(y) Σ_x −(P(x, y)/P(y)) log (P(x, y)/P(y))` is the mean entropy of the conditioned laws. A word is
`n` places `d : Fin n → Ω → β`; a reading order is a permutation `σ` of the places, `σ k` the place read `k`-th; the
places read before step `k` are the masked word `readBefore d σ k` (place `i` shown when `σ⁻¹ i < k`).

What is proved.

1. **The kept faces' fibre** (`release_mem_fibres`, `release_mem_fibres_of_conserved`): a release `r` that holds the
   faces `q ∈ Q` of `T(x, y)` lies in `⋂_(q∈Q) Fib_q`, `Fib_q = {r | q r = q (T x y)}`, and conversely; where each
   face is conserved, `q (T x y) = T_q (q x) (q y)`, a release whose faces read `T_q (q x) (q y)` lies there. With
   faces whose moduli's least common multiple exceeds a window's width, the fibre within the window is the one value
   (`Mathematics/CheckLoop.check_loop_decides`).
2. **The chain rule** (`entropy_pair`): `H(X, Y) = H(Y) + H(X | Y)`.
3. **A recoding keeps the entropy** (`entropy_comp`, `entropy_congr`): a variable determined by another and
   determining it has its entropy; so conditioning on a function of what is held changes nothing
   (`condEntropy_pair_comp`): a face of the reader's own release, computed from what it has written, gains nothing.
4. **Every reading order pays the same code** (`condEntropy_word_eq_sum`): for held faces `F` and every order `σ`,
   `H(W | F) = Σ_k H(d_σ(k) | d_σ(<k), F)`, where `W` is the word (`condEntropy_eq_sum_any_order` for a variable `W`
   whose places are `d`, through an injective chart of its places).
5. **A held face gains the same in every order** (`gain_any_order`): with `I(W; q | F) = H(W | F) − H(W | F, q)`,
   `Σ_k (H(d_σ(k) | d_σ(<k), F) − H(d_σ(k) | d_σ(<k), F, q)) = I(W; q | F)` for every `σ`. The order decides at which
   places the gain is paid, never its total.

Limits. Entropies are in nats (`Real.log`); the record's bits are these over `log 2`. The space is finite and the
mass is given; no measure-theoretic entropy (Mathlib's `ProbabilityTheory`) is joined here. The record's tables
(the per-place costs leading first and units first) are readings of its receipts and are not checked here. That
`H(W | F)` is the code of the result given what is held is the source-coding reading, not proved here.

The computational object is the helical pair interaction: each kept face is a ring's residue of the release, read
by its fold, and the release is the joint face of all of them; the chain rule says that the pairing of the word's
places with what the reader holds sums to the same flux in every order of the passage. Of the winding guide's six
general objects this touches the faces and placement (which face is held, at which place its gain is paid) and the
helix (the reading order of the places); the pair, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `radix.held-face-reading-order` and `arith.near-miss-kept-face-fibre`; the record's §6.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.HeldFaceOrder

open Finset Real

/-! ## 1. The kept faces' fibre -/

section Fibre

variable {α ι : Type*} {R : ι → Type*}

/-- [definition] The fibre of a face `q` through the value `v`: the releases with `v`'s face. -/
def Fib {ρ : Type*} (q : α → ρ) (v : α) : Set α := {r | q r = q v}

/-- [proved-standard; formal-checked] **A release that holds the faces lies in their fibres**: a release `r` whose
faces `q_i`, `i ∈ Q`, read those of `T(x, y)` lies in `⋂_(i∈Q) Fib_(q_i)`, and only such a release does. -/
theorem release_mem_fibres (q : (i : ι) → α → R i) (Q : Set ι) (T : α → α → α) (x y r : α) :
    r ∈ ⋂ i ∈ Q, Fib (q i) (T x y) ↔ ∀ i ∈ Q, q i r = q i (T x y) := by
  simp [Fib]

/-- [proved-standard; formal-checked] **The consumer equation places the release in the fibres**: where each face is
conserved, `q_i (T x y) = T_i (q_i x) (q_i y)`, a release whose faces read `T_i (q_i x) (q_i y)` lies in
`⋂_(i∈Q) Fib_(q_i)`. -/
theorem release_mem_fibres_of_conserved (q : (i : ι) → α → R i) (Q : Set ι) (T : α → α → α)
    (Tq : (i : ι) → R i → R i → R i) (hcons : ∀ i ∈ Q, ∀ a b, q i (T a b) = Tq i (q i a) (q i b))
    {x y r : α} (hr : ∀ i ∈ Q, q i r = Tq i (q i x) (q i y)) : r ∈ ⋂ i ∈ Q, Fib (q i) (T x y) := by
  rw [release_mem_fibres]
  intro i hi
  rw [hr i hi, hcons i hi]

end Fibre

/-! ## 2. Entropy on a finite space -/

section Entropy

variable {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ)
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- [definition] The mass of the event `X = x`. -/
def mass (X : Ω → α) (x : α) : ℝ := ∑ ω ∈ univ.filter (fun ω => X ω = x), μ ω

/-- [definition] The entropy `H(X) = Σ_x −P(x) log P(x)`, over the values `X` takes. -/
noncomputable def entropy (X : Ω → α) : ℝ := ∑ x ∈ univ.image X, negMulLog (mass μ X x)

/-- [definition] Two variables read together. -/
def pair (X : Ω → α) (Y : Ω → β) : Ω → α × β := fun ω => (X ω, Y ω)

/-- [definition] The conditional entropy `H(X | Y) = Σ_y P(y) H(X | Y = y)`. -/
noncomputable def condEntropy (X : Ω → α) (Y : Ω → β) : ℝ :=
  ∑ y ∈ univ.image Y, mass μ Y y * ∑ x ∈ univ.image X, negMulLog (mass μ (pair X Y) (x, y) / mass μ Y y)

variable {μ}

/-- [proved-standard; formal-checked] A mass is nonnegative. -/
theorem mass_nonneg (hμ : ∀ ω, 0 ≤ μ ω) (X : Ω → α) (x : α) : 0 ≤ mass μ X x :=
  sum_nonneg fun ω _ => hμ ω

/-- [proved-standard; formal-checked] A value `X` does not take has no mass. -/
theorem mass_eq_zero_of_not_mem {X : Ω → α} {x : α} (hx : x ∉ univ.image X) : mass μ X x = 0 := by
  refine sum_eq_zero fun ω hω => ?_
  exact absurd (mem_image.mpr ⟨ω, mem_univ _, (mem_filter.mp hω).2⟩) hx

/-- [proved-standard; formal-checked] The entropy may be summed over any set of values holding those `X` takes. -/
theorem entropy_eq_sum_of_subset {X : Ω → α} {s : Finset α} (hs : univ.image X ⊆ s) :
    entropy μ X = ∑ x ∈ s, negMulLog (mass μ X x) := by
  refine sum_subset hs fun x _ hx => ?_
  rw [mass_eq_zero_of_not_mem hx, negMulLog_zero]

/-- [proved-standard; formal-checked] **The marginal**: summing the joint mass over the values of `X` gives the
mass of `Y`. -/
theorem sum_mass_pair (X : Ω → α) (Y : Ω → β) (y : β) :
    ∑ x ∈ univ.image X, mass μ (pair X Y) (x, y) = mass μ Y y := by
  unfold mass
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun ω => Y ω = y)) (t := univ.image X) (g := X)
    (fun ω _ => mem_image.mpr ⟨ω, mem_univ _, rfl⟩)]
  refine sum_congr rfl fun x _ => ?_
  rw [filter_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [mem_filter, mem_univ, true_and, pair, Prod.mk.injEq]
  tauto

/-- [proved-standard; formal-checked] The joint entropy as a double sum over the two variables' values. -/
theorem entropy_pair_eq_sum (X : Ω → α) (Y : Ω → β) :
    entropy μ (pair X Y) =
      ∑ y ∈ univ.image Y, ∑ x ∈ univ.image X, negMulLog (mass μ (pair X Y) (x, y)) := by
  have hs : univ.image (pair X Y) ⊆ univ.image X ×ˢ univ.image Y := by
    intro p hp
    obtain ⟨ω, -, rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨mem_image_of_mem _ (mem_univ _), mem_image_of_mem _ (mem_univ _)⟩
  rw [entropy_eq_sum_of_subset hs, sum_product, sum_comm]

/-- [proved-standard; formal-checked] **The chain rule**: `H(X, Y) = H(Y) + H(X | Y)`. -/
theorem entropy_pair (hμ : ∀ ω, 0 ≤ μ ω) (X : Ω → α) (Y : Ω → β) :
    entropy μ (pair X Y) = entropy μ Y + condEntropy μ X Y := by
  rw [entropy_pair_eq_sum, entropy, condEntropy, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  set b := mass μ Y y with hb
  rcases (mass_nonneg hμ Y y).lt_or_eq with hpos | hzero
  · rw [← hb] at hpos
    have hsum := sum_mass_pair (μ := μ) X Y y
    have key : ∀ x, negMulLog (mass μ (pair X Y) (x, y)) =
        b * negMulLog (mass μ (pair X Y) (x, y) / b) + mass μ (pair X Y) (x, y) / b * negMulLog b := by
      intro x
      rw [← negMulLog_mul, div_mul_cancel₀ _ hpos.ne']
    simp_rw [key]
    rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← sum_div, hsum, div_self hpos.ne', one_mul, add_comm]
  · rw [← hb] at hzero
    rw [← hzero, negMulLog_zero, zero_mul, zero_add]
    refine sum_eq_zero fun x hx => ?_
    have hle : mass μ (pair X Y) (x, y) ≤ b := by
      rw [hb, ← sum_mass_pair (μ := μ) X Y y]
      exact single_le_sum (f := fun x => mass μ (pair X Y) (x, y)) (fun _ _ => mass_nonneg hμ _ _) hx
    have h0 : mass μ (pair X Y) (x, y) = 0 := le_antisymm (hle.trans hzero.symm.le) (mass_nonneg hμ _ _)
    rw [h0, negMulLog_zero]

/-- [proved-standard; formal-checked] The conditional entropy is the entropy the second variable leaves:
`H(X | Y) = H(X, Y) − H(Y)`. -/
theorem condEntropy_eq_sub (hμ : ∀ ω, 0 ≤ μ ω) (X : Ω → α) (Y : Ω → β) :
    condEntropy μ X Y = entropy μ (pair X Y) - entropy μ Y := by
  rw [entropy_pair hμ]; ring

/-- [proved-standard; formal-checked] **A recoding keeps the entropy**: if `f` separates whatever `X` separates,
`H(f ∘ X) = H(X)`. -/
theorem entropy_comp {X : Ω → α} (f : α → β) (hf : ∀ ω ω', f (X ω) = f (X ω') → X ω = X ω') :
    entropy μ (f ∘ X) = entropy μ X := by
  unfold entropy
  rw [← image_image, sum_image]
  · refine sum_congr rfl fun x hx => ?_
    obtain ⟨ω₀, -, rfl⟩ := mem_image.mp hx
    unfold mass
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext ω
    simp only [mem_filter, mem_univ, true_and, Function.comp]
    exact ⟨hf ω ω₀, fun h => by rw [h]⟩
  · intro x hx x' hx' hxx'
    obtain ⟨ω, -, rfl⟩ := mem_image.mp hx
    obtain ⟨ω', -, rfl⟩ := mem_image.mp hx'
    exact hf ω ω' hxx'

/-- [proved-standard; formal-checked] Two variables each a function of the other have one entropy. -/
theorem entropy_congr {X : Ω → α} {Z : Ω → β} (f : α → β) (g : β → α) (hZ : ∀ ω, Z ω = f (X ω))
    (hX : ∀ ω, X ω = g (Z ω)) : entropy μ Z = entropy μ X := by
  have hZf : Z = f ∘ X := funext hZ
  rw [hZf]
  exact entropy_comp f fun ω ω' h => by rw [hX ω, hX ω', hZ ω, hZ ω', h]

/-- [proved-standard; formal-checked] **A function of what is held gains nothing**: `H(X | Y, φ(Y)) = H(X | Y)`. -/
theorem condEntropy_pair_comp (hμ : ∀ ω, 0 ≤ μ ω) (X : Ω → α) (Y : Ω → β) (φ : β → γ) :
    condEntropy μ X (pair Y (φ ∘ Y)) = condEntropy μ X Y := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  have h1 : entropy μ (pair X (pair Y (φ ∘ Y))) = entropy μ (pair X Y) :=
    entropy_congr (fun p => (p.1, (p.2, φ p.2))) (fun p => (p.1, p.2.1)) (fun _ => rfl) (fun _ => rfl)
  have h2 : entropy μ (pair Y (φ ∘ Y)) = entropy μ Y :=
    entropy_congr (fun b => (b, φ b)) (fun p => p.1) (fun _ => rfl) (fun _ => rfl)
  rw [h1, h2]

end Entropy

/-! ## 3. Every reading order pays the same code -/

section Order

variable {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
variable {β γ : Type*} [DecidableEq β] [DecidableEq γ] {n : ℕ}

/-- [definition] The places read before step `k` in the order `σ` (`σ k` is the place read `k`-th): place `i` is
shown when `σ⁻¹ i < k`, hidden otherwise. -/
def readBefore (d : Fin n → Ω → β) (σ : Equiv.Perm (Fin n)) (k : ℕ) (ω : Ω) : Fin n → Option β :=
  fun i => if (σ.symm i : ℕ) < k then some (d i ω) else none

/-- [definition] The word: all its places at once. -/
def word (d : Fin n → Ω → β) (ω : Ω) : Fin n → β := fun i => d i ω

omit [Fintype Ω] [DecidableEq β] in
/-- [proved-standard; formal-checked] One more step shows one more place. -/
theorem readBefore_succ (d : Fin n → Ω → β) (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) (ω : Ω) :
    readBefore d σ (k + 1) ω = Function.update (readBefore d σ k ω) (σ ⟨k, hk⟩) (some (d (σ ⟨k, hk⟩) ω)) := by
  funext i
  by_cases hi : i = σ ⟨k, hk⟩
  · subst hi
    simp [readBefore]
  · rw [Function.update_of_ne hi]
    have hne : (σ.symm i : ℕ) ≠ k := by
      intro h
      apply hi
      rw [← Equiv.apply_symm_apply σ i]
      congr 1
      exact Fin.ext h
    simp only [readBefore]
    by_cases hlt : (σ.symm i : ℕ) < k
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- [proved-standard; formal-checked] One step of the chain: showing the place `σ k` adds its conditional
entropy given what was read before it and the held faces. -/
theorem entropy_readBefore_succ (hμ : ∀ ω, 0 ≤ μ ω) (d : Fin n → Ω → β) (σ : Equiv.Perm (Fin n)) (F : Ω → γ)
    {k : ℕ} (hk : k < n) :
    entropy μ (pair (readBefore d σ (k + 1)) F) =
      entropy μ (pair (readBefore d σ k) F) +
        condEntropy μ (d (σ ⟨k, hk⟩)) (pair (readBefore d σ k) F) := by
  rw [← entropy_pair hμ]
  set p := σ ⟨k, hk⟩
  have hfun : pair (readBefore d σ (k + 1)) F =
      (fun t : β × ((Fin n → Option β) × γ) => (Function.update t.2.1 p (some t.1), t.2.2)) ∘
        pair (d p) (pair (readBefore d σ k) F) := by
    funext ω
    simp only [pair, Function.comp, readBefore_succ d σ hk ω]
    rfl
  rw [hfun]
  refine entropy_comp _ fun ω ω' h => ?_
  simp only [pair, Prod.mk.injEq] at h ⊢
  obtain ⟨hu, hF⟩ := h
  have hp : readBefore d σ k ω p = none := by simp [readBefore, p]
  have hp' : readBefore d σ k ω' p = none := by simp [readBefore, p]
  refine ⟨?_, ?_, hF⟩
  · have := congrFun hu p
    simpa using this
  · funext i
    by_cases hi : i = p
    · rw [hi, hp, hp']
    · have := congrFun hu i
      rwa [Function.update_of_ne hi, Function.update_of_ne hi] at this

/-- [proved-standard; formal-checked] **Every reading order pays the same code**: for held faces `F` and every order
`σ`, `H(W | F) = Σ_k H(d_σ(k) | d_σ(<k), F)`. -/
theorem condEntropy_word_eq_sum (hμ : ∀ ω, 0 ≤ μ ω) (d : Fin n → Ω → β) (F : Ω → γ) (σ : Equiv.Perm (Fin n)) :
    ∑ k : Fin n, condEntropy μ (d (σ k)) (pair (readBefore d σ k) F) = condEntropy μ (word d) F := by
  let g : ℕ → ℝ := fun k => if h : k < n then condEntropy μ (d (σ ⟨k, h⟩)) (pair (readBefore d σ k) F) else 0
  have hg : ∑ k : Fin n, condEntropy μ (d (σ k)) (pair (readBefore d σ k) F) = ∑ k ∈ range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    simp [g, k.isLt]
  have tele : ∀ k ≤ n, ∑ j ∈ range k, g j =
      entropy μ (pair (readBefore d σ k) F) - entropy μ (pair (readBefore d σ 0) F) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih (by omega), entropy_readBefore_succ hμ d σ F (by omega : k < n)]
      simp only [g, dif_pos (by omega : k < n)]
      ring
  rw [hg, tele n le_rfl, condEntropy_eq_sub hμ]
  have h0 : entropy μ (pair (readBefore d σ 0) F) = entropy μ F :=
    entropy_congr (fun x => ((fun _ => none : Fin n → Option β), x)) (fun t => t.2)
      (fun ω => by
        simp only [pair, Prod.mk.injEq, and_true]
        funext i
        unfold readBefore
        simp) (fun _ => rfl)
  have hn : entropy μ (pair (readBefore d σ n) F) = entropy μ (pair (word d) F) := by
    have hfun : pair (readBefore d σ n) F =
        (fun t : (Fin n → β) × γ => ((fun i => some (t.1 i) : Fin n → Option β), t.2)) ∘ pair (word d) F := by
      funext ω
      simp only [pair, word, Function.comp, Prod.mk.injEq, and_true]
      funext i
      unfold readBefore
      rw [if_pos (σ.symm i).isLt]
    rw [hfun]
    refine entropy_comp _ fun ω ω' h => ?_
    simp only [pair, Prod.mk.injEq] at h ⊢
    refine ⟨funext fun i => ?_, h.2⟩
    simpa using congrFun h.1 i
  rw [h0, hn]

/-- [proved-standard; formal-checked] **The code of a variable is read in any order of its places**: if a variable
`W` is charted injectively by its places `d i = (enc ∘ W) · i`, then `H(W | F) = Σ_k H(d_σ(k) | d_σ(<k), F)` for every
order `σ`. -/
theorem condEntropy_eq_sum_any_order {α : Type*} [DecidableEq α] (hμ : ∀ ω, 0 ≤ μ ω) (W : Ω → α)
    (enc : α → Fin n → β) (henc : Function.Injective enc) (F : Ω → γ) (σ : Equiv.Perm (Fin n)) :
    ∑ k : Fin n, condEntropy μ (fun ω => enc (W ω) (σ k))
        (pair (readBefore (fun i ω => enc (W ω) i) σ k) F) = condEntropy μ W F := by
  rw [condEntropy_word_eq_sum hμ (fun i ω => enc (W ω) i) F σ, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  congr 1
  refine entropy_comp (X := pair W F) (fun t => (enc t.1, t.2)) fun ω ω' h => ?_
  simp only [pair, Prod.mk.injEq] at h ⊢
  exact ⟨henc h.1, h.2⟩

/-- [definition] The gain of a held face `q` given the faces `F`: `I(W; q | F) = H(W | F) − H(W | F, q)`. -/
noncomputable def gain {α δ : Type*} [DecidableEq α] [DecidableEq δ] (μ : Ω → ℝ) (W : Ω → α) (F : Ω → γ)
    (q : Ω → δ) : ℝ :=
  condEntropy μ W F - condEntropy μ W (pair F q)

/-- [proved-standard; formal-checked] **A held face gains the same in every order**: for every order `σ`, the gains
the face `q` pays place by place sum to `I(W; q | F)`; the order decides only at which places it is paid. -/
theorem gain_any_order {δ : Type*} [DecidableEq δ] (hμ : ∀ ω, 0 ≤ μ ω) (d : Fin n → Ω → β) (F : Ω → γ)
    (q : Ω → δ) (σ : Equiv.Perm (Fin n)) :
    ∑ k : Fin n, (condEntropy μ (d (σ k)) (pair (readBefore d σ k) F) -
        condEntropy μ (d (σ k)) (pair (readBefore d σ k) (pair F q))) = gain μ (word d) F q := by
  rw [sum_sub_distrib, condEntropy_word_eq_sum hμ, condEntropy_word_eq_sum hμ, gain]

end Order

end Holonics.Compression.HeldFaceOrder
