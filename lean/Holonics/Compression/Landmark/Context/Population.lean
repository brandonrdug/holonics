import Holonics.Compression.Landmark.Context.LocalWeighing

/-!
# The egg population: the static mixture with death, and survivor filtering

[definition; agent-inferred] A population is a receiver's mixture over candidate eggs: declared
navigator families, each with its own predictive face and a declared prior (Rust
`receiver::population`; `docs/ELEMENTARY_OBJECTS.md`, "The egg: a generator read as a whole").
`LocalWeighing.static_mixture` states the Bayes mixture of faces for **positive** faces. A
population's families may give a received cell zero (a deterministic family whose surviving keys
emit another class), so this module states the same mixture with **nonnegative** faces:

* `population_mixture` [proved-derived; formal-checked]: while some family with positive prior keeps
  a positive likelihood, every forward total is positive, the mixture's product telescopes to
  `Σ_x π_x A_x(n)`, a family whose face of a cell is zero keeps weight zero from the next cell on
  (death: `HolonicAdjointNormalization.replicator_eq_zero_iff` is its one-step form), and the
  population codes within `−log₂ π_x` of every living family.
* `survivor_code` [proved-derived; formal-checked]: a finite key space of deterministic emitters
  under the uniform prior. The survivors `S_t` are the keys agreeing with every cell before `t`; the
  mixture's face of the received cell is `#S_(t+1)/#S_t`, its product is `#S_n/|K|`, and its code is
  `log₂ |K| − log₂ #S_n`: the key description less the surviving fibre.
* `survivors_product` [proved-derived; formal-checked]: a key space that is a product, emitting the
  pair of its factors' classes, keeps the product of the factors' survivors, so its count is the
  product and its code the sum of the factors' codes (the sheet tuple read per ring; the Rust cell is
  the pair's injective mixed-radix code).

The computational object is the helical pair interaction read as a receiver's population of
candidate eggs; of the winding guide's six general objects this module touches **faces and
placement** (each family's face and the mixture's face); the helix, pair, cell holonomy, tube and
tower thread stay attached through the families' own owners.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Population

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing

/-- A likelihood that reaches zero stays zero. -/
theorem seqLik_eq_zero_of_le {a : ℕ → ℚ} {t n : ℕ} (h : seqLik a t = 0) (htn : t ≤ n) :
    seqLik a n = 0 := by
  induction n, htn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [seqLik_succ, ih, zero_mul]

theorem seqLik_nonneg {a : ℕ → ℚ} (ha : ∀ t, 0 ≤ a t) (n : ℕ) : 0 ≤ seqLik a n :=
  prod_nonneg fun t _ => ha t

section Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The static mixture's forward weight is the prior times the prequential likelihood, whatever
the faces' signs. -/
theorem fwd_id (π : ι → ℚ) (f : ι → ℕ → ℚ) :
    ∀ t x, fwd π f idKernel t x = π x * seqLik (f x) t := by
  intro t
  induction t with
  | zero => intro x; simp [fwd_zero, seqLik_zero]
  | succ n ih =>
    intro x
    simp only [fwd_succ, idKernel, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true,
      ih, seqLik_succ]
    ring

/-- [proved-derived; formal-checked] **`population_mixture`: the static mixture with death.** For a
prior `π` and nonnegative faces `f`, if some family keeps `π_x A_x(n) > 0`:
* every forward total up to `n` is positive (the mixture's face is defined at every cell);
* the mixture's product telescopes, `∏_(t<n) q_t = Σ_x π_x A_x(n)`;
* a family whose face of cell `t` is zero has forward weight zero at every later cell (death);
* the mixture codes within `−log₂ π_x` of every living family:
  `−log₂ ∏ q ≤ −log₂ π_x − log₂ A_x(n)`. -/
theorem population_mixture {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 ≤ f x t) (n : ℕ) (hlive : 0 < ∑ x, π x * seqLik (f x) n) :
    (∀ t ≤ n, 0 < ∑ x, fwd π f idKernel t x) ∧
      ∏ t ∈ range n, fwdMix π f idKernel t = ∑ x, π x * seqLik (f x) n ∧
      (∀ x t, f x t = 0 → ∀ m, t < m → fwd π f idKernel m x = 0) ∧
      ∀ x, 0 < π x → 0 < seqLik (f x) n →
        -Real.logb 2 ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ) ≤
          -Real.logb 2 (π x : ℝ) - Real.logb 2 (seqLik (f x) n : ℝ) := by
  have hfwd := fwd_id π f
  have hnn : ∀ t x, 0 ≤ fwd π f idKernel t x :=
    fwd_nonneg hπ.1 hf idKernel_stochastic.1
  obtain ⟨y, -, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ))
    (g := fun x => π x * seqLik (f x) n) (by simpa using hlive)
  have hπy : 0 < π y := lt_of_le_of_ne (hπ.1 y) fun h => by
    rw [← h, zero_mul] at hy; exact lt_irrefl _ hy
  have hLy : ∀ t ≤ n, 0 < seqLik (f y) t := fun t ht =>
    lt_of_le_of_ne (seqLik_nonneg (hf y) t) fun h => by
      rw [seqLik_eq_zero_of_le h.symm ht, mul_zero] at hy; exact lt_irrefl _ hy
  have htot : ∀ t ≤ n, 0 < ∑ x, fwd π f idKernel t x := fun t ht =>
    lt_of_lt_of_le (by rw [hfwd]; exact mul_pos hπy (hLy t ht))
      (single_le_sum (f := fun x => fwd π f idKernel t x) (fun x _ => hnn t x) (mem_univ y))
  have htel : ∀ m ≤ n, ∏ t ∈ range m, fwdMix π f idKernel t = ∑ x, fwd π f idKernel m x := by
    intro m hm
    induction m with
    | zero => simp [fwd_zero, hπ.2]
    | succ m ih =>
      rw [prod_range_succ, ih (by omega), fwd_sum_succ idKernel_stochastic, fwdMix,
        mul_div_cancel₀ _ (htot m (by omega)).ne']
  have hprod : ∏ t ∈ range n, fwdMix π f idKernel t = ∑ x, π x * seqLik (f x) n := by
    rw [htel n le_rfl]
    exact sum_congr rfl fun x _ => hfwd n x
  refine ⟨htot, hprod, fun x t h0 m htm => ?_, fun x hx hA => ?_⟩
  · have hz : seqLik (f x) (t + 1) = 0 := by rw [seqLik_succ, h0, mul_zero]
    rw [hfwd, seqLik_eq_zero_of_le hz htm, mul_zero]
  · have hle : π x * seqLik (f x) n ≤ ∏ t ∈ range n, fwdMix π f idKernel t := by
      rw [htel n le_rfl, ← hfwd n x]
      exact single_le_sum (f := fun y => fwd π f idKernel n y) (fun y _ => hnn n y) (mem_univ _)
    have hb := neg_logb_le_of_le (a := ((π x * seqLik (f x) n : ℚ) : ℝ))
      (b := ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ)) (by exact_mod_cast mul_pos hx hA)
      (by exact_mod_cast hle)
    push_cast at hb
    rw [Real.logb_mul (by exact_mod_cast hx.ne') (by exact_mod_cast hA.ne')] at hb
    push_cast
    linarith

end Mixture

section Survivors

variable {κ C : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq C]

/-- [definition] **The survivors** at tick `t`: the keys whose emissions agree with every received
cell before `t`. -/
def survivors (e : κ → ℕ → C) (x : ℕ → C) (t : ℕ) : Finset κ :=
  univ.filter fun k => ∀ s < t, e k s = x s

/-- [definition] **A deterministic key's face of the received cell**: one where it emits the cell,
zero elsewhere. -/
def emits (e : κ → ℕ → C) (x : ℕ → C) : κ → ℕ → ℚ :=
  fun k t => if e k t = x t then 1 else 0

/-- [definition] **The uniform prior** over the keys. -/
def uniformPrior : κ → ℚ := fun _ => 1 / (Fintype.card κ : ℚ)

omit [DecidableEq κ] in
theorem uniformPrior_isPrior [Nonempty κ] : IsPrior (uniformPrior (κ := κ)) := by
  refine ⟨fun _ => by unfold uniformPrior; positivity, ?_⟩
  have hc : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformPrior, sum_const, card_univ, nsmul_eq_mul, hc]

omit [DecidableEq κ] in
theorem survivors_succ (e : κ → ℕ → C) (x : ℕ → C) (t : ℕ) :
    survivors e x (t + 1) = (survivors e x t).filter fun k => e k t = x t := by
  ext k
  simp only [survivors, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun s hs => h s (by omega), h t (by omega)⟩
  · rintro ⟨h, ht⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact h s hs
    · exact ht

omit [DecidableEq κ] in
theorem survivors_zero (e : κ → ℕ → C) (x : ℕ → C) : survivors e x 0 = univ := by
  ext k; simp [survivors]

omit [DecidableEq κ] in
theorem survivors_antitone (e : κ → ℕ → C) (x : ℕ → C) {t n : ℕ} (h : t ≤ n) :
    survivors e x n ⊆ survivors e x t := by
  intro k hk
  simp only [survivors, mem_filter, mem_univ, true_and] at hk ⊢
  exact fun s hs => hk s (by omega)

/-- A key's likelihood is one while it survives and zero once it has emitted another class. -/
theorem seqLik_emits (e : κ → ℕ → C) (x : ℕ → C) (k : κ) (t : ℕ) :
    seqLik (emits e x k) t = if k ∈ survivors e x t then 1 else 0 := by
  induction t with
  | zero => simp [seqLik_zero, survivors_zero]
  | succ t ih =>
    rw [seqLik_succ, ih, survivors_succ]
    by_cases hk : k ∈ survivors e x t <;> by_cases he : e k t = x t <;> simp [emits, hk, he]

/-- `Σ_k [k ∈ S] = #S`. -/
theorem sum_indicator (S : Finset κ) : ∑ k, (if k ∈ S then (1 : ℚ) else 0) = S.card := by
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one]

/-- [proved-derived; formal-checked] **`survivor_code`: survivor filtering is uniform Bayes.** Under
the uniform prior, while a key survives to `n`:
* the mixture's face of the received cell at every `t < n` is the surviving fraction
  `#S_(t+1)/#S_t`;
* its product over the passage is `#S_n/|K|`;
* its code is `log₂ |K| − log₂ #S_n`. -/
theorem survivor_code [Nonempty κ] (e : κ → ℕ → C) (x : ℕ → C) (n : ℕ)
    (hS : (survivors e x n).Nonempty) :
    (∀ t < n, fwdMix uniformPrior (emits e x) idKernel t =
        ((survivors e x (t + 1)).card : ℚ) / (survivors e x t).card) ∧
      ∏ t ∈ range n, fwdMix uniformPrior (emits e x) idKernel t =
        ((survivors e x n).card : ℚ) / Fintype.card κ ∧
      -Real.logb 2 ((∏ t ∈ range n, fwdMix uniformPrior (emits e x) idKernel t : ℚ) : ℝ) =
        Real.logb 2 (Fintype.card κ) - Real.logb 2 (survivors e x n).card := by
  have hc : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf : ∀ k t, 0 ≤ emits e x k t := fun k t => by unfold emits; split_ifs <;> norm_num
  have hweight : ∀ t, ∑ k, uniformPrior k * seqLik (emits e x k) t =
      ((survivors e x t).card : ℚ) / Fintype.card κ := by
    intro t
    simp only [seqLik_emits, uniformPrior, mul_ite, mul_one, mul_zero]
    rw [← sum_indicator, sum_div]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  have hcardpos : 0 < ((survivors e x n).card : ℚ) := by exact_mod_cast hS.card_pos
  have hlive : 0 < ∑ k, uniformPrior k * seqLik (emits e x k) n := by
    rw [hweight]; exact div_pos hcardpos (by exact_mod_cast Fintype.card_pos)
  obtain ⟨-, hprod, -, -⟩ := population_mixture uniformPrior_isPrior hf n hlive
  refine ⟨fun t ht => ?_, by rw [hprod, hweight], ?_⟩
  · have hSt : ((survivors e x t).card : ℚ) ≠ 0 := by
      have := (hS.mono (survivors_antitone e x ht.le)).card_pos
      exact_mod_cast this.ne'
    have hnum : ∑ k, fwd uniformPrior (emits e x) idKernel t k * emits e x k t =
        ((survivors e x (t + 1)).card : ℚ) / Fintype.card κ := by
      rw [← hweight (t + 1)]
      refine sum_congr rfl fun k _ => ?_
      rw [fwd_id, seqLik_succ]; ring
    have hden : ∑ k, fwd uniformPrior (emits e x) idKernel t k =
        ((survivors e x t).card : ℚ) / Fintype.card κ := by
      rw [← hweight t]
      exact sum_congr rfl fun k _ => fwd_id _ _ t k
    rw [fwdMix, hnum, hden]
    field_simp
  · rw [hprod, hweight]
    have hcard : (0 : ℝ) < (survivors e x n).card := by exact_mod_cast hS.card_pos
    have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    push_cast
    rw [Real.logb_div hcard.ne' hK.ne']
    ring

/-- [proved-derived; formal-checked] **`survivors_product`: a product key space keeps the product
of its factors' survivors.** Keys `(k₁, k₂)` emitting the pair of their factors' classes survive
exactly when each factor's key survives on its component of the cells, so the count is the product
and the code is the sum of the factors' codes. -/
theorem survivors_product {κ₁ κ₂ C₁ C₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁]
    [DecidableEq κ₂] [DecidableEq C₁] [DecidableEq C₂] [Nonempty κ₁] [Nonempty κ₂]
    (e₁ : κ₁ → ℕ → C₁) (e₂ : κ₂ → ℕ → C₂) (x₁ : ℕ → C₁) (x₂ : ℕ → C₂) (t : ℕ) :
    survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t =
        survivors e₁ x₁ t ×ˢ survivors e₂ x₂ t ∧
      (survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t).card =
        (survivors e₁ x₁ t).card * (survivors e₂ x₂ t).card ∧
      ((survivors e₁ x₁ t).Nonempty → (survivors e₂ x₂ t).Nonempty →
        Real.logb 2 (Fintype.card (κ₁ × κ₂)) -
            Real.logb 2 (survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s))
              (fun s => (x₁ s, x₂ s)) t).card =
          (Real.logb 2 (Fintype.card κ₁) - Real.logb 2 (survivors e₁ x₁ t).card) +
            (Real.logb 2 (Fintype.card κ₂) - Real.logb 2 (survivors e₂ x₂ t).card)) := by
  have hset : survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t =
      survivors e₁ x₁ t ×ˢ survivors e₂ x₂ t := by
    ext ⟨k₁, k₂⟩
    simp only [survivors, mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]
    exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
      fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩
  have hcard := congrArg card hset
  rw [card_product] at hcard
  refine ⟨hset, hcard, fun h₁ h₂ => ?_⟩
  have p₁ : (0 : ℝ) < (survivors e₁ x₁ t).card := by exact_mod_cast h₁.card_pos
  have p₂ : (0 : ℝ) < (survivors e₂ x₂ t).card := by exact_mod_cast h₂.card_pos
  have q₁ : (0 : ℝ) < Fintype.card κ₁ := by exact_mod_cast Fintype.card_pos
  have q₂ : (0 : ℝ) < Fintype.card κ₂ := by exact_mod_cast Fintype.card_pos
  rw [hcard, Fintype.card_prod]
  push_cast
  rw [Real.logb_mul q₁.ne' q₂.ne', Real.logb_mul p₁.ne' p₂.ne']
  ring

end Survivors

section Audit

#print axioms seqLik_eq_zero_of_le
#print axioms seqLik_nonneg
#print axioms fwd_id
#print axioms population_mixture
#print axioms uniformPrior_isPrior
#print axioms survivors_succ
#print axioms survivors_zero
#print axioms survivors_antitone
#print axioms seqLik_emits
#print axioms sum_indicator
#print axioms survivor_code
#print axioms survivors_product

end Audit

end Holonics.Compression.Landmark.Context.Population
