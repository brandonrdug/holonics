import Holonics.Compression.Landmark.Context.Population

/-!
# The egg population's dormancy: keys filtered only where their layers sound, switches priced by the fixed share

[definition; agent-inferred] Campaign 3 at the population (rebuild step 4, #73; Rust
`receiver::population::dormancy`). A key family's emitters read through layers (a moiré's rings).
A layer is active or dormant: a dormant layer is silent while its ring's clock keeps winding, so
its key is retained through the aeon it sleeps in, not filtered. The hidden state is the key and
the activity; the key is kept, the activity moves by a stochastic kernel (per layer the fixed share
`LocalWeighing.shareKernel`, layers independent: `productKernel`), and a state's face of a cell is
one where its key emits the cell at its activity and zero elsewhere. `Population.survivor_code` is
the case of one activity.

* `forward_dominance_nonneg` [proved-derived; formal-checked]: the forward mixture with nonnegative
  faces (a deterministic emitter's) telescopes and dominates every state sequence whose prior, faces
  and kernel steps are positive: `LocalWeighing.forward_dominance` without positive faces.
* `dormant_survivor_code` [proved-derived; formal-checked]: **the dormancy-aware survivor code.**
  Over `n + 1` cells, for every activity path `σ`, the keys `S_σ(n + 1)` that emit every cell at
  `σ`'s activity survive, and the mixture codes within
  `log₂ |K| − log₂ #S_σ(n + 1) − log₂ π(σ_0) − Σ_(t<n) log₂ T(σ_t, σ_(t+1))`: the path pays its `n`
  transitions between received cells, and the step after the last cell sums out.
* `layer_survivors` [proved-derived; formal-checked]: **keys are filtered only where the layer
  sounds.** For one layer whose dormancy emits a declared silent class, when `σ`'s dormant ticks
  read the silent class, `S_σ(n)` is exactly the keys agreeing with the cells at `σ`'s active ticks.
* `productKernel_stochastic`, `productKernel_path` [proved-derived; formal-checked]: independent
  layers' kernel is stochastic, and a path's kernel product is the product of its layers'.
* `share_path_code`, `stay_code_le`, `share_path_code_le` [proved-derived; formal-checked]: **the
  switching prior's code.** A layer's fixed-share path code is `k (−log₂ α) + (n − k)(−log₂(1 − α))`
  for `k` switches; at `α = 2^(−j)`, `j ≥ 1`, a stay costs less than `3·2^(−j)` bits, so the path costs
  at most `k j + 3 (n − k)/2^j`, and at most `k j + 3` bits over `n ≤ 2^j` cells: each switch pays
  the `log₂` of its positions.
* `exec_total_le`, `exec_path_le`, `forward_executed_nonneg` [proved-derived; formal-checked]:
  **the executed forward mixture with nonnegative faces.** Weights rounded down after each kernel
  step by at most `ρ_t`, and faces scored from class sums rounded down by at most `μ_t`, code within
  `Σ_t −log₂(ρ_t μ_t)` of every state sequence. The rounded totals telescope
  (`(∏ μ) Σ W_n ≤ (Σ W_0) ∏ q`) and a path keeps its weight up to `∏ ρ`; no face need be positive.
  This is `LocalWeighing.forward_executed` for nonnegative faces, with the rounding on the weight
  after the kernel (the share step's rebase) rather than on the face before it.
* `dormant_survivor_executed`, `dormant_executed_code` [proved-derived; formal-checked]: **the
  executed filter codes within the certified drift.** With the opening at scale `c`, every rounding
  a factor in `(1 − 2^(−j), 1]` and `r` of them counted, the executed code is within
  `dormant_survivor_code`'s bound plus `3 r 2^(−j)` bits; at `j = 62` this is Rust
  `Dormancy::drift`. [agent-inferred] That the Rust's counted roundings bound the factors: each
  `Weight::sum` and `Weight::of` rounds down once by a factor in `(1 − 2^(−62), 1]`; a state's weight
  after the kernel passes `L` share roundings and the opening `#active` products, a class sum one
  rounding per added weight and per chunk join, and the counter `roundings` adds all of them, more
  than any one face or weight needs.

The computational object is the helical pair interaction read as a receiver's population of eggs
through aeons; of the winding guide's six general objects this module touches the **helix** (the key
is kept while the activity moves: a ring's clock keeps winding through its silence), the **tube**
(a run of cells at one activity, an aeon's span) and **faces and placement** (each state's face and
the mixture's face); the pair, cell holonomy and tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Dormancy

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing
open Holonics.Compression.Landmark.Context.Population

/-! ## 1. The forward mixture with nonnegative faces -/

section Forward

variable {ι : Type*} [Fintype ι]

/-- A path's weight is at most its end state's forward weight, with nonnegative faces. -/
theorem fwd_path_le {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : ∀ x, 0 ≤ F0 x)
    (hf : ∀ x t, 0 ≤ f x t) (hT : ∀ y x, 0 ≤ T y x) (σ : ℕ → ι) :
    ∀ n, F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) ≤ fwd F0 f T n (σ n) := by
  have hnn := fwd_nonneg hF hf hT
  intro n
  induction n with
  | zero => simp [fwd_zero]
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, fwd_succ]
    have hm : 0 ≤ f (σ n) n * T (σ n) (σ (n + 1)) := mul_nonneg (hf _ _) (hT _ _)
    calc (F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
          (f (σ n) n * T (σ n) (σ (n + 1)))
        ≤ fwd F0 f T n (σ n) * (f (σ n) n * T (σ n) (σ (n + 1))) :=
          mul_le_mul_of_nonneg_right ih hm
      _ = fwd F0 f T n (σ n) * f (σ n) n * T (σ n) (σ (n + 1)) := by ring
      _ ≤ ∑ y, fwd F0 f T n y * f y n * T y (σ (n + 1)) :=
          single_le_sum (f := fun y => fwd F0 f T n y * f y n * T y (σ (n + 1)))
            (fun y _ => mul_nonneg (mul_nonneg (hnn n y) (hf y n)) (hT _ _)) (mem_univ _)

/-- A positive product of nonnegative factors has positive prefixes. -/
theorem prefix_pos {a : ℚ} {g : ℕ → ℚ} (ha : 0 ≤ a) (hg : ∀ t, 0 ≤ g t) {n : ℕ}
    (h : 0 < a * ∏ t ∈ range n, g t) {m : ℕ} (hm : m ≤ n) : 0 < a * ∏ t ∈ range m, g t := by
  have hsplit := prod_range_mul_prod_Ico g hm
  have hnn : 0 ≤ a * ∏ t ∈ range m, g t := mul_nonneg ha (prod_nonneg fun t _ => hg t)
  refine lt_of_le_of_ne hnn fun h0 => ?_
  rw [← hsplit, ← mul_assoc, ← h0, zero_mul] at h
  exact lt_irrefl _ h

/-- [proved-derived; formal-checked] **`forward_dominance_nonneg`: the forward mixture with
nonnegative faces.** For a prior, nonnegative faces and a stochastic kernel, if a state sequence `σ`
has a positive weight `F₀(σ_0) ∏_(t<n) f_(σ_t)(t) T(σ_t, σ_(t+1))`, then every total up to `n` is
positive, the mixture's product telescopes to the total forward weight, and it dominates that
sequence's weight. -/
theorem forward_dominance_nonneg {F0 : ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} (hF : IsPrior F0)
    (hf : ∀ x t, 0 ≤ f x t) (hT : Stochastic T) (σ : ℕ → ι) (n : ℕ)
    (hpath : 0 < F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) :
    (∀ t ≤ n, 0 < ∑ x, fwd F0 f T t x) ∧
      ∏ t ∈ range n, fwdMix F0 f T t = ∑ x, fwd F0 f T n x ∧
      F0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))) ≤
        ∏ t ∈ range n, fwdMix F0 f T t := by
  have hnn := fwd_nonneg hF.1 hf hT.1
  have hdom := fwd_path_le hF.1 hf hT.1 σ
  have htot : ∀ t ≤ n, 0 < ∑ x, fwd F0 f T t x := fun t ht =>
    lt_of_lt_of_le ((prefix_pos (hF.1 _) (fun s => mul_nonneg (hf _ _) (hT.1 _ _)) hpath ht).trans_le
      (hdom t)) (single_le_sum (f := fun x => fwd F0 f T t x) (fun x _ => hnn t x) (mem_univ _))
  have htel : ∀ m ≤ n, ∏ t ∈ range m, fwdMix F0 f T t = ∑ x, fwd F0 f T m x := by
    intro m hm
    induction m with
    | zero => simp [fwd_zero, hF.2]
    | succ m ih =>
      rw [prod_range_succ, ih (by omega), fwd_sum_succ hT, fwdMix,
        mul_div_cancel₀ _ (htot m (by omega)).ne']
  refine ⟨htot, htel n le_rfl, ?_⟩
  rw [htel n le_rfl]
  exact (hdom n).trans
    (single_le_sum (f := fun x => fwd F0 f T n x) (fun x _ => hnn n x) (mem_univ _))

end Forward

/-! ## 2. The dormancy-aware survivor code -/

section Survivors

variable {κ A C : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype A] [DecidableEq A]
  [DecidableEq C]

/-- [definition] **The prior over (key, activity)**: uniform over the keys, `π` over the
activities. -/
def keyPrior (π : A → ℚ) : κ × A → ℚ := fun s => uniformPrior s.1 * π s.2

/-- [definition] **The kernel over (key, activity)**: the key is kept, the activity moves by `T`. -/
def keyKernel (T : A → A → ℚ) : κ × A → κ × A → ℚ :=
  fun s s' => if s.1 = s'.1 then T s.2 s'.2 else 0

/-- [definition] **A state's face of the received cell**: one where its key at its activity emits
the cell, zero elsewhere. -/
def activeEmits (e : κ → A → ℕ → C) (x : ℕ → C) : κ × A → ℕ → ℚ :=
  fun s t => if e s.1 s.2 t = x t then 1 else 0

/-- [definition] **The survivors along an activity path**: the keys that emit every received cell
before `n` at the path's activity. -/
def pathSurvivors (e : κ → A → ℕ → C) (x : ℕ → C) (σ : ℕ → A) (n : ℕ) : Finset κ :=
  univ.filter fun k => ∀ t < n, e k (σ t) t = x t

omit [DecidableEq κ] [DecidableEq A] in
theorem keyPrior_isPrior {π : A → ℚ} (hπ : IsPrior π) : IsPrior (keyPrior (κ := κ) π) := by
  refine ⟨fun s => mul_nonneg ((uniformPrior_isPrior (κ := κ)).1 s.1) (hπ.1 s.2), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [keyPrior, ← mul_sum, hπ.2, mul_one]
  exact (uniformPrior_isPrior (κ := κ)).2

omit [Nonempty κ] [DecidableEq A] in
theorem keyKernel_stochastic {T : A → A → ℚ} (hT : Stochastic T) :
    Stochastic (keyKernel (κ := κ) T) := by
  refine ⟨fun s s' => ?_, fun s => ?_⟩
  · unfold keyKernel; split_ifs
    · exact hT.1 _ _
    · exact le_refl _
  · rw [Fintype.sum_prod_type]
    simp only [keyKernel]
    rw [sum_eq_single s.1 (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp [hT.2 s.2]

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`dormant_survivor_code`: the dormancy-aware survivor code.**
Under the uniform key prior, an activity prior `π` and an activity kernel `T`, over `n + 1` received
cells and so `n` transitions (the kernel step after the last cell sums out: its row is stochastic),
for every activity path `σ` whose survivors `S_σ(n + 1)` are nonempty and whose prior and kernel
steps are positive, the mixture over (key, activity) dominates
`#S_σ(n + 1)/|K| · π(σ_0) ∏_(t<n) T(σ_t, σ_(t+1))`, so it codes within
`log₂ |K| − log₂ #S_σ(n + 1) − log₂ π(σ_0) − Σ_(t<n) log₂ T(σ_t, σ_(t+1))`: the key description less
the fibre that survives along the path, plus the path's own code over its transitions between
received cells (Rust `Dormancy`'s bound over a passage of `n + 1` cells, `n` transitions). -/
theorem dormant_survivor_code {π : A → ℚ} {T : A → A → ℚ} (hπ : IsPrior π) (hT : Stochastic T)
    (e : κ → A → ℕ → C) (x : ℕ → C) (σ : ℕ → A) (n : ℕ)
    (hS : (pathSurvivors e x σ (n + 1)).Nonempty)
    (h0 : 0 < π (σ 0)) (hTσ : ∀ t < n, 0 < T (σ t) (σ (t + 1))) :
    ((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
        (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) ≤
      ∏ t ∈ range (n + 1), fwdMix (keyPrior π) (activeEmits e x) (keyKernel T) t ∧
      -Real.logb 2 ((∏ t ∈ range (n + 1), fwdMix (keyPrior π) (activeEmits e x) (keyKernel T) t :
          ℚ) : ℝ) ≤
        Real.logb 2 (Fintype.card κ) - Real.logb 2 ((pathSurvivors e x σ (n + 1)).card) -
          Real.logb 2 (π (σ 0) : ℝ) - ∑ t ∈ range n, Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ) := by
  have hP := keyPrior_isPrior (κ := κ) hπ
  have hK := keyKernel_stochastic (κ := κ) hT
  have hf : ∀ s t, 0 ≤ activeEmits e x s t := fun s t => by
    unfold activeEmits; split_ifs <;> norm_num
  have hcard : (0 : ℚ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  -- a surviving key emits every cell up to the last along the path: its transitions' weight
  have hpath : ∀ k ∈ pathSurvivors e x σ (n + 1),
      keyPrior π (k, σ 0) * ∏ t ∈ range n, (activeEmits e x (k, σ t) t *
        keyKernel T (k, σ t) (k, σ (t + 1))) =
        1 / Fintype.card κ * (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) := by
    intro k hk
    have hk' := (mem_filter.mp hk).2
    rw [prod_congr rfl fun t ht => show activeEmits e x (k, σ t) t *
        keyKernel T (k, σ t) (k, σ (t + 1)) = T (σ t) (σ (t + 1)) by
      simp [activeEmits, keyKernel, hk' t (by have := mem_range.mp ht; omega)]]
    simp only [keyPrior, uniformPrior]
    ring
  -- and its face of the last cell is one
  have hlast : ∀ k ∈ pathSurvivors e x σ (n + 1), activeEmits e x (k, σ n) n = 1 := by
    intro k hk
    simp [activeEmits, (mem_filter.mp hk).2 n (by omega)]
  obtain ⟨k₀, hk₀⟩ := hS
  have hTpos : 0 < ∏ t ∈ range n, T (σ t) (σ (t + 1)) :=
    prod_pos fun t ht => hTσ t (mem_range.mp ht)
  have hpos : 0 < keyPrior π (k₀, σ 0) * ∏ t ∈ range n, (activeEmits e x (k₀, σ t) t *
      keyKernel T (k₀, σ t) (k₀, σ (t + 1))) := by
    rw [hpath k₀ hk₀]; exact mul_pos (by positivity) (mul_pos h0 hTpos)
  obtain ⟨htot, htel, -⟩ := forward_dominance_nonneg hP hf hK (fun t => (k₀, σ t)) n hpos
  have hnn := fwd_nonneg hP.1 hf hK.1
  -- the product over `n + 1` cells is the forward weight read at the last cell, before its step
  have htel' : ∏ t ∈ range (n + 1), fwdMix (keyPrior π) (activeEmits e x) (keyKernel T) t =
      ∑ s, fwd (keyPrior π) (activeEmits e x) (keyKernel T) n s * activeEmits e x s n := by
    rw [prod_range_succ, htel, fwdMix, mul_div_cancel₀ _ (htot n le_rfl).ne']
  have hsum : ((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
      (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) ≤
      ∏ t ∈ range (n + 1), fwdMix (keyPrior π) (activeEmits e x) (keyKernel T) t := by
    rw [htel', Fintype.sum_prod_type]
    calc ((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
          (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1)))
        = ∑ k ∈ pathSurvivors e x σ (n + 1),
            1 / Fintype.card κ * (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ k ∈ pathSurvivors e x σ (n + 1),
            fwd (keyPrior π) (activeEmits e x) (keyKernel T) n (k, σ n) *
              activeEmits e x (k, σ n) n := sum_le_sum fun k hk => by
          rw [← hpath k hk, hlast k hk, mul_one]
          exact fwd_path_le hP.1 hf hK.1 (fun t => (k, σ t)) n
      _ ≤ ∑ k, fwd (keyPrior π) (activeEmits e x) (keyKernel T) n (k, σ n) *
            activeEmits e x (k, σ n) n :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ =>
            mul_nonneg (hnn n _) (hf _ _)
      _ ≤ ∑ k, ∑ a, fwd (keyPrior π) (activeEmits e x) (keyKernel T) n (k, a) *
            activeEmits e x (k, a) n :=
          sum_le_sum fun k _ => single_le_sum (f := fun a => fwd (keyPrior π) (activeEmits e x)
            (keyKernel T) n (k, a) * activeEmits e x (k, a) n)
            (fun a _ => mul_nonneg (hnn n _) (hf _ _)) (mem_univ _)
  refine ⟨hsum, ?_⟩
  have hSpos : (0 : ℚ) < (pathSurvivors e x σ (n + 1)).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨k₀, hk₀⟩
  have hlow : 0 < ((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
      (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) :=
    mul_pos (div_pos hSpos hcard) (mul_pos h0 hTpos)
  have hR := neg_logb_le_of_le (by exact_mod_cast hlow) (show
    ((((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
        (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) : ℚ) : ℝ) ≤
      ((∏ t ∈ range (n + 1), fwdMix (keyPrior π) (activeEmits e x) (keyKernel T) t : ℚ) : ℝ) by
    exact_mod_cast hsum)
  have hSr : (0 : ℝ) < (pathSurvivors e x σ (n + 1)).card := by exact_mod_cast hSpos
  have hKr : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hcard
  have h0r : (0 : ℝ) < (π (σ 0) : ℝ) := by exact_mod_cast h0
  have hTr : ∀ t ∈ range n, ((T (σ t) (σ (t + 1)) : ℚ) : ℝ) ≠ 0 := fun t ht =>
    (by exact_mod_cast (hTσ t (mem_range.mp ht)).ne' : ((T (σ t) (σ (t + 1)) : ℚ) : ℝ) ≠ 0)
  push_cast at hR
  rw [Real.logb_mul (by positivity) (mul_pos h0r (prod_pos fun t ht => by
      exact_mod_cast hTσ t (mem_range.mp ht))).ne', Real.logb_div hSr.ne' hKr.ne',
    Real.logb_mul h0r.ne' (prod_ne_zero_iff.mpr hTr), Real.logb_prod _ _ hTr] at hR
  push_cast
  linarith

/-- [definition] **One layer's emission**: its key's class when active, the declared silent class
when dormant (a dormant ring's sheet reads `0` while its clock keeps winding). -/
def layerEmit (emit : κ → ℕ → C) (silent : C) : κ → Bool → ℕ → C :=
  fun k a t => if a then emit k t else silent

omit [DecidableEq κ] [Nonempty κ] [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`layer_survivors`: keys are filtered only where the layer
sounds.** When the path's dormant ticks read the silent class, the survivors along it are exactly
the keys agreeing with the cells at its active ticks. -/
theorem layer_survivors (emit : κ → ℕ → C) (silent : C) (x : ℕ → C) (σ : ℕ → Bool) (n : ℕ)
    (hsilent : ∀ t < n, σ t = false → x t = silent) :
    pathSurvivors (layerEmit emit silent) x σ n =
      univ.filter fun k => ∀ t < n, σ t = true → emit k t = x t := by
  ext k
  rw [pathSurvivors, Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h t ht hσ
    have := h t ht
    simpa [layerEmit, hσ] using this
  · intro h t ht
    cases hσ : σ t
    · simp [layerEmit, (hsilent t ht hσ).symm]
    · simpa [layerEmit] using h t ht hσ

end Survivors

/-! ## 3. Independent layers and the switching prior's code -/

section Layers

variable {A₁ A₂ : Type*} [Fintype A₁] [Fintype A₂]

/-- [definition] **Independent layers' kernel**: each layer moves by its own kernel. -/
def productKernel (T₁ : A₁ → A₁ → ℚ) (T₂ : A₂ → A₂ → ℚ) : A₁ × A₂ → A₁ × A₂ → ℚ :=
  fun a b => T₁ a.1 b.1 * T₂ a.2 b.2

/-- [proved-derived; formal-checked] Independent layers' kernel is stochastic. -/
theorem productKernel_stochastic {T₁ : A₁ → A₁ → ℚ} {T₂ : A₂ → A₂ → ℚ} (h₁ : Stochastic T₁)
    (h₂ : Stochastic T₂) : Stochastic (productKernel T₁ T₂) := by
  refine ⟨fun a b => mul_nonneg (h₁.1 _ _) (h₂.1 _ _), fun a => ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [productKernel, ← mul_sum, h₂.2, mul_one, h₁.2]

omit [Fintype A₁] [Fintype A₂] in
/-- [proved-derived; formal-checked] **A path's kernel product is its layers'.** -/
theorem productKernel_path (T₁ : A₁ → A₁ → ℚ) (T₂ : A₂ → A₂ → ℚ) (σ : ℕ → A₁ × A₂) (n : ℕ) :
    ∏ t ∈ range n, productKernel T₁ T₂ (σ t) (σ (t + 1)) =
      (∏ t ∈ range n, T₁ (σ t).1 (σ (t + 1)).1) * ∏ t ∈ range n, T₂ (σ t).2 (σ (t + 1)).2 := by
  simp only [productKernel, prod_mul_distrib]

end Layers

/-- [proved-derived; formal-checked] **`share_path_code`: a layer's fixed-share path code.** For
`α ∈ (0, 1)` and a path with `k` switches over `n` steps,
`−Σ_t log₂ T_α(σ_t, σ_(t+1)) = k (−log₂ α) + (n − k)(−log₂(1 − α))`. -/
theorem share_path_code {α : ℚ} (hα0 : 0 < α) (hα1 : α < 1) (σ : ℕ → Bool) (n : ℕ) :
    -∑ t ∈ range n, Real.logb 2 (shareKernel α (σ t) (σ (t + 1)) : ℝ) =
      switches σ n * -Real.logb 2 (α : ℝ) + stays σ n * -Real.logb 2 ((1 - α : ℚ) : ℝ) := by
  have hpos : ∀ t ∈ range n, ((shareKernel α (σ t) (σ (t + 1)) : ℚ) : ℝ) ≠ 0 := fun t _ => by
    have : 0 < shareKernel α (σ t) (σ (t + 1)) := by
      unfold shareKernel; split_ifs <;> linarith
    exact_mod_cast this.ne'
  rw [← Real.logb_prod _ _ hpos]
  have e : ∏ t ∈ range n, ((shareKernel α (σ t) (σ (t + 1)) : ℚ) : ℝ) =
      ((1 - α : ℚ) : ℝ) ^ stays σ n * (α : ℝ) ^ switches σ n := by
    rw [← Rat.cast_prod, share_prod]; push_cast; ring
  have h1 : (0 : ℝ) < ((1 - α : ℚ) : ℝ) := by exact_mod_cast sub_pos.mpr hα1
  have h0 : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα0
  rw [e, Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
  ring

/-- [proved-derived; formal-checked] **`stay_code_le`: a stay at `α = 2^(−j)` costs less than
`3·2^(−j)` bits** (`j ≥ 1`): `−log(1 − x) ≤ x/(1 − x) ≤ 2x` for `x ≤ ½`, and `log 2 > 2/3`. -/
theorem stay_code_le {j : ℕ} (hj : 1 ≤ j) :
    -Real.logb 2 ((1 - (1 / 2 : ℚ) ^ j : ℚ) : ℝ) ≤ 3 * (1 / 2 : ℝ) ^ j := by
  set x : ℝ := (1 / 2 : ℝ) ^ j with hx
  have hx0 : 0 < x := by positivity
  have hxh : x ≤ 1 / 2 := by
    rw [hx]; calc (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      _ = 1 / 2 := by norm_num
  have hcast : ((1 - (1 / 2 : ℚ) ^ j : ℚ) : ℝ) = 1 - x := by push_cast; rfl
  rw [hcast]
  have h1x : 0 < 1 - x := by linarith
  have hlog : -Real.log (1 - x) ≤ 2 * x := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
    rw [Real.log_inv] at this
    have hinv : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
    rw [hinv] at this
    have : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ h1x]; nlinarith
    linarith
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hl2pos : 0 < Real.log 2 := by linarith
  rw [Real.logb, show -(Real.log (1 - x) / Real.log 2) = -Real.log (1 - x) / Real.log 2 by ring,
    div_le_iff₀ hl2pos]
  nlinarith

/-- [proved-derived; formal-checked] **`share_path_code_le`: each switch pays the `log₂` of its
positions.** At `α = 2^(−j)`, `j ≥ 1`, a layer's path with `k` switches over `n` steps costs at most
`k j + 3 (n − k)/2^j` bits, and at most `k j + 3` bits when `n ≤ 2^j`. -/
theorem share_path_code_le {j : ℕ} (hj : 1 ≤ j) (σ : ℕ → Bool) (n : ℕ) :
    -∑ t ∈ range n, Real.logb 2 (shareKernel ((1 / 2 : ℚ) ^ j) (σ t) (σ (t + 1)) : ℝ) ≤
        switches σ n * j + stays σ n * (3 * (1 / 2 : ℝ) ^ j) ∧
      (n ≤ 2 ^ j →
        -∑ t ∈ range n, Real.logb 2 (shareKernel ((1 / 2 : ℚ) ^ j) (σ t) (σ (t + 1)) : ℝ) ≤
          switches σ n * j + 3) := by
  have hα0 : (0 : ℚ) < (1 / 2) ^ j := by positivity
  have hα1 : ((1 / 2 : ℚ) ^ j) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hcode := share_path_code hα0 hα1 σ n
  have hswitch : -Real.logb 2 (((1 / 2 : ℚ) ^ j : ℚ) : ℝ) = j := by
    push_cast
    rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    ring
  have hstay := stay_code_le hj
  have hstays_nn : (0 : ℝ) ≤ stays σ n := Nat.cast_nonneg _
  have hmain : -∑ t ∈ range n, Real.logb 2 (shareKernel ((1 / 2 : ℚ) ^ j) (σ t) (σ (t + 1)) : ℝ) ≤
      switches σ n * j + stays σ n * (3 * (1 / 2 : ℝ) ^ j) := by
    rw [hcode, hswitch]
    have := mul_le_mul_of_nonneg_left hstay hstays_nn
    linarith
  refine ⟨hmain, fun hn => ?_⟩
  have hst : (stays σ n : ℝ) ≤ 2 ^ j := by
    have h1 : stays σ n ≤ n := by
      have := stays_add_switches σ n; omega
    exact_mod_cast h1.trans hn
  have : (stays σ n : ℝ) * (3 * (1 / 2 : ℝ) ^ j) ≤ 3 := by
    have h2 : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
    have h3 : (0 : ℝ) ≤ (1 / 2) ^ j := by positivity
    nlinarith
  linarith

/-! ## 4. The executed filter: weights rounded after the kernel, faces from rounded sums -/

section Executed

variable {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] **`exec_total_le`: the rounded totals telescope.** Carried
weights `W_t ≥ 0` rounded down after each kernel step (`W_(t+1)(x) ≤ Σ_y W_t(y) f_y(t) T(y, x)`)
and scored faces `q_t ≥ 0` read from sums rounded down by at most `μ_t`
(`μ_t Σ_x W_t(x) f_x(t) ≤ q_t Σ_x W_t(x)`) give `(∏_(t<n) μ_t) Σ W_n ≤ (Σ W_0) ∏_(t<n) q_t`: the
mass a face loses to rounding is at most what its normalization returns. -/
theorem exec_total_le {W : ℕ → ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} {q μ : ℕ → ℚ}
    (hT : Stochastic T) (hdown : ∀ t x, W (t + 1) x ≤ ∑ y, W t y * f y t * T y x)
    (hq : ∀ t, μ t * ∑ x, W t x * f x t ≤ q t * ∑ x, W t x)
    (hμ : ∀ t, 0 ≤ μ t) (hq0 : ∀ t, 0 ≤ q t) :
    ∀ n, (∏ t ∈ range n, μ t) * ∑ x, W n x ≤ (∑ x, W 0 x) * ∏ t ∈ range n, q t := by
  have hZ : ∀ t, ∑ x, W (t + 1) x ≤ ∑ y, W t y * f y t := by
    intro t
    calc ∑ x, W (t + 1) x ≤ ∑ x, ∑ y, W t y * f y t * T y x := sum_le_sum fun x _ => hdown t x
      _ = ∑ y, W t y * f y t := by
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← mul_sum, hT.2 y, mul_one]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, prod_range_succ]
    have hμn : 0 ≤ ∏ t ∈ range n, μ t := prod_nonneg fun t _ => hμ t
    calc (∏ t ∈ range n, μ t) * μ n * ∑ x, W (n + 1) x
        ≤ (∏ t ∈ range n, μ t) * μ n * ∑ y, W n y * f y n :=
          mul_le_mul_of_nonneg_left (hZ n) (mul_nonneg hμn (hμ n))
      _ ≤ (∏ t ∈ range n, μ t) * (q n * ∑ x, W n x) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hq n) hμn
      _ = (∏ t ∈ range n, μ t) * (∑ x, W n x) * q n := by ring
      _ ≤ (∑ x, W 0 x) * (∏ t ∈ range n, q t) * q n :=
          mul_le_mul_of_nonneg_right ih (hq0 n)
      _ = (∑ x, W 0 x) * ((∏ t ∈ range n, q t) * q n) := by ring

/-- [proved-derived; formal-checked] **`exec_path_le`: a path keeps its weight up to the roundings.**
With weights rounded down after each kernel step by at most `ρ_t`
(`ρ_t Σ_y W_t(y) f_y(t) T(y, x) ≤ W_(t+1)(x)`), nonnegative faces and kernel, every state sequence
keeps `(∏_(t<n) ρ_t) W_0(σ_0) ∏_(t<n) f_(σ_t)(t) T(σ_t, σ_(t+1)) ≤ W_n(σ_n)`. -/
theorem exec_path_le {W : ℕ → ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ} {ρ : ℕ → ℚ}
    (hW : ∀ t x, 0 ≤ W t x) (hf : ∀ x t, 0 ≤ f x t) (hT : ∀ y x, 0 ≤ T y x)
    (hup : ∀ t x, ρ t * ∑ y, W t y * f y t * T y x ≤ W (t + 1) x) (hρ : ∀ t, 0 ≤ ρ t)
    (σ : ℕ → ι) :
    ∀ n, (∏ t ∈ range n, ρ t) *
        (W 0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) ≤ W n (σ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : 0 ≤ f (σ n) n * T (σ n) (σ (n + 1)) := mul_nonneg (hf _ _) (hT _ _)
    calc (∏ t ∈ range (n + 1), ρ t) *
          (W 0 (σ 0) * ∏ t ∈ range (n + 1), (f (σ t) t * T (σ t) (σ (t + 1))))
        = ρ n * ((∏ t ∈ range n, ρ t) *
            (W 0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) *
              (f (σ n) n * T (σ n) (σ (n + 1)))) := by
          rw [prod_range_succ, prod_range_succ]; ring
      _ ≤ ρ n * (W n (σ n) * (f (σ n) n * T (σ n) (σ (n + 1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ih hm) (hρ n)
      _ ≤ ρ n * ∑ y, W n y * f y n * T y (σ (n + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hρ n)
          rw [← mul_assoc]
          exact single_le_sum (f := fun y => W n y * f y n * T y (σ (n + 1)))
            (fun y _ => mul_nonneg (mul_nonneg (hW n y) (hf y n)) (hT _ _)) (mem_univ _)
      _ ≤ W (n + 1) (σ (n + 1)) := hup n _

/-- [proved-derived; formal-checked] **`forward_executed_nonneg`: the executed forward mixture with
nonnegative faces.** Weights opened at most `1` in total, rounded down after each kernel step by at
most `ρ_t`, and faces scored from sums rounded down by at most `μ_t` code within the roundings of
every state sequence: `(∏_(t<n) ρ_t μ_t) W_0(σ_0) ∏_(t<n) f_(σ_t)(t) T(σ_t, σ_(t+1)) ≤ ∏_(t<n) q_t`.
No face need be positive: a deterministic emitter's zeros pass, and the rounding sits after the
kernel, on the weight, where `LocalWeighing.forward_executed` charts the face before it. -/
theorem forward_executed_nonneg {W : ℕ → ι → ℚ} {f : ι → ℕ → ℚ} {T : ι → ι → ℚ}
    {q ρ μ : ℕ → ℚ} (hW : ∀ t x, 0 ≤ W t x) (hf : ∀ x t, 0 ≤ f x t) (hT : Stochastic T)
    (hdown : ∀ t x, W (t + 1) x ≤ ∑ y, W t y * f y t * T y x)
    (hup : ∀ t x, ρ t * ∑ y, W t y * f y t * T y x ≤ W (t + 1) x)
    (hq : ∀ t, μ t * ∑ x, W t x * f x t ≤ q t * ∑ x, W t x)
    (hρ : ∀ t, 0 ≤ ρ t) (hμ : ∀ t, 0 ≤ μ t) (hq0 : ∀ t, 0 ≤ q t) (hZ : ∑ x, W 0 x ≤ 1)
    (σ : ℕ → ι) (n : ℕ) :
    (∏ t ∈ range n, (ρ t * μ t)) *
        (W 0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1)))) ≤
      ∏ t ∈ range n, q t := by
  have htot := exec_total_le hT hdown hq hμ hq0 n
  have hpath := exec_path_le hW hf hT.1 hup hρ σ n
  have hμn : 0 ≤ ∏ t ∈ range n, μ t := prod_nonneg fun t _ => hμ t
  have hqn : 0 ≤ ∏ t ∈ range n, q t := prod_nonneg fun t _ => hq0 t
  rw [prod_mul_distrib]
  calc (∏ t ∈ range n, ρ t) * (∏ t ∈ range n, μ t) *
        (W 0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))))
      = (∏ t ∈ range n, μ t) * ((∏ t ∈ range n, ρ t) *
          (W 0 (σ 0) * ∏ t ∈ range n, (f (σ t) t * T (σ t) (σ (t + 1))))) := by ring
    _ ≤ (∏ t ∈ range n, μ t) * W n (σ n) := mul_le_mul_of_nonneg_left hpath hμn
    _ ≤ (∏ t ∈ range n, μ t) * ∑ x, W n x :=
        mul_le_mul_of_nonneg_left (single_le_sum (f := W n) (fun x _ => hW n x) (mem_univ _)) hμn
    _ ≤ (∑ x, W 0 x) * ∏ t ∈ range n, q t := htot
    _ ≤ 1 * ∏ t ∈ range n, q t := mul_le_mul_of_nonneg_right hZ hqn
    _ = ∏ t ∈ range n, q t := one_mul _

end Executed

section ExecutedSurvivors

variable {κ A C : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype A] [DecidableEq A]
  [DecidableEq C]

omit [Nonempty κ] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`dormant_survivor_executed`: the executed filter keeps the
survivor bound up to its roundings.** The weights over (key, activity) opened at scale `c > 0`
(`ρ₀ c π(k, a) ≤ W_0(k, a)`, `Σ W_0 ≤ c`), rounded down after each kernel step by at most `ρ_t`,
and the faces read from class sums rounded down by at most `μ_t`, over `n + 1` cells and `n`
transitions: `ρ₀ (∏_(t<n) ρ_t)(∏_(t≤n) μ_t) · #S_σ(n + 1)/|K| · π(σ_0) ∏_(t<n) T(σ_t, σ_(t+1)) ≤
∏_(t≤n) q_t`, `dormant_survivor_code`'s product times the roundings (Rust `Dormancy`: the opening
`2^(−jL)(2^j − 1)^(#active)` per key, so `c = |K|`). -/
theorem dormant_survivor_executed {π : A → ℚ} {T : A → A → ℚ} (hT : Stochastic T)
    (e : κ → A → ℕ → C) (x : ℕ → C) (σ : ℕ → A) (n : ℕ)
    {W : ℕ → κ × A → ℚ} {q ρ μ : ℕ → ℚ} {ρ₀ c : ℚ} (hW : ∀ t s, 0 ≤ W t s)
    (hdown : ∀ t s', W (t + 1) s' ≤ ∑ s, W t s * activeEmits e x s t * keyKernel T s s')
    (hup : ∀ t s', ρ t * ∑ s, W t s * activeEmits e x s t * keyKernel T s s' ≤ W (t + 1) s')
    (hq : ∀ t, μ t * ∑ s, W t s * activeEmits e x s t ≤ q t * ∑ s, W t s)
    (hρ : ∀ t, 0 ≤ ρ t) (hμ : ∀ t, 0 ≤ μ t) (hq0 : ∀ t, 0 ≤ q t)
    (hopen : ∀ s, ρ₀ * (c * keyPrior π s) ≤ W 0 s) (hc : 0 < c)
    (hZ : ∑ s, W 0 s ≤ c) :
    ρ₀ * (∏ t ∈ range n, ρ t) * (∏ t ∈ range (n + 1), μ t) *
        (((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
          (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1)))) ≤
      ∏ t ∈ range (n + 1), q t := by
  have hK := keyKernel_stochastic (κ := κ) hT
  have hf : ∀ s t, 0 ≤ activeEmits e x s t := fun s t => by
    unfold activeEmits; split_ifs <;> norm_num
  have htot := exec_total_le hK hdown hq hμ hq0 n
  have hρn : 0 ≤ ∏ t ∈ range n, ρ t := prod_nonneg fun t _ => hρ t
  have hμn : 0 ≤ ∏ t ∈ range n, μ t := prod_nonneg fun t _ => hμ t
  have hqn : 0 ≤ ∏ t ∈ range n, q t := prod_nonneg fun t _ => hq0 t
  set P : ℚ := π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1)) with hP
  -- each survivor keeps its path's weight, up to the roundings, at the last cell's activity
  have hkeep : ∀ k ∈ pathSurvivors e x σ (n + 1),
      ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P)) ≤
        W n (k, σ n) * activeEmits e x (k, σ n) n := by
    intro k hk
    have hk' := (mem_filter.mp hk).2
    have hpath := exec_path_le hW hf hK.1 hup hρ (fun t => (k, σ t)) n
    rw [prod_congr rfl fun t ht => show activeEmits e x (k, σ t) t *
        keyKernel T (k, σ t) (k, σ (t + 1)) = T (σ t) (σ (t + 1)) by
      simp [activeEmits, keyKernel, hk' t (by have := mem_range.mp ht; omega)]] at hpath
    have hlast : activeEmits e x (k, σ n) n = 1 := by
      simp [activeEmits, hk' n (by omega)]
    have h0 := hopen (k, σ 0)
    simp only [keyPrior, uniformPrior] at h0
    rw [hlast, mul_one]
    calc ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P))
        = (∏ t ∈ range n, ρ t) * (ρ₀ * (c * (1 / Fintype.card κ * π (σ 0))) *
            ∏ t ∈ range n, T (σ t) (σ (t + 1))) := by rw [hP]; ring
      _ ≤ (∏ t ∈ range n, ρ t) * (W 0 (k, σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h0
            (prod_nonneg fun t _ => hT.1 _ _)) hρn
      _ ≤ W n (k, σ n) := hpath
  -- the survivors' weights are part of the last cell's emitting mass
  have hsum : ((pathSurvivors e x σ (n + 1)).card : ℚ) *
      (ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P))) ≤
      ∑ s, W n s * activeEmits e x s n := by
    rw [Fintype.sum_prod_type]
    calc ((pathSurvivors e x σ (n + 1)).card : ℚ) *
          (ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P)))
        = ∑ k ∈ pathSurvivors e x σ (n + 1),
            ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ pathSurvivors e x σ (n + 1), W n (k, σ n) * activeEmits e x (k, σ n) n :=
          sum_le_sum hkeep
      _ ≤ ∑ k, W n (k, σ n) * activeEmits e x (k, σ n) n :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ =>
            mul_nonneg (hW n _) (hf _ _)
      _ ≤ ∑ k, ∑ a, W n (k, a) * activeEmits e x (k, a) n :=
          sum_le_sum fun k _ => single_le_sum (f := fun a => W n (k, a) * activeEmits e x (k, a) n)
            (fun a _ => mul_nonneg (hW n _) (hf _ _)) (mem_univ _)
  have hmain : c * (ρ₀ * (∏ t ∈ range n, ρ t) * (∏ t ∈ range (n + 1), μ t) *
      (((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ * P)) ≤
      c * ∏ t ∈ range (n + 1), q t := by
    calc c * (ρ₀ * (∏ t ∈ range n, ρ t) * (∏ t ∈ range (n + 1), μ t) *
          (((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ * P))
        = (∏ t ∈ range n, μ t) * (μ n * (((pathSurvivors e x σ (n + 1)).card : ℚ) *
            (ρ₀ * (∏ t ∈ range n, ρ t) * (c * (1 / Fintype.card κ * P))))) := by
          rw [prod_range_succ]; ring
      _ ≤ (∏ t ∈ range n, μ t) * (μ n * ∑ s, W n s * activeEmits e x s n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (hμ n)) hμn
      _ ≤ (∏ t ∈ range n, μ t) * (q n * ∑ s, W n s) :=
          mul_le_mul_of_nonneg_left (hq n) hμn
      _ = q n * ((∏ t ∈ range n, μ t) * ∑ s, W n s) := by ring
      _ ≤ q n * ((∑ s, W 0 s) * ∏ t ∈ range n, q t) := mul_le_mul_of_nonneg_left htot (hq0 n)
      _ ≤ q n * (c * ∏ t ∈ range n, q t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ hqn) (hq0 n)
      _ = c * ∏ t ∈ range (n + 1), q t := by rw [prod_range_succ]; ring
  exact le_of_mul_le_mul_left hmain hc

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`dormant_executed_code`: the executed code is within the
certified drift of the ideal bound.** When the roundings' factors multiply to at least
`(1 − 2^(−j))^r` (each rounding a factor in `(1 − 2^(−j), 1]`, `r` of them counted, `j ≥ 1`), the
executed filter codes within `dormant_survivor_code`'s bound plus `3 r 2^(−j)` bits:
`−log₂ ∏_(t≤n) q_t ≤ log₂ |K| − log₂ #S_σ(n + 1) − log₂ π(σ_0) − Σ_(t<n) log₂ T(σ_t, σ_(t+1))
+ 3 r 2^(−j)`. At `j = 62` this is Rust `Dormancy::drift`, `3 · r · 2^(−62)`. -/
theorem dormant_executed_code {π : A → ℚ} {T : A → A → ℚ} (hT : Stochastic T)
    (e : κ → A → ℕ → C) (x : ℕ → C) (σ : ℕ → A) (n : ℕ)
    {W : ℕ → κ × A → ℚ} {q ρ μ : ℕ → ℚ} {ρ₀ c : ℚ} (hW : ∀ t s, 0 ≤ W t s)
    (hdown : ∀ t s', W (t + 1) s' ≤ ∑ s, W t s * activeEmits e x s t * keyKernel T s s')
    (hup : ∀ t s', ρ t * ∑ s, W t s * activeEmits e x s t * keyKernel T s s' ≤ W (t + 1) s')
    (hq : ∀ t, μ t * ∑ s, W t s * activeEmits e x s t ≤ q t * ∑ s, W t s)
    (hρ : ∀ t, 0 ≤ ρ t) (hμ : ∀ t, 0 ≤ μ t) (hq0 : ∀ t, 0 ≤ q t)
    (hopen : ∀ s, ρ₀ * (c * keyPrior π s) ≤ W 0 s) (hc : 0 < c)
    (hZ : ∑ s, W 0 s ≤ c) {j r : ℕ} (hj : 1 ≤ j)
    (hround : (1 - (1 / 2 : ℚ) ^ j) ^ r ≤
      ρ₀ * (∏ t ∈ range n, ρ t) * ∏ t ∈ range (n + 1), μ t)
    (hS : (pathSurvivors e x σ (n + 1)).Nonempty)
    (h0 : 0 < π (σ 0)) (hTσ : ∀ t < n, 0 < T (σ t) (σ (t + 1))) :
    -Real.logb 2 ((∏ t ∈ range (n + 1), q t : ℚ) : ℝ) ≤
      Real.logb 2 (Fintype.card κ) - Real.logb 2 ((pathSurvivors e x σ (n + 1)).card) -
        Real.logb 2 (π (σ 0) : ℝ) - ∑ t ∈ range n, Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ) +
          r * (3 * (1 / 2 : ℝ) ^ j) := by
  have hprod := dormant_survivor_executed hT e x σ n hW hdown hup hq hρ hμ hq0 hopen hc hZ
  set Λ : ℚ := ρ₀ * (∏ t ∈ range n, ρ t) * ∏ t ∈ range (n + 1), μ t with hΛ
  set X : ℚ := ((pathSurvivors e x σ (n + 1)).card : ℚ) / Fintype.card κ *
    (π (σ 0) * ∏ t ∈ range n, T (σ t) (σ (t + 1))) with hX
  have hε : (0 : ℚ) < 1 - (1 / 2 : ℚ) ^ j := by
    have : ((1 / 2 : ℚ) ^ j) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le (pow_pos hε r) hround
  have hcard : (0 : ℚ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hSpos : (0 : ℚ) < (pathSurvivors e x σ (n + 1)).card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hTpos : 0 < ∏ t ∈ range n, T (σ t) (σ (t + 1)) :=
    prod_pos fun t ht => hTσ t (mem_range.mp ht)
  have hXpos : 0 < X := mul_pos (div_pos hSpos hcard) (mul_pos h0 hTpos)
  have hR := neg_logb_le_of_le (by exact_mod_cast mul_pos hΛpos hXpos)
    (show ((Λ * X : ℚ) : ℝ) ≤ ((∏ t ∈ range (n + 1), q t : ℚ) : ℝ) by exact_mod_cast hprod)
  have hΛr : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛpos
  have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
  rw [Rat.cast_mul, Real.logb_mul hΛr.ne' hXr.ne'] at hR
  -- the roundings: `−log₂ Λ ≤ r (−log₂ (1 − 2^(−j))) ≤ 3 r 2^(−j)`
  have hεr : (0 : ℝ) < ((1 - (1 / 2 : ℚ) ^ j : ℚ) : ℝ) := by exact_mod_cast hε
  have hlam : -Real.logb 2 (Λ : ℝ) ≤ r * (3 * (1 / 2 : ℝ) ^ j) := by
    have h1 := neg_logb_le_of_le (by exact_mod_cast pow_pos hε r)
      (show (((1 - (1 / 2 : ℚ) ^ j) ^ r : ℚ) : ℝ) ≤ (Λ : ℝ) by exact_mod_cast hround)
    rw [Rat.cast_pow, Real.logb_pow] at h1
    have h2 := mul_le_mul_of_nonneg_left (stay_code_le hj) (Nat.cast_nonneg (α := ℝ) r)
    linarith
  -- the ideal bound's expansion, as in `dormant_survivor_code`
  have hSr : (0 : ℝ) < (pathSurvivors e x σ (n + 1)).card := by exact_mod_cast hSpos
  have hKr : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hcard
  have h0r : (0 : ℝ) < (π (σ 0) : ℝ) := by exact_mod_cast h0
  have hTr : ∀ t ∈ range n, ((T (σ t) (σ (t + 1)) : ℚ) : ℝ) ≠ 0 := fun t ht =>
    (by exact_mod_cast (hTσ t (mem_range.mp ht)).ne' : ((T (σ t) (σ (t + 1)) : ℚ) : ℝ) ≠ 0)
  have hXe : Real.logb 2 (X : ℝ) = Real.logb 2 ((pathSurvivors e x σ (n + 1)).card) -
      Real.logb 2 (Fintype.card κ) + (Real.logb 2 (π (σ 0) : ℝ) +
        ∑ t ∈ range n, Real.logb 2 (T (σ t) (σ (t + 1)) : ℝ)) := by
    rw [hX]
    push_cast
    rw [Real.logb_mul (by positivity) (mul_pos h0r (prod_pos fun t ht => by
        exact_mod_cast hTσ t (mem_range.mp ht))).ne', Real.logb_div hSr.ne' hKr.ne',
      Real.logb_mul h0r.ne' (prod_ne_zero_iff.mpr hTr), Real.logb_prod _ _ hTr]
  rw [hXe] at hR
  linarith

end ExecutedSurvivors

section Audit

#print axioms fwd_path_le
#print axioms prefix_pos
#print axioms forward_dominance_nonneg
#print axioms keyPrior_isPrior
#print axioms keyKernel_stochastic
#print axioms dormant_survivor_code
#print axioms layer_survivors
#print axioms productKernel_stochastic
#print axioms productKernel_path
#print axioms share_path_code
#print axioms stay_code_le
#print axioms share_path_code_le
#print axioms exec_total_le
#print axioms exec_path_le
#print axioms forward_executed_nonneg
#print axioms dormant_survivor_executed
#print axioms dormant_executed_code

end Audit

end Holonics.Compression.Landmark.Context.Dormancy
