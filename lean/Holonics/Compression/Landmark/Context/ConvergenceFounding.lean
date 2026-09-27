import Holonics.Compression.Landmark.Context.LocalWeighing

/-!
# Compression.Landmark.Context.ConvergenceFounding: a landmark is founded where paths converge, at its second arrival

[definition; agent-inferred] Decision 36 of the step 4 design (`docs/plans/THE_REBUILD.md`, "A
landmark is founded where paths converge"), rebuild step 4 (#73). The elementary objects define a
landmark as a face where navigator paths converge. Decision 28 founded every node of the landmark
tree at its first arrival; at scale the deepest nodes are mostly visited once, hold no convergence,
and their memory capped the depth. Here a node is founded at its **second** arrival: until then the
opened path stops at its deepest present ancestor, and the unfounded child reads as **absent** (its
parent reads its own face alone), not as a KT node with no counts. The computational object is the
helical pair interaction; this owner is the receiving parametron's landmark tree founding a node
where two paths meet. Of the winding guide's six general objects it touches two: **faces and
placement** (the stopped path's face is a normalized receiving face) and the **tower thread** (the
path's restriction stops at its deepest present node, and an absent child reads through its
parent). The pair stays attached (each edge of the stopped path compares a node's face with its
child's); a tree has no two-cells, so no cell holonomy is claimed; the tube is the passage.

```text
present      the root, or a node an earlier arrival reached while its parent was present
stopped read τ = the deepest present node of the opened path, decided before the symbol;
             q_τ = e_τ (the node's own face alone: its child along the address is absent);
             q_d = λ_d e_d + (1 − λ_d) q_(d+1)  (d < τ)
weight       W_s = E_s at depth D ;  W_s = w_d E_s + (1 − w_d) ∏_b R_(s b) W_(s b)
             E_s: the node's own faces over the arrivals it read while present
             R_(s b): the parent's own faces over the arrivals that found s b absent
step         E'_d = E_d e_d(c) (d ≤ τ),  R'_(τ+1) = R_(τ+1) e_τ(c)  ⇒  W'_d = W_d q_d(c)  (d ≤ τ)
             β'_d = β_d e_d(c)/q_(d+1)(c) (d < τ) ;  β'_τ = β_τ (the stop moves E and P alike)
trees        W_s = Σ_S prior_w(S) ∏_(leaves ℓ) E_ℓ ∏_(splits t, letters b) R_(t b) ;  Σ_S prior_w(S) = 1
dominance    −log₂ W ≤ −log₂ prior_w(S) − log₂ ∏_(leaves) E − log₂ ∏_(split children) R    every S
first        every node present (τ = D), R = 1, E = KT(N): W = stopWeight w N, λ = stopLam (Decision 28)
second       the arrival that finds a child absent gives it its first count; the child opens at its
             second arrival with that count: E_s = KT(N_s)/KT(first count), e_s = KT's face of N_s
```

[proved-derived; formal-checked] What is proved.

1. **The stopped path is normalized under any stopping rule decided before the symbol**
   (`stopped_face_normalized`, `prequentialCode`, `prequential_code_complete`,
   `stopping_rule_normalized`): for positive normalized node faces and stop weights in `[0, 1]`, the
   path face stopped at any depth `τ` is positive and normalized; for any causal stopping rule `τ(h)`
   (a function of the past, never of the next class) the stopped faces' prequential code is positive
   and sums to one over the words of every length: a complete code.
2. **The tree with absent children** (`convWeight`, `convSplit`, `convLik`,
   `conv_mixture_over_trees`, `conv_kraft_and_dominance`): for any positive own weights `E` and
   pre-factors `R`, the weight is the mixture over pruned trees with the stop law's prior and the
   likelihood `∏_(leaves) E ∏_(split children) R`; the prior sums to one (the Kraft form), and the tree
   codes within `−log₂ prior_w(S)` of every pruned tree `S`, in particular of every pruned tree whose
   leaves are founded (an absent node's own weight is one, `convWeight_unit`).
3. **The stopped step** (`convLam`, `convRatio`, `convLam_mem`, `convWeight_congr`, `conv_off`,
   `conv_deep`, `conv_weight_step`, `conv_split_step`, `conv_ratio_step`): an arrival that moves each
   present node's own weight by its own face and the absent child's pre-factor by the stopped node's
   face multiplies each opened node's weight by the stopped path's face; the ratio steps by
   `β' = β e/q'` above the stop and is unchanged at the stop.
4. **Decision 28 is the case "found at the first arrival"** (`stopDepth`, `stopDepth_spec`,
   `stopDepth_all`, `convWeight_first_arrival`, `convLik_first_arrival`,
   `first_arrival_is_the_full_tree`): when every node is present (an unfounded one reading as the
   prior, `Tree.unfounded_reads_prior`) the path never stops above `D` and no pre-factor
   moves, and the weight, the pruned trees' likelihood and the stop weights are the declared stop
   law's (`Tree.stopWeight`, `treeLik`, `stopLam`).
5. **The second arrival** (`Convergence`, `Convergence.present`, `Convergence.own`,
   `Convergence.receive`, `Convergence.Inv`, `convergence_step`, `convergenceOf`,
   `convergence_is_probability`, `second_arrival_opens_with_the_first_count`): the standing holds
   each node's counts (its opening count included), its opening count (its first arrival's) and its
   pre-factor; no occurrence is retained. The arrival that finds a child absent gives it its first
   count, which is its opening count, and the child is present at its second arrival; an opening
   moves no weight (its own weight is `1` before and after). Over a stream with a causal context the
   root weight is the product of the stopped faces and a probability law on the words of every
   length.

[proved-standard] The recursive mixture is Willems, Shtarkov and Tjalkens (1995); a context tree
grown only where a context recurs is the growth rule of PPM-style models. The proofs here are this
owner's.

[conditional] The dominance compares against the pruned tree's leaves' own faces and the pre-factors
of its splits' absent children, which this law's stops coded with the parent's face. A founded
leaf's own weight is `E_ℓ = KT(x_ℓ)/KT(x₁) = |A| KT(x_ℓ)` over the arrivals it met, and its
pre-factor is `R_ℓ = k_parent(x₁)`: against a first-arrival KT leaf over the same arrivals it gains
`log₂(|A| k_parent(x₁))`, positive exactly when the parent predicted the first digit above
`1/|A|`. But the path grows one depth a recurrence: a node meets arrivals only while its parent is
present, so a context must recur `d + 1` times before depth `d` reads it, where the first-arrival
tree reads it from its second occurrence. Which founding codes shorter is a measurement (the Rust
owner's header records it).

The Rust consumer is retired; realization at `d137e8a6` (`compression::landmark::context`, the founding at the
second arrival): its arena opened a node at the second arrival with the first arrival's count and
never stored `R` (the stopped node's `β` does not move, `conv_ratio_step`). The development cells
chose the founding at the first arrival (Decision 36, measured), and Decision 37 stores that tree
where paths part (`Compression/Landmark/Context/Compaction`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.ConvergenceFounding

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing

universe u

/-! ## 1. The stopped path under any stopping rule decided before the symbol -/

section Stopped

variable {A : Type*} [Fintype A]

/-- [proved-derived; formal-checked] **`stopped_face_normalized`.** For positive normalized node
faces at the depths `d ≤ τ` and stop weights in `[0, 1]`, the path face stopped at `τ` (the node at
`τ` reading its own face alone) is positive and normalized at every depth `d ≤ τ`, whatever `τ`. -/
theorem stopped_face_normalized (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (τ : ℕ)
    (hk : ∀ d ≤ τ, ∀ c, 0 < k d c) (hks : ∀ d ≤ τ, ∑ c, k d c = 1)
    (hl : ∀ d < τ, 0 ≤ lam d ∧ lam d ≤ 1) :
    ∀ d ≤ τ, (∀ c, 0 < pathFace k lam τ d c) ∧ ∑ c, pathFace k lam τ d c = 1 :=
  path_face_normalized k lam τ hk hks hl

/-- [definition] **The prequential code of a past** under a causal face `q h` (read at the past
`h`, newest class first, before the next class): the product of the faces its classes were read
at. -/
def prequentialCode (q : List A → A → ℚ) : List A → ℚ
  | [] => 1
  | c :: h => prequentialCode q h * q h c

/-- [proved-derived; formal-checked] **A causal normalized face is a complete code**: its
prequential code sums to one over the words of every length. -/
theorem prequential_code_complete (q : List A → A → ℚ) (hq : ∀ h, ∑ c, q h c = 1) :
    ∀ n, wordSum n (prequentialCode q) = 1 := by
  have e : (fun h => ∑ c, prequentialCode q (c :: h)) = prequentialCode q := by
    funext h
    simp only [prequentialCode, ← Finset.mul_sum, hq, mul_one]
  intro n
  induction n with
  | zero => simp [wordSum, prequentialCode]
  | succ n ih => rw [wordSum, e, ih]

/-- [proved-derived; formal-checked] **`stopping_rule_normalized`: any stopping rule decided
before the symbol gives a normalized face and a complete code.** For causal node faces `k h`
(positive, normalized), causal stop weights `lam h ∈ [0, 1]` and any causal stopping depth `τ h`
(each a function of the past `h` only), the stopped face at the root is positive and normalized,
the prequential code is positive, and it sums to one over the words of every length. -/
theorem stopping_rule_normalized (k : List A → ℕ → A → ℚ) (lam : List A → ℕ → ℚ)
    (τ : List A → ℕ) (hk : ∀ h d c, 0 < k h d c) (hks : ∀ h d, ∑ c, k h d c = 1)
    (hl : ∀ h d, 0 ≤ lam h d ∧ lam h d ≤ 1) :
    (∀ h, (∀ c, 0 < pathFace (k h) (lam h) (τ h) 0 c) ∧
        ∑ c, pathFace (k h) (lam h) (τ h) 0 c = 1) ∧
      (∀ h, 0 < prequentialCode (fun h => pathFace (k h) (lam h) (τ h) 0) h) ∧
      ∀ n, wordSum n (prequentialCode fun h => pathFace (k h) (lam h) (τ h) 0) = 1 ∧
        ∑ v : Fin n → A,
          prequentialCode (fun h => pathFace (k h) (lam h) (τ h) 0) (List.ofFn v) = 1 := by
  have hface : ∀ h, (∀ c, 0 < pathFace (k h) (lam h) (τ h) 0 c) ∧
      ∑ c, pathFace (k h) (lam h) (τ h) 0 c = 1 := fun h =>
    stopped_face_normalized (k h) (lam h) (τ h) (fun d _ c => hk h d c) (fun d _ => hks h d)
      (fun d _ => hl h d) 0 (Nat.zero_le _)
  refine ⟨hface, fun h => ?_, fun n => ?_⟩
  · induction h with
    | nil => simp [prequentialCode]
    | cons c h ih =>
      simp only [prequentialCode]
      exact mul_pos ih ((hface h).1 c)
  · have hn := prequential_code_complete _ (fun h => (hface h).2) n
    exact ⟨hn, by rw [wordSum_eq_sum] at hn; exact hn⟩

end Stopped

/-! ## 2. The tree with absent children: the Kraft form and the dominance -/

section Weight

variable {Ltr : Type u} [Fintype Ltr] [DecidableEq Ltr]

/-- [definition] **The tree with absent children** at node `s` with `m` levels below it: the own
weight `E_s` at the maximum depth, and `W_s = w_|s| E_s + (1 − w_|s|) ∏_b R_(s b) W_(s b)` above it,
the child's pre-factor `R_(s b)` carrying its parent's faces over the arrivals that found it
absent. -/
def convWeight (w : ℕ → ℚ) (E R : List Ltr → ℚ) : ℕ → List Ltr → ℚ
  | 0, s => E s
  | m + 1, s => w s.length * E s +
      (1 - w s.length) * ∏ b, R (s ++ [b]) * convWeight w E R m (s ++ [b])

/-- [definition] **The split weight** `P_s = ∏_b R_(s b) W_(s b)`. -/
def convSplit (w : ℕ → ℚ) (E R : List Ltr → ℚ) (m : ℕ) (s : List Ltr) : ℚ :=
  ∏ b, R (s ++ [b]) * convWeight w E R m (s ++ [b])

omit [DecidableEq Ltr] in
theorem convWeight_succ (w : ℕ → ℚ) (E R : List Ltr → ℚ) (m : ℕ) (s : List Ltr) :
    convWeight w E R (m + 1) s = w s.length * E s + (1 - w s.length) * convSplit w E R m s := rfl

/-- [definition] **The likelihood of a pruned tree with absent children**: its leaves' own weights
times the pre-factors of its splits' children. -/
def convLik (E R : List Ltr → ℚ) : (m : ℕ) → List Ltr → PrunedTree Ltr m → ℚ
  | 0, s, _ => E s
  | m + 1, s, S => Option.elim (S : Option (Ltr → PrunedTree Ltr m)) (E s)
      fun f => ∏ b, R (s ++ [b]) * convLik E R m (s ++ [b]) (f b)

omit [DecidableEq Ltr] in
theorem convWeight_pos {w : ℕ → ℚ} (hw : StopLaw w) {E R : List Ltr → ℚ} (hE : ∀ s, 0 < E s)
    (hR : ∀ s, 0 < R s) : ∀ m s, 0 < convWeight w E R m s
  | 0, s => hE s
  | m + 1, s => by
    have hP : 0 < ∏ b, R (s ++ [b]) * convWeight w E R m (s ++ [b]) :=
      Finset.prod_pos fun _ _ => mul_pos (hR _) (convWeight_pos hw hE hR m _)
    obtain ⟨h0, h1⟩ := hw s.length
    have e1 := mul_pos h0 (hE s)
    have e2 := mul_pos (sub_pos.mpr h1) hP
    simp only [convWeight]
    linarith

omit [DecidableEq Ltr] in
theorem convSplit_pos {w : ℕ → ℚ} (hw : StopLaw w) {E R : List Ltr → ℚ} (hE : ∀ s, 0 < E s)
    (hR : ∀ s, 0 < R s) (m : ℕ) (s : List Ltr) : 0 < convSplit w E R m s :=
  Finset.prod_pos fun _ _ => mul_pos (hR _) (convWeight_pos hw hE hR m _)

omit [DecidableEq Ltr] in
theorem convLik_pos {E R : List Ltr → ℚ} (hE : ∀ s, 0 < E s) (hR : ∀ s, 0 < R s) :
    ∀ m s (S : PrunedTree Ltr m), 0 < convLik E R m s S
  | 0, s, _ => hE s
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [convLik, Option.elim]; exact hE s
    | some f =>
      simp only [convLik, Option.elim]
      exact Finset.prod_pos fun b _ => mul_pos (hR _) (convLik_pos hE hR m _ _)

/-- [proved-derived; formal-checked] **`conv_mixture_over_trees`: the tree with absent children is
the mixture over pruned trees with the stop law's prior**,
`W_s = Σ_S prior_w(S) ∏_(leaves ℓ) E_ℓ ∏_(splits t, letters b) R_(t b)`. -/
theorem conv_mixture_over_trees (w : ℕ → ℚ) (E R : List Ltr → ℚ) :
    ∀ m s, convWeight w E R m s =
      ∑ S : PrunedTree Ltr m, PrunedTree.prior w m s.length S * convLik E R m s S
  | 0, s => by
    have hc : Fintype.card (PrunedTree Ltr 0) = 1 := rfl
    simp [convWeight, convLik, PrunedTree.prior, hc]
  | m + 1, s => by
    rw [convWeight_succ, convSplit]
    simp only [conv_mixture_over_trees w E R m, List.length_append, List.length_singleton,
      Finset.mul_sum]
    rw [Fintype.prod_sum]
    have e : ∑ S : PrunedTree Ltr (m + 1),
        PrunedTree.prior w (m + 1) s.length S * convLik E R (m + 1) s S =
        w s.length * E s + ∑ f : Ltr → PrunedTree Ltr m,
          ((1 - w s.length) * ∏ b, PrunedTree.prior w m (s.length + 1) (f b)) *
            ∏ b, R (s ++ [b]) * convLik E R m (s ++ [b]) (f b) :=
      Fintype.sum_option (fun S : Option (Ltr → PrunedTree Ltr m) =>
        PrunedTree.prior w (m + 1) s.length S * convLik E R (m + 1) s S)
    rw [e, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring

/-- [proved-derived; formal-checked] **`conv_kraft_and_dominance`.** Under any stop-weight law, own
weights and pre-factors positive:
* **Kraft**: the pruned trees' prior weights sum to one (the stop/split code is complete);
* **dominance**: for every pruned tree `S`, `prior_w(S) · L(S) ≤ W` with
  `L(S) = ∏_(leaves) E ∏_(split children) R`, so
  `−log₂ W ≤ −log₂ prior_w(S) − log₂ L(S)`: the tree codes within its prior's code of every pruned
  tree, and in particular of every pruned tree whose leaves are founded. -/
theorem conv_kraft_and_dominance {w : ℕ → ℚ} (hw : StopLaw w) {E R : List Ltr → ℚ}
    (hE : ∀ s, 0 < E s) (hR : ∀ s, 0 < R s) (m : ℕ) (s : List Ltr) :
    ∑ S : PrunedTree Ltr m, PrunedTree.prior w m s.length S = 1 ∧
      ∀ S : PrunedTree Ltr m,
        PrunedTree.prior w m s.length S * convLik E R m s S ≤ convWeight w E R m s ∧
        -Real.logb 2 (convWeight w E R m s : ℝ) ≤
          -Real.logb 2 (PrunedTree.prior w m s.length S : ℝ) -
            Real.logb 2 (convLik E R m s S : ℝ) := by
  have hdom : ∀ S : PrunedTree Ltr m,
      PrunedTree.prior w m s.length S * convLik E R m s S ≤ convWeight w E R m s := by
    intro S
    rw [conv_mixture_over_trees w E R m s]
    exact Finset.single_le_sum
      (f := fun S => PrunedTree.prior w m s.length S * convLik E R m s S)
      (fun S _ => (mul_pos (PrunedTree.prior_pos hw m _ S) (convLik_pos hE hR m s S)).le)
      (Finset.mem_univ S)
  refine ⟨PrunedTree.prior_sum w m s.length, fun S => ⟨hdom S, ?_⟩⟩
  have hpR : (0 : ℝ) < (PrunedTree.prior w m s.length S : ℝ) := by
    exact_mod_cast PrunedTree.prior_pos hw m s.length S
  have hLR : (0 : ℝ) < (convLik E R m s S : ℝ) := by exact_mod_cast convLik_pos hE hR m s S
  have hdR : ((PrunedTree.prior w m s.length S : ℚ) : ℝ) * (convLik E R m s S : ℝ) ≤
      (convWeight w E R m s : ℝ) := by exact_mod_cast hdom S
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hdR
  rw [Real.logb_mul hpR.ne' hLR.ne'] at hlog
  linarith

omit [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] **`convWeight_unit`: a subtree nothing has reached weighs one**:
with own weights and pre-factors `1` at a node and below it, `W = 1` (the prior is complete). -/
theorem convWeight_unit (w : ℕ → ℚ) {E R : List Ltr → ℚ} :
    ∀ m s, (∀ t, E (s ++ t) = 1) → (∀ t, t ≠ [] → R (s ++ t) = 1) → convWeight w E R m s = 1
  | 0, s, hE, _ => by simpa [convWeight] using hE []
  | m + 1, s, hE, hR => by
    have hs : E s = 1 := by simpa using hE []
    have hP : ∏ b, R (s ++ [b]) * convWeight w E R m (s ++ [b]) = 1 :=
      Finset.prod_eq_one fun b _ => by
        rw [hR [b] (by simp), convWeight_unit w m (s ++ [b])
          (fun t => by simpa using hE (b :: t)) (fun t _ => by simpa using hR (b :: t) (by simp)),
          one_mul]
    simp only [convWeight, hs, hP]
    ring

omit [DecidableEq Ltr] in
/-- **Found at the first arrival, no pre-factor moves**: with `R = 1` the tree with absent children
is the tree over own weights (`LocalWeighing.ownWeight`). -/
theorem convWeight_first_arrival (w : ℕ → ℚ) (E : List Ltr → ℚ) :
    ∀ m s, convWeight w E (fun _ => 1) m s = ownWeight w E m s
  | 0, _ => rfl
  | m + 1, s => by
    simp only [convWeight, ownWeight, one_mul, convWeight_first_arrival w E m]

omit [DecidableEq Ltr] in
/-- With `R = 1` a pruned tree's likelihood is its leaves' own weights (`LocalWeighing.ownLik`). -/
theorem convLik_first_arrival (E : List Ltr → ℚ) :
    ∀ m s (S : PrunedTree Ltr m), convLik E (fun _ => 1) m s S = ownLik E m s S
  | 0, _, _ => rfl
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [convLik, ownLik, Option.elim]
    | some f => simp only [convLik, ownLik, Option.elim, one_mul, convLik_first_arrival E m]

end Weight

/-! ## 3. The stopped step -/

section Step

variable {Ltr : Type u} [Fintype Ltr] [DecidableEq Ltr] {A : Type*}

/-- [definition] **The stop weight at depth `d`** of the opened path:
`λ_d = w_d E_d/(w_d E_d + (1 − w_d) P_d)`, `P_d` the split weight with its children's
pre-factors. -/
def convLam (w : ℕ → ℚ) (E R : List Ltr → ℚ) (D : ℕ) (a : List Ltr) (d : ℕ) : ℚ :=
  w d * E (a.take d) / (w d * E (a.take d) + (1 - w d) * convSplit w E R (D - d - 1) (a.take d))

/-- [definition] **The stop-to-split ratio** `β_d = w_d E_d/((1 − w_d) P_d)`. -/
def convRatio (w : ℕ → ℚ) (E R : List Ltr → ℚ) (D : ℕ) (a : List Ltr) (d : ℕ) : ℚ :=
  w d * E (a.take d) / ((1 - w d) * convSplit w E R (D - d - 1) (a.take d))

omit [DecidableEq Ltr] in
theorem convLam_mem {w : ℕ → ℚ} (hw : StopLaw w) {E R : List Ltr → ℚ} (hE : ∀ s, 0 < E s)
    (hR : ∀ s, 0 < R s) (D : ℕ) (a : List Ltr) (d : ℕ) :
    0 < convLam w E R D a d ∧ convLam w E R D a d < 1 := by
  have hEd := hE (a.take d)
  have hP := convSplit_pos hw hE hR (D - d - 1) (a.take d)
  obtain ⟨h0, h1⟩ := hw d
  have e1 := mul_pos h0 hEd
  have e2 := mul_pos (sub_pos.mpr h1) hP
  unfold convLam
  exact ⟨div_pos e1 (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

omit [DecidableEq Ltr] in
/-- A node's weight is unchanged when nothing moves its own weight at it or below it, nor a
pre-factor strictly below it. -/
theorem convWeight_congr (w : ℕ → ℚ) {E E' R R' : List Ltr → ℚ} :
    ∀ m s, (∀ t, E' (s ++ t) = E (s ++ t)) → (∀ t, t ≠ [] → R' (s ++ t) = R (s ++ t)) →
      convWeight w E' R' m s = convWeight w E R m s
  | 0, s, hE, _ => by simpa [convWeight] using hE []
  | m + 1, s, hE, hR => by
    have hs : E' s = E s := by simpa using hE []
    have hP : convSplit w E' R' m s = convSplit w E R m s :=
      Finset.prod_congr rfl fun b _ => by
        rw [show R' (s ++ [b]) = R (s ++ [b]) by simpa using hR [b] (by simp),
          convWeight_congr w m (s ++ [b]) (fun t => by simpa using hE (b :: t))
            (fun t _ => by simpa using hR (b :: t) (by simp))]
    rw [convWeight_succ, convWeight_succ, hs, hP]

omit [Fintype Ltr] [DecidableEq Ltr] in
theorem take_ne_of_length_ne {a s : List Ltr} {n : ℕ} (h : s.length ≠ (a.take n).length) :
    s ≠ a.take n := fun e => h (congrArg List.length e)

omit [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] **Off the opened path nothing moves**: at a node off the path
the arrival moves neither its pre-factor nor its weight. -/
theorem conv_off (w : ℕ → ℚ) {E E' R R' : List Ltr → ℚ} {a : List Ltr} {τ D : ℕ}
    (hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) → E' s = E s)
    (hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → R' s = R s)
    {s : List Ltr} (h : ¬ a.take s.length = s) (m : ℕ) :
    R' s = R s ∧ convWeight w E' R' m s = convWeight w E R m s := by
  have hR : ∀ t, R' (s ++ t) = R (s ++ t) := fun t => hRoff _ fun hp =>
    off_path_descendant h t (by rw [hp.1]; exact opens_take a (τ + 1))
  exact ⟨by simpa using hR [], convWeight_congr w m s (fun t => hEoff _ fun hp =>
    off_path_descendant h t hp.1) fun t _ => hR t⟩

omit [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] **Below the stop nothing moves**: at a node deeper than the
stopping depth the arrival moves no weight (the absent child's pre-factor moves at its parent's
split, not below the child). -/
theorem conv_deep (w : ℕ → ℚ) {E E' R R' : List Ltr → ℚ} {a : List Ltr} {τ D : ℕ}
    (hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) → E' s = E s)
    (hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → R' s = R s)
    {s : List Ltr} (hs : τ < s.length) (m : ℕ) :
    convWeight w E' R' m s = convWeight w E R m s := by
  refine convWeight_congr w m s (fun t => hEoff _ fun hp => ?_) fun t ht => hRoff _ fun hp => ?_
  · have := hp.2
    simp only [List.length_append] at this
    omega
  · have hlen := congrArg List.length hp.1
    cases t with
    | nil => exact ht rfl
    | cons x t =>
      simp only [List.length_append, List.length_cons, List.length_take] at hlen
      omega

/-- [proved-derived; formal-checked] **`conv_weight_step`: the stopped path's face is the successive
likelihood ratio.** For an address `a` of length at least `D`, a stopping depth `τ ≤ D` and own
faces `e`: when the arrival moves each present node's own weight by its own face
(`E'_d = E_d e_d(c)`, `d ≤ τ`), the absent child's pre-factor by the stopped node's face
(`R'_(τ+1) = R_(τ+1) e_τ(c)` when `τ < D`), and nothing else, then at every depth `d ≤ τ`,
`W'_d = W_d · q_d(c)` with `q` the path face stopped at `τ`. -/
theorem conv_weight_step {w : ℕ → ℚ} (hw : StopLaw w) {E E' R R' : List Ltr → ℚ}
    (hE : ∀ s, 0 < E s) (hR : ∀ s, 0 < R s)
    {D τ : ℕ} {a : List Ltr} (hD : D ≤ a.length) (hτ : τ ≤ D) (e : ℕ → A → ℚ) (c : A)
    (hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) → E' s = E s)
    (hEon : ∀ d ≤ τ, E' (a.take d) = E (a.take d) * e d c)
    (hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → R' s = R s)
    (hRon : τ < D → R' (a.take (τ + 1)) = R (a.take (τ + 1)) * e τ c) :
    ∀ d ≤ τ, convWeight w E' R' (D - d) (a.take d) =
      convWeight w E R (D - d) (a.take d) * pathFace e (convLam w E R D a) τ d c := by
  suffices h : ∀ j d, d + j = τ → convWeight w E' R' (D - d) (a.take d) =
      convWeight w E R (D - d) (a.take d) * pathFace e (convLam w E R D a) τ d c by
    intro d hd
    exact h (τ - d) d (by omega)
  intro j
  induction j with
  | zero =>
    intro d hd
    have hdτ : d = τ := by omega
    rw [hdτ, pathFace_deepest]
    rcases Nat.lt_or_ge τ D with hlt | hge
    · -- the stop above the maximum depth: the absent child's pre-factor takes the stopped face
      obtain ⟨m, hm⟩ : ∃ m, D - τ = m + 1 := ⟨D - τ - 1, by omega⟩
      have hda : τ < a.length := by omega
      have hlen : (a.take τ).length = τ := by simp; omega
      have hsplit : convSplit w E' R' m (a.take τ) = convSplit w E R m (a.take τ) * e τ c := by
        unfold convSplit
        refine prod_update_one _ _ a[τ] (e τ c) ?_ fun b hb => ?_
        · have ek : a.take τ ++ [a[τ]] = a.take (τ + 1) := (restrict_succ hda).symm
          rw [ek, hRon hlt, conv_deep w hEoff hRoff (s := a.take (τ + 1)) (by simp; omega) m]
          ring
        · obtain ⟨h1, h2⟩ := conv_off w hEoff hRoff (off_path_child hda hb) m
          rw [h1, h2]
      rw [hm, convWeight_succ, convWeight_succ, hsplit, hlen, hEon τ le_rfl]
      ring
    · rw [show D - τ = 0 by omega]
      simp only [convWeight]
      exact hEon τ le_rfl
  | succ j ih =>
    intro d hd
    have hdτ : d < τ := by omega
    have hda : d < a.length := by omega
    have hlen : (a.take d).length = d := by simp; omega
    obtain ⟨m, hm⟩ : ∃ m, D - d = m + 1 := ⟨D - d - 1, by omega⟩
    have hchild := ih (d + 1) (by omega)
    rw [show D - (d + 1) = m by omega] at hchild
    have hsplit : convSplit w E' R' m (a.take d) =
        convSplit w E R m (a.take d) * pathFace e (convLam w E R D a) τ (d + 1) c := by
      unfold convSplit
      refine prod_update_one _ _ a[d] _ ?_ fun b hb => ?_
      · have ek : a.take d ++ [a[d]] = a.take (d + 1) := (restrict_succ hda).symm
        have hRd : R' (a.take (d + 1)) = R (a.take (d + 1)) := hRoff _ fun hp =>
          take_ne_of_length_ne (by have := hp.2; simp only [List.length_take]; omega) hp.1
        rw [ek, hRd, hchild]
        ring
      · obtain ⟨h1, h2⟩ := conv_off w hEoff hRoff (off_path_child hda hb) m
        rw [h1, h2]
    rw [hm, convWeight_succ, convWeight_succ, hsplit, hlen, hEon d hdτ.le,
      pathFace_step _ _ hdτ]
    have hlam : convLam w E R D a d = w d * E (a.take d) /
        (w d * E (a.take d) + (1 - w d) * convSplit w E R m (a.take d)) := by
      unfold convLam
      rw [show D - d - 1 = m by omega]
    rw [hlam]
    have hEd := hE (a.take d)
    have hP := convSplit_pos hw hE hR m (a.take d)
    obtain ⟨h0, h1⟩ := hw d
    have hden : w d * E (a.take d) + (1 - w d) * convSplit w E R m (a.take d) ≠ 0 :=
      (add_pos (mul_pos h0 hEd) (mul_pos (sub_pos.mpr h1) hP)).ne'
    field_simp
    ring

/-- [proved-derived; formal-checked] **`conv_split_step`: the split weight's step.** Above the stop
the split weight moves by the child's stopped face, `P'_d = P_d q_(d+1)(c)`; at the stop it moves by
the stopped node's own face, `P'_τ = P_τ e_τ(c)`, as its own weight does. -/
theorem conv_split_step {w : ℕ → ℚ} (hw : StopLaw w) {E E' R R' : List Ltr → ℚ}
    (hE : ∀ s, 0 < E s) (hR : ∀ s, 0 < R s)
    {D τ : ℕ} {a : List Ltr} (hD : D ≤ a.length) (hτ : τ ≤ D) (e : ℕ → A → ℚ) (c : A)
    (hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) → E' s = E s)
    (hEon : ∀ d ≤ τ, E' (a.take d) = E (a.take d) * e d c)
    (hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → R' s = R s)
    (hRon : τ < D → R' (a.take (τ + 1)) = R (a.take (τ + 1)) * e τ c) :
    (∀ d < τ, convSplit w E' R' (D - d - 1) (a.take d) =
      convSplit w E R (D - d - 1) (a.take d) * pathFace e (convLam w E R D a) τ (d + 1) c) ∧
      (τ < D → convSplit w E' R' (D - τ - 1) (a.take τ) =
        convSplit w E R (D - τ - 1) (a.take τ) * e τ c) := by
  have hstep := conv_weight_step hw hE hR hD hτ e c hEoff hEon hRoff hRon
  refine ⟨fun d hd => ?_, fun hlt => ?_⟩
  · have hda : d < a.length := by omega
    have hchild := hstep (d + 1) (by omega)
    rw [show D - (d + 1) = D - d - 1 by omega] at hchild
    unfold convSplit
    refine prod_update_one _ _ a[d] _ ?_ fun b hb => ?_
    · have ek : a.take d ++ [a[d]] = a.take (d + 1) := (restrict_succ hda).symm
      have hRd : R' (a.take (d + 1)) = R (a.take (d + 1)) := hRoff _ fun hp =>
        take_ne_of_length_ne (by have := hp.2; simp only [List.length_take]; omega) hp.1
      rw [ek, hRd, hchild]
      ring
    · obtain ⟨h1, h2⟩ := conv_off w hEoff hRoff (off_path_child hda hb) (D - d - 1)
      rw [h1, h2]
  · have hda : τ < a.length := by omega
    unfold convSplit
    refine prod_update_one _ _ a[τ] (e τ c) ?_ fun b hb => ?_
    · have ek : a.take τ ++ [a[τ]] = a.take (τ + 1) := (restrict_succ hda).symm
      rw [ek, hRon hlt,
        conv_deep w hEoff hRoff (s := a.take (τ + 1)) (by simp; omega) (D - τ - 1)]
      ring
    · obtain ⟨h1, h2⟩ := conv_off w hEoff hRoff (off_path_child hda hb) (D - τ - 1)
      rw [h1, h2]

variable [Fintype A]

/-- [proved-derived; formal-checked] **`conv_ratio_step`: the executed step.** The stop weight is
`λ = β/(1 + β)` with `β_d = w_d E_d/((1 − w_d) P_d)`; above the stop an arrival moves
`β' = β e_d(c)/q_(d+1)(c)` (Decision 28's step), and at the stop the ratio does not move: its own
weight and its split weight both take the stopped node's own face. So the executed tree steps `β`
only at the mixing nodes of the stopped read and stores no pre-factor. -/
theorem conv_ratio_step {w : ℕ → ℚ} (hw : StopLaw w) {E E' R R' : List Ltr → ℚ}
    (hE : ∀ s, 0 < E s) (hR : ∀ s, 0 < R s)
    {D τ : ℕ} {a : List Ltr} (hD : D ≤ a.length) (hτ : τ ≤ D) (e : ℕ → A → ℚ) (c : A)
    (he : ∀ d ≤ τ, ∀ c, 0 < e d c) (hes : ∀ d ≤ τ, ∑ c, e d c = 1)
    (hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) → E' s = E s)
    (hEon : ∀ d ≤ τ, E' (a.take d) = E (a.take d) * e d c)
    (hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → R' s = R s)
    (hRon : τ < D → R' (a.take (τ + 1)) = R (a.take (τ + 1)) * e τ c) :
    (∀ d, convLam w E R D a d = convRatio w E R D a d / (1 + convRatio w E R D a d)) ∧
      (∀ d < τ, convRatio w E' R' D a d =
        convRatio w E R D a d * e d c / pathFace e (convLam w E R D a) τ (d + 1) c) ∧
      (τ < D → convRatio w E' R' D a τ = convRatio w E R D a τ) := by
  obtain ⟨hsplit, hstop⟩ := conv_split_step hw hE hR hD hτ e c hEoff hEon hRoff hRon
  refine ⟨fun d => ?_, fun d hd => ?_, fun hlt => ?_⟩
  · have hEd := hE (a.take d)
    have hP := convSplit_pos hw hE hR (D - d - 1) (a.take d)
    obtain ⟨h0, h1⟩ := hw d
    have hw1 : (0 : ℚ) < 1 - w d := sub_pos.mpr h1
    have hden : 0 < w d * E (a.take d) + (1 - w d) * convSplit w E R (D - d - 1) (a.take d) :=
      add_pos (mul_pos h0 hEd) (mul_pos hw1 hP)
    have hw1' : (1 : ℚ) - w d ≠ 0 := hw1.ne'
    unfold convLam convRatio
    field_simp
    ring
  · have hq : 0 < pathFace e (convLam w E R D a) τ (d + 1) c :=
      (stopped_face_normalized e (convLam w E R D a) τ he hes
        (fun d _ => ⟨(convLam_mem hw hE hR D a d).1.le, (convLam_mem hw hE hR D a d).2.le⟩)
        (d + 1) (by omega)).1 c
    have hPp := convSplit_pos hw hE hR (D - d - 1) (a.take d)
    obtain ⟨h0, h1⟩ := hw d
    have hw1' : (1 : ℚ) - w d ≠ 0 := (sub_pos.mpr h1).ne'
    unfold convRatio
    rw [hEon d hd.le, hsplit d hd]
    field_simp
  · have he0 : 0 < e τ c := he τ le_rfl c
    have hPp := convSplit_pos hw hE hR (D - τ - 1) (a.take τ)
    obtain ⟨h0, h1⟩ := hw τ
    have hw1' : (1 : ℚ) - w τ ≠ 0 := (sub_pos.mpr h1).ne'
    unfold convRatio
    rw [hEon τ le_rfl, hstop hlt]
    field_simp

end Step

/-! ## 4. The stopping depth, and Decision 28 as the first arrival -/

section Depth

variable {Ltr : Type u}

/-- [definition] **The stopping depth** of an address under a presence reading: the deepest
`d ≤ D` whose opened nodes `a.take 1, …, a.take d` are all present (the root always is). It reads
only the standing, never the next class. -/
def stopDepth (present : List Ltr → Bool) (a : List Ltr) : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
    if stopDepth present a d = d ∧ present (a.take (d + 1)) = true then d + 1
    else stopDepth present a d

/-- [proved-derived; formal-checked] **`stopDepth_spec`.** The stopping depth lies within `D`,
every opened node down to it is present, and below it (when it stops above `D`) the child is
absent. -/
theorem stopDepth_spec (present : List Ltr → Bool) (a : List Ltr) :
    ∀ D, stopDepth present a D ≤ D ∧
      (∀ d, 1 ≤ d → d ≤ stopDepth present a D → present (a.take d) = true) ∧
      (stopDepth present a D < D → present (a.take (stopDepth present a D + 1)) = false)
  | 0 => ⟨le_rfl, fun d h1 h2 => by simp [stopDepth] at h2; omega, fun h => by
      simp [stopDepth] at h⟩
  | D + 1 => by
    obtain ⟨hle, hpres, habs⟩ := stopDepth_spec present a D
    by_cases hc : stopDepth present a D = D ∧ present (a.take (D + 1)) = true
    · have e : stopDepth present a (D + 1) = D + 1 := by simp only [stopDepth, if_pos hc]
      rw [e]
      refine ⟨le_rfl, fun d h1 h2 => ?_, fun h => absurd h (lt_irrefl _)⟩
      rcases Nat.lt_or_ge d (D + 1) with hlt | hge
      · exact hpres d h1 (by omega)
      · have : d = D + 1 := by omega
        subst this
        exact hc.2
    · have e : stopDepth present a (D + 1) = stopDepth present a D := by
        simp only [stopDepth, if_neg hc]
      rw [e]
      refine ⟨by omega, hpres, fun h => ?_⟩
      rcases Nat.lt_or_ge (stopDepth present a D) D with hlt | hge
      · exact habs hlt
      · have hD : stopDepth present a D = D := by omega
        rw [hD]
        cases hp : present (a.take (D + 1)) with
        | false => rfl
        | true => exact absurd ⟨hD, hp⟩ hc

/-- **When every node is present the path never stops above the maximum depth.** -/
theorem stopDepth_all (present : List Ltr → Bool) (a : List Ltr) (h : ∀ s, present s = true) :
    ∀ D, stopDepth present a D = D
  | 0 => rfl
  | D + 1 => by simp only [stopDepth, stopDepth_all present a h D, h, and_self, if_true]

variable [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] **`first_arrival_is_the_full_tree`: Decision 28's tree is the case
"found at the first arrival".** When every node is present at every arrival (an unfounded node
reading as the prior with no counts, `Tree.unfounded_reads_prior`), the path never stops
above `D`; no arrival finds a child absent, so every pre-factor stays `1`; and with the KT own
weights the tree with absent children is the declared stop law's tree, its pruned trees'
likelihood is `treeLik`, and its stop weights are `stopLam` (so the stopped face at `D` is
`stopFace`, whose step is `stop_weight_step`). -/
theorem first_arrival_is_the_full_tree (w : ℕ → ℚ) (N : TreeStanding Ltr A) (D : ℕ)
    (a : List Ltr) :
    stopDepth (fun _ => true) a D = D ∧
      (∀ m s, convWeight w (fun s => ktMass (N s)) (fun _ => 1) m s = stopWeight w N m s) ∧
      (∀ m s (S : PrunedTree Ltr m),
        convLik (fun s => ktMass (N s)) (fun _ => 1) m s S = treeLik N m s S) ∧
      convLam w (fun s => ktMass (N s)) (fun _ => 1) D a = stopLam w N D a := by
  have hW : ∀ m s, convWeight w (fun s => ktMass (N s)) (fun _ => 1) m s = stopWeight w N m s :=
    fun m s => by rw [convWeight_first_arrival, ownWeight_kt]
  refine ⟨stopDepth_all _ a (fun _ => rfl) D, hW,
    fun m s S => by rw [convLik_first_arrival, ownLik_kt], ?_⟩
  funext d
  have hP : convSplit w (fun s => ktMass (N s)) (fun _ => 1) (D - d - 1) (a.take d) =
      stopSplit w N (D - d - 1) (a.take d) := by
    unfold convSplit stopSplit
    simp only [one_mul, hW]
  unfold convLam stopLam
  rw [hP]

end Depth

/-! ## 5. The second arrival: the convergence standing and its law -/

section Second

/-- [definition] **The convergence standing** (Decision 36): at every node the counts it has met
(its opening count included; zero until an arrival reaches it), the count it opened with (its first
arrival's, which the arrival that found it absent gave it; none at the root, present from its first
arrival), and its pre-factor (its parent's faces over the arrivals that found it absent). It retains
counts and one ratio a node, never an occurrence. -/
structure Convergence (Ltr : Type u) (A : Type*) where
  count : List Ltr → A → ℕ
  opening : List Ltr → A → ℕ
  pre : List Ltr → ℚ

variable {Ltr : Type u} [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

namespace Convergence

/-- [definition] **Presence**: the root, or a node an earlier arrival reached. -/
def present (N : Convergence Ltr A) (s : List Ltr) : Bool :=
  s.isEmpty || decide (0 < ∑ c, N.count s c)

/-- [definition] **A node's own weight**: KT over the arrivals it read while present, given its
opening count, `KT(N_s)/KT(opening_s)`. -/
def own (N : Convergence Ltr A) (s : List Ltr) : ℚ := ktMass (N.count s) / ktMass (N.opening s)

/-- [definition] The standing nothing has reached. -/
def unreached : Convergence Ltr A := ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 1⟩

/-- [definition] **An arrival** of class `c` at address `a` in a tree of depth `D`: it stops at `τ`,
the deepest present node; every node of the stopped path counts `c`; the absent child below the
stop (when `τ < D`) is reached for the first time, counts `c` and opens with that count; its
pre-factor takes the stopped node's KT face. -/
def receive (N : Convergence Ltr A) (D : ℕ) (a : List Ltr) (c : A) : Convergence Ltr A where
  count := fun s =>
    if a.take s.length = s ∧ s.length ≤ stopDepth N.present a D + 1 ∧ s.length ≤ D then
      bump (N.count s) c
    else N.count s
  opening := fun s =>
    if s = a.take (stopDepth N.present a D + 1) ∧ stopDepth N.present a D < D then
      bump (N.opening s) c
    else N.opening s
  pre := fun s =>
    if s = a.take (stopDepth N.present a D + 1) ∧ stopDepth N.present a D < D then
      N.pre s * ktFace (N.count (a.take (stopDepth N.present a D))) c
    else N.pre s

/-- [definition] **The standing's invariant**: every pre-factor is positive, and a node nothing has
reached holds no opening count. -/
def Inv (N : Convergence Ltr A) : Prop :=
  (∀ s, 0 < N.pre s) ∧ ∀ s, ∑ c, N.count s c = 0 → N.opening s = fun _ => 0

omit [DecidableEq Ltr] [DecidableEq A] in
theorem unreached_inv : (unreached : Convergence Ltr A).Inv :=
  ⟨fun _ => by simp [unreached], fun _ _ => rfl⟩

omit [DecidableEq Ltr] [DecidableEq A] in
theorem own_pos [Nonempty A] (N : Convergence Ltr A) (s : List Ltr) : 0 < N.own s :=
  div_pos (ktMass_pos _) (ktMass_pos _)

end Convergence

open Convergence

omit [DecidableEq Ltr] [DecidableEq A] in
/-- The absent node's counts are empty: it is not the root and nothing reached it. -/
theorem absent_count_zero {N : Convergence Ltr A} {s : List Ltr}
    (h : N.present s = false) : ∑ c, N.count s c = 0 ∧ N.count s = fun _ => 0 := by
  simp only [present, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
    Nat.le_zero] at h
  refine ⟨h.2, funext fun c' => ?_⟩
  simpa using Finset.sum_eq_zero_iff.mp h.2 c' (Finset.mem_univ _)

/-- [proved-derived; formal-checked] **The arrival keeps the invariant.** -/
theorem receive_inv [Nonempty A] {N : Convergence Ltr A} (hN : N.Inv) {D : ℕ} {a : List Ltr}
    (hD : D ≤ a.length) (c : A) : (N.receive D a c).Inv := by
  obtain ⟨hpre, hzero⟩ := hN
  set τ := stopDepth N.present a D with hτdef
  refine ⟨fun s => ?_, fun s hs => ?_⟩
  · simp only [receive, ← hτdef]
    split_ifs
    · exact mul_pos (hpre s) (ktFace_pos _ c)
    · exact hpre s
  · simp only [receive, ← hτdef] at hs ⊢
    by_cases hb : a.take s.length = s ∧ s.length ≤ τ + 1 ∧ s.length ≤ D
    · simp only [if_pos hb, sum_bump] at hs
      omega
    · simp only [if_neg hb] at hs
      have hno : ¬ (s = a.take (τ + 1) ∧ τ < D) := by
        rintro ⟨rfl, hlt⟩
        apply hb
        have hl : (a.take (τ + 1)).length = τ + 1 := by simp; omega
        exact ⟨opens_take a (τ + 1), by omega, by omega⟩
      rw [if_neg hno]
      exact hzero s hs

/-- [definition] **The standing after a past** under a causal context `ctx` in a tree of depth
`D`: the standing nothing has reached, and each class arriving at the address its past opens. -/
def convergenceOf (D : ℕ) (ctx : List A → List Ltr) : List A → Convergence Ltr A
  | [] => unreached
  | c :: h => (convergenceOf D ctx h).receive D (ctx h) c

theorem convergenceOf_inv [Nonempty A] (D : ℕ) (ctx : List A → List Ltr)
    (hctx : ∀ h, D ≤ (ctx h).length) : ∀ h, (convergenceOf D ctx h).Inv
  | [] => unreached_inv
  | c :: h => receive_inv (convergenceOf_inv D ctx hctx h) (hctx h) c

/-- [proved-derived; formal-checked] **`second_arrival_opens_with_the_first_count`: a node is
founded at its second arrival, opening with its first arrival's count.** When the arrival stops
above the maximum depth, the child below the stop was absent (`present = false`); after it, that
child is present, it holds exactly this arrival's count as its counts and as its opening count, its
own weight is `1` (the opening moves no weight), and its pre-factor took the stopped node's face.
At its next arrival it reads KT's face of that one count. -/
theorem second_arrival_opens_with_the_first_count [Nonempty A] {N : Convergence Ltr A}
    (hN : N.Inv) {D : ℕ} {a : List Ltr} (hD : D ≤ a.length) (c : A)
    (hlt : stopDepth N.present a D < D) :
    N.present (a.take (stopDepth N.present a D + 1)) = false ∧
      (N.receive D a c).present (a.take (stopDepth N.present a D + 1)) = true ∧
      (N.receive D a c).count (a.take (stopDepth N.present a D + 1)) = bump (fun _ => 0) c ∧
      (N.receive D a c).opening (a.take (stopDepth N.present a D + 1)) = bump (fun _ => 0) c ∧
      (N.receive D a c).own (a.take (stopDepth N.present a D + 1)) = 1 ∧
      (N.receive D a c).pre (a.take (stopDepth N.present a D + 1)) =
        N.pre (a.take (stopDepth N.present a D + 1)) *
          ktFace (N.count (a.take (stopDepth N.present a D))) c := by
  obtain ⟨_, hzero⟩ := hN
  obtain ⟨hτD, _, habs⟩ := stopDepth_spec N.present a D
  set τ := stopDepth N.present a D with hτdef
  have hab := habs hlt
  obtain ⟨hcount, hc0⟩ := absent_count_zero hab
  have hl : (a.take (τ + 1)).length = τ + 1 := by simp; omega
  have hb : a.take (a.take (τ + 1)).length = a.take (τ + 1) ∧
      (a.take (τ + 1)).length ≤ τ + 1 ∧ (a.take (τ + 1)).length ≤ D :=
    ⟨opens_take a (τ + 1), by omega, by omega⟩
  have hcnt : (N.receive D a c).count (a.take (τ + 1)) = bump (fun _ => 0) c := by
    simp only [receive, ← hτdef]
    rw [if_pos hb, hc0]
  have hopen : (N.receive D a c).opening (a.take (τ + 1)) = bump (fun _ => 0) c := by
    simp [receive, ← hτdef, hlt, hzero _ hcount]
  refine ⟨hab, ?_, hcnt, hopen, ?_, ?_⟩
  · simp [present, hcnt, sum_bump]
  · rw [own, hcnt, hopen, div_self (ktMass_pos _).ne']
  · simp [receive, ← hτdef, hlt]

variable [Fintype Ltr]

/-- [proved-derived; formal-checked] **`convergence_step`: the arrival moves the root weight by the
stopped face.** For a standing with its invariant and an address of length at least `D`, the
arrival multiplies the root weight `convWeight w own pre D []` by the root face of the path stopped
at the deepest present node, over the nodes' KT faces and the stop weights `convLam`. -/
theorem convergence_step [Nonempty A] {w : ℕ → ℚ} (hw : StopLaw w) {N : Convergence Ltr A}
    (hN : N.Inv) {D : ℕ} {a : List Ltr} (hD : D ≤ a.length) (c : A) :
    convWeight w (N.receive D a c).own (N.receive D a c).pre D [] =
      convWeight w N.own N.pre D [] *
        pathFace (fun d => ktFace (N.count (a.take d))) (convLam w N.own N.pre D a)
          (stopDepth N.present a D) 0 c := by
  obtain ⟨hpre, hzero⟩ := hN
  obtain ⟨hτD, _, habs⟩ := stopDepth_spec N.present a D
  set τ := stopDepth N.present a D with hτdef
  have hEoff : ∀ s, ¬ (a.take s.length = s ∧ s.length ≤ τ) →
      (N.receive D a c).own s = N.own s := by
    intro s hs
    simp only [own, receive, ← hτdef]
    by_cases hb : a.take s.length = s ∧ s.length ≤ τ + 1 ∧ s.length ≤ D
    · -- the only such node off the stopped path is the absent child `a.take (τ + 1)`
      have hlen : s.length = τ + 1 := by
        by_contra hne
        exact hs ⟨hb.1, by omega⟩
      have hs' : s = a.take (τ + 1) := by rw [← hlen, hb.1]
      have hlt : τ < D := by omega
      have h0 := habs hlt
      rw [← hs'] at h0
      obtain ⟨hcount, hc0⟩ := absent_count_zero h0
      rw [if_pos hb, if_pos (show s = a.take (τ + 1) ∧ τ < D from ⟨hs', hlt⟩), hzero s hcount, hc0, ktMass_zero, div_one,
        div_self (ktMass_pos _).ne']
    · have hno : ¬ (s = a.take (τ + 1) ∧ τ < D) := by
        rintro ⟨rfl, hlt⟩
        apply hb
        have hl : (a.take (τ + 1)).length = τ + 1 := by simp; omega
        exact ⟨opens_take a (τ + 1), by omega, by omega⟩
      rw [if_neg hb, if_neg hno]
  have hEon : ∀ d ≤ τ, (N.receive D a c).own (a.take d) =
      N.own (a.take d) * ktFace (N.count (a.take d)) c := by
    intro d hd
    have hl : (a.take d).length = d := by simp; omega
    have hb : a.take (a.take d).length = a.take d ∧ (a.take d).length ≤ τ + 1 ∧
        (a.take d).length ≤ D := ⟨opens_take a d, by omega, by omega⟩
    have hno : ¬ (a.take d = a.take (τ + 1) ∧ τ < D) := fun h =>
      take_ne_of_length_ne (by have := h.2; simp only [List.length_take]; omega) h.1
    simp only [own, receive, ← hτdef]
    rw [if_pos hb, if_neg hno, ktMass_bump]
    ring
  have hRoff : ∀ s, ¬ (s = a.take (τ + 1) ∧ τ < D) → (N.receive D a c).pre s = N.pre s := by
    intro s hs
    simp only [receive, ← hτdef]
    rw [if_neg hs]
  have hRon : τ < D → (N.receive D a c).pre (a.take (τ + 1)) =
      N.pre (a.take (τ + 1)) * ktFace (N.count (a.take τ)) c := by
    intro hlt
    simp [receive, ← hτdef, hlt]
  have hstep := conv_weight_step hw (fun s => N.own_pos s) hpre hD hτD
    (fun d => ktFace (N.count (a.take d))) c hEoff hEon hRoff hRon 0 (Nat.zero_le _)
  rw [Nat.sub_zero, List.take_zero] at hstep
  exact hstep

/-- [definition] **The convergence tree's face after a past**: the root face of the path stopped at
the deepest present node, over the nodes' KT faces. -/
def convergenceFace (w : ℕ → ℚ) (D : ℕ) (ctx : List A → List Ltr) (h : List A) : A → ℚ :=
  pathFace (fun d => ktFace ((convergenceOf D ctx h).count ((ctx h).take d)))
    (convLam w (convergenceOf D ctx h).own (convergenceOf D ctx h).pre D (ctx h))
    (stopDepth (convergenceOf D ctx h).present (ctx h) D) 0

/-- [proved-derived; formal-checked] **`convergence_is_probability`: the convergence tree is a
probability law on words of each length.** For a causal context whose addresses reach depth `D`,
the root weight after a past is the product of the stopped faces its classes were read at (the
prequential code), each face is positive and normalized, and the root weights over all words of
length `n` sum to one. -/
theorem convergence_is_probability [Nonempty A] {w : ℕ → ℚ} (hw : StopLaw w) (D : ℕ)
    (ctx : List A → List Ltr) (hctx : ∀ h, D ≤ (ctx h).length) :
    (∀ h, convWeight w (convergenceOf D ctx h).own (convergenceOf D ctx h).pre D [] =
        prequentialCode (convergenceFace w D ctx) h) ∧
      (∀ h, (∀ c, 0 < convergenceFace w D ctx h c) ∧ ∑ c, convergenceFace w D ctx h c = 1) ∧
      ∀ n, wordSum n (fun h => convWeight w (convergenceOf D ctx h).own
        (convergenceOf D ctx h).pre D []) = 1 := by
  have hface : ∀ h, (∀ c, 0 < convergenceFace w D ctx h c) ∧
      ∑ c, convergenceFace w D ctx h c = 1 := fun h => by
    have hpre := (convergenceOf_inv D ctx hctx h).1
    exact stopped_face_normalized
      (fun d => ktFace ((convergenceOf D ctx h).count ((ctx h).take d)))
      (convLam w (convergenceOf D ctx h).own (convergenceOf D ctx h).pre D (ctx h))
      (stopDepth (convergenceOf D ctx h).present (ctx h) D)
      (fun d _ c => ktFace_pos _ c) (fun d _ => ktFace_sum _)
      (fun d _ => ⟨(convLam_mem hw (fun s => own_pos _ s) hpre D (ctx h) d).1.le,
        (convLam_mem hw (fun s => own_pos _ s) hpre D (ctx h) d).2.le⟩) 0 (Nat.zero_le _)
  have hcode : ∀ h, convWeight w (convergenceOf D ctx h).own (convergenceOf D ctx h).pre D [] =
      prequentialCode (convergenceFace w D ctx) h := by
    intro h
    induction h with
    | nil =>
      have hown : (unreached : Convergence Ltr A).own = fun _ => 1 := by
        funext s
        simp [own, unreached, ktMass_zero]
      simp only [convergenceOf, prequentialCode, hown]
      exact convWeight_unit w D [] (fun _ => rfl) fun _ _ => by simp [unreached]
    | cons c h ih =>
      simp only [convergenceOf, prequentialCode]
      rw [convergence_step hw (convergenceOf_inv D ctx hctx h) (hctx h) c, ih]
      rfl
  refine ⟨hcode, hface, fun n => ?_⟩
  rw [show (fun h => convWeight w (convergenceOf D ctx h).own (convergenceOf D ctx h).pre D []) =
      prequentialCode (convergenceFace w D ctx) from funext hcode]
  exact prequential_code_complete _ (fun h => (hface h).2) n

end Second

section Audit

#print axioms stopped_face_normalized
#print axioms prequential_code_complete
#print axioms stopping_rule_normalized
#print axioms convWeight_succ
#print axioms convWeight_pos
#print axioms convSplit_pos
#print axioms convLik_pos
#print axioms conv_mixture_over_trees
#print axioms conv_kraft_and_dominance
#print axioms convWeight_unit
#print axioms convWeight_first_arrival
#print axioms convLik_first_arrival
#print axioms convLam_mem
#print axioms convWeight_congr
#print axioms take_ne_of_length_ne
#print axioms conv_off
#print axioms conv_deep
#print axioms conv_weight_step
#print axioms conv_split_step
#print axioms conv_ratio_step
#print axioms stopDepth_spec
#print axioms stopDepth_all
#print axioms first_arrival_is_the_full_tree
#print axioms Convergence.unreached_inv
#print axioms Convergence.own_pos
#print axioms absent_count_zero
#print axioms receive_inv
#print axioms convergenceOf_inv
#print axioms second_arrival_opens_with_the_first_count
#print axioms convergence_step
#print axioms convergence_is_probability

end Audit

end Holonics.Compression.Landmark.Context.ConvergenceFounding
