import Holonics.HNN.ConvergenceFounding

/-!
# HNN.LandmarkCompaction: the tree is stored at the faces where paths part

[definition; agent-inferred] Decision 37 of the step 4 design (`docs/plans/THE_REBUILD.md`, "The
tree is stored at the faces where paths part"), rebuild step 4 (#73). Decision 28's prior needs no
late founding to save memory (Decision 36), because its unary chains are determined by their ends.
The computational object is the helical pair interaction; this owner is the receiving parametron's
landmark tree stored only where it is plural. Of the winding guide's six general objects it touches
two. The **tower thread**: context depth is a restriction chain; a node with one reached child is a
gluing that is unique, so it carries nothing but its rung into its chain's sum; a node where paths
part is a plural gluing and is kept. **Faces and placement**: the compacted face is the same
normalized receiving face, the prequential face of each dyadic digit's tree. The helix, the pair
(each kept edge still compares a node's face with its child's), the cell holonomy (a tree has no
two-cells) and the tube (the passage) stay attached, unchanged.

```text
routed     N_s(c) = Σ_b N_(s b)(c)  (|s| < D): every arrival runs to D (Boundary padding)
chain      s_0 … s_k, each s_i (i < k) with the one reached child s_(i+1):  N_(s_i) = N_(s_k), one E
           E − W(s_0) = ∏_(i ≤ k) (1 − w_i) · (E − X) ,  X = ∏_b W(s_k b) ;  1 − ρ_i = (1 − w_i)(1 − ρ_(i+1))
dyadic     w_i = 1 − 2^(−j_i) , j_i ≥ 0:  ∏_(i ≤ k) (1 − w_i) = 2^(−S) ,  S = Σ_(i ≤ k) j_i
           W(s_0) = ladder S · E + (1 − ladder S) X   (one node at the summed rung)
           β = ladder S · E/((1 − ladder S) X) = (2^S − 1) E/X ;  founding β₀ = 2^S − 1
forced     j_d = 0 , w_d = 0:  the node always splits (λ = 0) and passes its path face through
leaf       a chain ending at D:  W = E at every node (ρ = 1), one KT node
split      S = S_up + S_low:  β_ℓ = β (2^(S_low) − 1)/(2^S − 1) ,
           β_u = (2^(S_up) − 1) 2^(S_low) β_ℓ/((2^(S_low) − 1)(β_ℓ + 1)) ;  above a leaf β_u = 2^(S_up) − 1
           S_up = 0 (the upper part above the forced depths):  β_u = 0 , the face passes through,
           and the lower part keeps β
implicit   every node with exactly one reached child, the root included (a unary root is its chain's top)
kept       the parting nodes (at least two reached children) and the reached leaves at D;
           the root only while nothing has arrived
compacted  C(S, s) = E_s at D ;  C(S + j_d, s b) at an implicit node (one reached child b) ;
           ladder S′ E_s + (1 − ladder S′) ∏_(reached b) C(0, s b) at a kept node, S′ = S + j_d
           C(S, s) = (1 − 2^(−S)) E_s + 2^(−S) W(s) ,  so C(0, root) = W(root)
face       q = Λ k + (1 − Λ) q_below ,  Λ = ladder S′ E/(ladder S′ E + (1 − ladder S′) X) = β/(1 + β)
           at a kept node or where the address parts from a chain; the rung is carried at an implicit
           node the address follows; q_below = 1/|A| at an absent child
bound      #parting ≤ L − 1 ,  #kept ≤ 2L − 1 (L ≥ 1) ,  L ≤ n ,  #kept ≤ 2n − 1 (n ≥ 1) , 1 (n = 0)
```

[proved-derived; formal-checked] What is proved.

1. **Routing** (`Routed`, `reachedKids`, `routed_arrive`, `routed_standingOf`,
   `standingOf_root_total`, `routed_zero`, `routed_absent_one`, `routed_split`, `routed_unary`,
   `routed_split_unary`): an arrival whose address reaches the declared depth keeps every count above
   `D` continuing into exactly one child, so every passage from the empty standing is routed and its
   root holds one count an arrival. Under routing an unreached node has nothing reached below it and
   weighs one, the split is the product over the reached children, and a node with one reached child
   holds that child's counts and splits into its weight alone.
2. **The chain** (`chain_ratio`, `chain_ratio_dyadic`, `leaf_chain_is_one_node`): every node of a
   unary chain holds its bottom's counts (one KT mass `E`), and for any stop weights
   `E − W(s_0) = ∏_(i ≤ k) (1 − w_i) (E − X)`, also in the ratio `ρ = W/E`. On the dyadic ladder the
   product is `2^(−S)` with `S` the summed rung, so the chain with its bottom is Decision 28's node at
   rung `S`: `W = ladder S · E + (1 − ladder S) X`, founded at `2^S − 1` (`LandmarkTree.ladder_ratio`)
   with the ratio `β = (2^S − 1) E/X`, Decision 32's `β = w E/((1 − w) P)`, at every rung `j_d ≥ 0`
   (a forced depth has rung `0`). A chain that ends at the declared depth weighs `E` at every node
   under any stop weights.
3. **The split** (`chain_split`, `chain_split_pass`): cutting a summed rung `S = S_up + S_low` changes
   no weight; the lower part keeps `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`, the upper part holds the same
   counts at `β_u = (2^(S_up) − 1) 2^(S_low) β_ℓ/((2^(S_low) − 1)(β_ℓ + 1))`, and
   `β_u = 2^(S_up) − 1` above a leaf. An upper part with no rung (`S_up = 0`, above the forced depths)
   is a pass-through: it weighs its lower part, `β_u = 0` and `Λ = 0`, so its face is its lower
   part's, and the lower part keeps the chain's `β`. This is the chart an arrival that parts from a
   label at a chain's depth founds its node with.
4. **The compacted tree is Decision 28's tree, code for code** (`compactFrom`, `compactWeight`,
   `keptLam`, `compactFaceFrom`, `compactFace`, `compactFrom_eq`, `compact_weight_eq`,
   `follow_step_algebra`, `kept_step_algebra`, `compactFaceFrom_eq`, `compact_face_eq`,
   `stop_weight_prequential`, `compacted_is_decision_28`): the compacted weight reads a KT mass only
   at the kept nodes, each one node at the rung summed over its implicit chain, and it equals the stop
   law's weight (`LandmarkTree.stopWeight`, every node founded at its first arrival) at every routed
   standing. Its face is the path mixture over the kept nodes (with the split's `β_u` where the
   address parts from a chain, and the uniform prior at an absent child), and it equals the stop
   law's face (`LandmarkTree.stopFace`) at every arrival: over a passage from the empty standing the
   two prequential codes are equal exactly in `ℚ`, and each is the root weight. A root with one
   reached child is implicit like every other unary node: its rung joins its chain's sum. The rungs
   are any `j_d ≥ 0` (`LandmarkTree.ladder_stopLaw₀`): a forced depth has rung `0` and always splits.
5. **The kept nodes** (`partingNodes`, `leafNodes`, `keptNodes`, `mem_leafNodes`,
   `mem_partingNodes`, `nodes_of_zero`, `parting_card_le`, `leaf_card_le_total`,
   `compacted_node_bound`): the reached leaves are the reached nodes at depth `D`, the parting nodes
   are the nodes above `D` with at least two reached children, there is at most one parting node
   fewer than leaves, and the leaves are at most the arrivals. The kept nodes are the parting nodes
   and the leaves (the root is kept only while nothing has arrived, reading the prior), so `L ≥ 1`
   reached leaves keep at most `2L − 1` nodes, and a passage of `n ≥ 1` arrivals at most `2n − 1`
   nodes a tree, whatever the declared depth (one node, the root, when nothing has arrived).

[proved-standard] The compacted context tree is the storage of Willems's unbounded-depth
context-tree weighting (Willems, 1998); a rooted tree whose internal nodes have at least two
children has fewer internal nodes than leaves (the bound of Morrison's PATRICIA tree, 1968). The
proofs here are this owner's.

[conditional] The weight, face and code identities and the founding ratio hold for any rungs
`j_d ≥ 0`, the forced rung `0` included. The executed chart steps `β` on its lattice (`LandmarkTree`,
section 6′); its drift at a split, where `β_u` and `β_ℓ` are evaluated from the stored `β`, is the
lattice chart's passage-level drift owed in #62 ("the landmark lattice's drift"), not restated here.

The Rust consumer is `crates/holonics/src/hnn/landmark.rs` (`hnn::landmark::Storage::Compacted`):
the arena keeps the parting nodes and the leaves with their labels, each kept node with its counts,
its summed rung (`rung_sums`, a forced depth's rung `0`) and its `β`; the first arrival founds one
node, its leaf, whose chain runs from the root (a unary root folds into its chain); an arrival that
parts from a label at a chain's depth founds a node there with the label's counts and the
closed-form `β_u`, `β_ℓ` (`chain_split`, `Law::part`), and an upper part with no rung passes its
face through (`chain_split_pass`). Its test of exact equality with `IdealLandmarks` at the same `D`
(forced depths `0` and `1`) is the executed receipt of `compacted_is_decision_28`, and its node
counts (one node after one arrival, at most `2n − 1`) the receipt of `compacted_node_bound`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LandmarkCompaction

open Finset
open Holonics.HNN.LandmarkTree
open Holonics.HNN.ConvergenceFounding (prequentialCode)

/-! ## 1. Routed standings: every arrival runs to the declared depth -/

section Routed

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **A standing routed to the declared depth `D`**: every count at a node above `D`
continues to exactly one child, `N_s(c) = Σ_b N_(s b)(c)`. The addresses are padded with
`Boundary`, so every arrival runs to `D` and every standing its arrivals build is routed
(`routed_standingOf`). -/
def Routed (D : ℕ) (N : TreeStanding Ltr A) : Prop :=
  ∀ s : List Ltr, s.length < D → ∀ c, N s c = ∑ b, N (s ++ [b]) c

/-- [definition] **The reached children** of a node: the letters `b` whose child `s b` some arrival
has reached. -/
def reachedKids (N : TreeStanding Ltr A) (s : List Ltr) : Finset Ltr :=
  univ.filter fun b => N (s ++ [b]) ≠ fun _ => 0

omit [DecidableEq Ltr] [DecidableEq A] in
theorem mem_reachedKids {N : TreeStanding Ltr A} {s : List Ltr} {b : Ltr} :
    b ∈ reachedKids N s ↔ N (s ++ [b]) ≠ fun _ => 0 := by
  simp [reachedKids]

omit [DecidableEq Ltr] [Fintype A] [DecidableEq A] in
/-- The empty standing is routed to every depth. -/
theorem routed_empty (D : ℕ) : Routed D (emptyStanding : TreeStanding Ltr A) := by
  intro s _ c
  simp [emptyStanding]

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- Of the children of an opened node above the address's end, exactly the address's next letter is
opened. -/
theorem opens_child_iff {a s : List Ltr} (hs : a.take s.length = s) (hlt : s.length < a.length)
    (b : Ltr) : a.take (s ++ [b]).length = s ++ [b] ↔ b = a[s.length] := by
  have e : a.take (s.length + 1) = s ++ [a[s.length]] := by
    have := restrict_succ hlt
    unfold LandmarkTree.restrict at this
    rw [this, hs]
  simp only [List.length_append, List.length_singleton, e]
  constructor
  · intro h
    exact (List.singleton_inj.mp (List.append_cancel_left h)).symm
  · rintro rfl
    rfl

omit [Fintype A] in
/-- [proved-derived; formal-checked] **An arrival whose address runs to the declared depth keeps the
standing routed.** -/
theorem routed_arrive {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) {a : List Ltr}
    (ha : D ≤ a.length) (c : A) : Routed D (arrive N a c) := by
  intro s hs c'
  by_cases h : a.take s.length = s
  · have hlt : s.length < a.length := by omega
    have e : ∀ b, arrive N a c (s ++ [b]) c' =
        N (s ++ [b]) c' + if b = a[s.length] ∧ c' = c then 1 else 0 := by
      intro b
      by_cases hb : b = a[s.length]
      · rw [show arrive N a c (s ++ [b]) = bump (N (s ++ [b])) c from
          if_pos ((opens_child_iff h hlt b).mpr hb)]
        simp [bump, hb]
      · have hno : ¬ a.take (s ++ [b]).length = s ++ [b] := fun h' =>
          hb ((opens_child_iff h hlt b).mp h')
        rw [show arrive N a c (s ++ [b]) = N (s ++ [b]) from if_neg hno]
        simp [hb]
    simp only [e, Finset.sum_add_distrib]
    rw [← hN s hs c']
    simp only [arrive, if_pos h, bump]
    by_cases hc : c' = c
    · simp [hc]
    · simp [hc]
  · have e : ∀ b, arrive N a c (s ++ [b]) = N (s ++ [b]) := fun b =>
      if_neg (off_path_descendant h [b])
    rw [show arrive N a c s = N s from if_neg h,
      Finset.sum_congr rfl fun b _ => congrFun (e b) c']
    exact hN s hs c'

omit [Fintype A] in
/-- [proved-derived; formal-checked] **Every standing built by arrivals over addresses that run to
the declared depth is routed**: a causal context whose addresses reach `D`, from the empty
standing. -/
theorem routed_standingOf {D : ℕ} {ctx : List A → List Ltr} (hctx : ∀ h, D ≤ (ctx h).length) :
    ∀ h, Routed D (standingOf ctx h)
  | [] => routed_empty D
  | c :: h => routed_arrive (routed_standingOf hctx h) (hctx h) c

omit [Fintype Ltr] in
/-- The root of a passage holds one count per arrival. -/
theorem standingOf_root_total (ctx : List A → List Ltr) :
    ∀ h, ∑ c, standingOf ctx h [] c = h.length
  | [] => by simp [standingOf, emptyStanding]
  | c :: h => by
    have hroot : (ctx h).take ([] : List Ltr).length = [] := by simp
    simp only [standingOf, arrive, if_pos hroot]
    rw [sum_bump, standingOf_root_total ctx h, List.length_cons]

omit [DecidableEq Ltr] [Fintype A] [DecidableEq A] in
/-- Under routing, a node nothing has reached has nothing reached below it, to the declared depth. -/
theorem routed_zero {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ (t s : List Ltr), (s ++ t).length ≤ D → (N s = fun _ => 0) → N (s ++ t) = fun _ => 0
  | [], s, _, h => by simpa using h
  | b :: t, s, hl, h => by
    have hs : s.length < D := by simp at hl; omega
    have hb : N (s ++ [b]) = fun _ => 0 := by
      funext c
      have := hN s hs c
      simp only [h] at this
      exact (Finset.sum_eq_zero_iff.mp this.symm) b (mem_univ b)
    have := routed_zero hN t (s ++ [b]) (by simp at hl ⊢; omega) hb
    simpa using this

omit [DecidableEq Ltr] [DecidableEq A] in
/-- A node none of whose descendants to the depth `m` below it has been reached weighs one. -/
theorem stopWeight_one_of_zero (w : ℕ → ℚ) (N : TreeStanding Ltr A) :
    ∀ m s, (∀ t : List Ltr, t.length ≤ m → N (s ++ t) = fun _ => 0) → stopWeight w N m s = 1
  | 0, s, h => by
    have hs : N s = fun _ => 0 := by simpa using h [] (by simp)
    simp [stopWeight, hs, ktMass_zero]
  | m + 1, s, h => by
    have hs : N s = fun _ => 0 := by simpa using h [] (by simp)
    rw [stopWeight_succ, hs, ktMass_zero, stopSplit,
      Finset.prod_eq_one fun b _ => stopWeight_one_of_zero w N m _ fun t ht => by
        simpa using h (b :: t) (by simp; omega)]
    ring

omit [DecidableEq Ltr] [DecidableEq A] in
/-- Under routing, an absent child weighs one: it contributes `1` to its parent's split. -/
theorem routed_absent_one (w : ℕ → ℚ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) {m : ℕ}
    {s : List Ltr} (hsm : s.length + m = D) (h0 : N s = fun _ => 0) : stopWeight w N m s = 1 :=
  stopWeight_one_of_zero w N m s fun t ht =>
    routed_zero hN t s (by simp; omega) h0

omit [DecidableEq Ltr] [DecidableEq A] in
/-- Under routing, the split is the product over the reached children: absent children weigh one. -/
theorem routed_split (w : ℕ → ℚ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) {m : ℕ}
    {s : List Ltr} (hsm : s.length + m + 1 = D) (f : Ltr → ℚ)
    (hf : ∀ b ∈ reachedKids N s, f b = stopWeight w N m (s ++ [b])) :
    ∏ b ∈ reachedKids N s, f b = stopSplit w N m s := by
  rw [stopSplit, reachedKids, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs with hb
  · exact hf b (mem_reachedKids.mpr hb)
  · exact (routed_absent_one w hN (by simp; omega) (not_not.mp hb)).symm

omit [DecidableEq Ltr] [DecidableEq A] in
/-- Under routing, a node with a single reached child holds that child's counts: every arrival
that reached the node continued into it. -/
theorem routed_unary {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) {s : List Ltr}
    (hs : s.length < D) {b0 : Ltr} (h : ∀ b, (N (s ++ [b]) ≠ fun _ => 0) → b = b0) :
    N (s ++ [b0]) = N s := by
  funext c
  rw [hN s hs c, Finset.sum_eq_single b0]
  · intro b _ hb
    have hz : N (s ++ [b]) = fun _ => 0 := by
      by_contra h'
      exact hb (h b h')
    simp [hz]
  · simp

omit [DecidableEq Ltr] [DecidableEq A] in
/-- Under routing, a node with a single reached child splits into that child's weight alone. -/
theorem routed_split_unary (w : ℕ → ℚ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N)
    {m : ℕ} {s : List Ltr} (hsm : s.length + m + 1 = D) {b0 : Ltr}
    (h : ∀ b, (N (s ++ [b]) ≠ fun _ => 0) → b = b0) :
    stopSplit w N m s = stopWeight w N m (s ++ [b0]) := by
  rw [stopSplit, Finset.prod_eq_single b0]
  · intro b _ hb
    have hz : N (s ++ [b]) = fun _ => 0 := by
      by_contra h'
      exact hb (h b h')
    exact routed_absent_one w hN (by simp; omega) hz
  · simp

end Routed

/-! ## 2. A unary chain with its bottom is one node at the summed rung -/

section Chain

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- `1 − ladder j = 2^(−j)`. -/
theorem one_sub_ladder (j : ℕ) : 1 - ladder j = (1 / 2 : ℚ) ^ j := by
  unfold ladder
  ring

/-- Summing rungs composes the ladder: `ladder (S + j) = 1 − 2^(−S) (1 − ladder j)`. -/
theorem ladder_add (S j : ℕ) : ladder (S + j) = 1 - (1 / 2 : ℚ) ^ S * (1 - ladder j) := by
  unfold ladder
  rw [pow_add]
  ring

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`chain_ratio`: along a unary chain the weighting is an
exact shift.** Let `s` be a node at depth `d` with `m` levels below it and `t` a label with
`|t| < m`, such that every node `s_i = s ++ t.take i` (`i < |t|`) of the chain has no reached child
but `s_(i+1)` (the chain's label). Under routing every node of the chain holds the counts of its
bottom `s ++ t`, so one KT mass `E`; and for **any** stop weights `w`,
`E − W(s) = ∏_(i ≤ |t|) (1 − w_(d+i)) · (E − X)`, `X` the split of the bottom. In the ratio
`ρ = W/E`: `1 − ρ_top = ∏ (1 − w_i) (1 − X/E)` (the step `1 − ρ_i = (1 − w_i)(1 − ρ_(i+1))`
iterated). -/
theorem chain_ratio [Nonempty A] (w : ℕ → ℚ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ (t s : List Ltr) (m : ℕ), s.length + m = D → t.length < m →
      (∀ i (hi : i < t.length) b, (N (s ++ t.take i ++ [b]) ≠ fun _ => 0) → b = t[i]) →
      N (s ++ t) = N s ∧
      ktMass (N s) - stopWeight w N m s =
        (∏ i ∈ range (t.length + 1), (1 - w (s.length + i))) *
          (ktMass (N s) - stopSplit w N (m - t.length - 1) (s ++ t)) ∧
      1 - stopWeight w N m s / ktMass (N s) =
        (∏ i ∈ range (t.length + 1), (1 - w (s.length + i))) *
          (1 - stopSplit w N (m - t.length - 1) (s ++ t) / ktMass (N s)) := by
  have hdiv : ∀ {E W P X : ℚ}, 0 < E → E - W = P * (E - X) → 1 - W / E = P * (1 - X / E) := by
    intro E W P X hE h
    have hE' : E ≠ 0 := hE.ne'
    field_simp
    linarith
  intro t
  induction t with
  | nil =>
    intro s m hsm hm _
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have e : ktMass (N s) - stopWeight w N (m' + 1) s =
        (∏ i ∈ range (([] : List Ltr).length + 1), (1 - w (s.length + i))) *
          (ktMass (N s) - stopSplit w N (m' + 1 - ([] : List Ltr).length - 1) (s ++ [])) := by
      simp only [List.length_nil, zero_add, Finset.prod_range_one, add_zero, Nat.sub_zero,
        Nat.add_sub_cancel, List.append_nil, stopWeight_succ]
      ring
    exact ⟨by simp, e, hdiv (ktMass_pos _) e⟩
  | cons b t ih =>
    intro s m hsm hm hU
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    have hs : s.length < D := by omega
    have hU0 : ∀ b', (N (s ++ [b']) ≠ fun _ => 0) → b' = b := fun b' hb' => by
      have := hU 0 (by simp) b' (by simpa using hb')
      rwa [List.getElem_cons_zero] at this
    have hE : N (s ++ [b]) = N s := routed_unary hN hs hU0
    have hP : stopSplit w N m' s = stopWeight w N m' (s ++ [b]) :=
      routed_split_unary w hN (by omega) hU0
    obtain ⟨hN', hchain, -⟩ := ih (s ++ [b]) m' (by simp; omega) (by simp at hm; omega)
      fun i hi b' hb' => by
        have := hU (i + 1) (by simp; omega) b' (by simpa using hb')
        simpa using this
    have hlab : s ++ b :: t = s ++ [b] ++ t := by simp
    have hsub : m' + 1 - (b :: t).length - 1 = m' - t.length - 1 := by
      simp only [List.length_cons]; omega
    have hprod : ∏ i ∈ range ((b :: t).length + 1), (1 - w (s.length + i)) =
        (∏ i ∈ range (t.length + 1), (1 - w ((s ++ [b]).length + i))) * (1 - w s.length) := by
      rw [List.length_cons, Finset.prod_range_succ']
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [List.length_append, List.length_singleton]
      ring_nf
    have e : ktMass (N s) - stopWeight w N (m' + 1) s =
        (∏ i ∈ range ((b :: t).length + 1), (1 - w (s.length + i))) *
          (ktMass (N s) - stopSplit w N (m' + 1 - (b :: t).length - 1) (s ++ b :: t)) := by
      rw [hprod, hsub, hlab, stopWeight_succ, hP]
      rw [hE] at hchain
      rw [mul_comm (∏ i ∈ range (t.length + 1), (1 - w ((s ++ [b]).length + i))), mul_assoc,
        ← hchain]
      ring
    refine ⟨?_, e, hdiv (ktMass_pos _) e⟩
    rw [hlab, hN', hE]

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`chain_ratio_dyadic`: a chain with its bottom is ONE node at
the summed rung.** On the dyadic ladder `w_d = 1 − 2^(−j_d)` at any rungs `j_d ≥ 0` (a forced depth
has rung `0`), for a unary chain `s … s ++ t` (as in `chain_ratio`) with the summed rung
`S = Σ_(i ≤ |t|) j_(d+i)`:
* `∏_(i ≤ |t|) (1 − w_(d+i)) = 2^(−S)`;
* `W(s) = ladder S · E + (1 − ladder S) · X`, `X` the split of the bottom: Decision 28's node at
  rung `S` (`stopWeight_succ` with `w = ladder S`);
* its founding ratio is `ladder S/(1 − ladder S) = 2^S − 1` (`ladder_ratio`; `0` for a chain within
  the forced depths, which passes its face through), and its ratio is
  `β = ladder S · E/((1 − ladder S) X) = (2^S − 1) E/X`, Decision 32's `β = w E/((1 − w) P)`. -/
theorem chain_ratio_dyadic [Nonempty A] (j : ℕ → ℕ) {D : ℕ}
    {N : TreeStanding Ltr A} (hN : Routed D N) (t s : List Ltr) (m : ℕ) (hsm : s.length + m = D)
    (ht : t.length < m)
    (hU : ∀ i (hi : i < t.length) b, (N (s ++ t.take i ++ [b]) ≠ fun _ => 0) → b = t[i])
    (S : ℕ) (hS : ∑ i ∈ range (t.length + 1), j (s.length + i) = S) :
    ∏ i ∈ range (t.length + 1), (1 - ladder (j (s.length + i))) = (1 / 2 : ℚ) ^ S ∧
      stopWeight (fun d => ladder (j d)) N m s =
        ladder S * ktMass (N s) +
          (1 - ladder S) * stopSplit (fun d => ladder (j d)) N (m - t.length - 1) (s ++ t) ∧
      ladder S / (1 - ladder S) = 2 ^ S - 1 ∧
      ladder S * ktMass (N s) /
          ((1 - ladder S) * stopSplit (fun d => ladder (j d)) N (m - t.length - 1) (s ++ t)) =
        (2 ^ S - 1) * ktMass (N s) /
          stopSplit (fun d => ladder (j d)) N (m - t.length - 1) (s ++ t) := by
  have hprod : ∏ i ∈ range (t.length + 1), (1 - ladder (j (s.length + i))) = (1 / 2 : ℚ) ^ S := by
    simp only [one_sub_ladder, Finset.prod_pow_eq_pow_sum, hS]
  have hfound := ladder_ratio S
  obtain ⟨-, hchain, -⟩ := chain_ratio (fun d => ladder (j d)) hN t s m hsm ht hU
  have hW : stopWeight (fun d => ladder (j d)) N m s =
      ladder S * ktMass (N s) +
        (1 - ladder S) * stopSplit (fun d => ladder (j d)) N (m - t.length - 1) (s ++ t) := by
    rw [hprod] at hchain
    rw [one_sub_ladder, show ladder S = 1 - (1 / 2 : ℚ) ^ S from rfl]
    linarith
  refine ⟨hprod, hW, hfound, ?_⟩
  rw [mul_div_mul_comm, hfound, mul_div_assoc]

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`leaf_chain_is_one_node`: a chain that ends at the declared
depth reads as one KT node.** For a unary chain `s … s ++ t` whose bottom lies at depth `D`
(`|s| + |t| = D`, the leaf, `w = 1` there), under routing and **any** stop weights every node of the
chain weighs the chain's one KT mass: `W(s ++ t.take i) = E` for every `i ≤ |t|` (`ρ = 1`). -/
theorem leaf_chain_is_one_node (w : ℕ → ℚ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ (t s : List Ltr), s.length + t.length = D →
      (∀ i (hi : i < t.length) b, (N (s ++ t.take i ++ [b]) ≠ fun _ => 0) → b = t[i]) →
      N (s ++ t) = N s ∧
        ∀ i ≤ t.length, stopWeight w N (t.length - i) (s ++ t.take i) = ktMass (N s) := by
  intro t
  induction t with
  | nil =>
    intro s _ _
    refine ⟨by simp, fun i hi => ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    simp [stopWeight]
  | cons b t ih =>
    intro s hsD hU
    have hs : s.length < D := by simp at hsD; omega
    have hU0 : ∀ b', (N (s ++ [b']) ≠ fun _ => 0) → b' = b := fun b' hb' => by
      have := hU 0 (by simp) b' (by simpa using hb')
      rwa [List.getElem_cons_zero] at this
    have hE : N (s ++ [b]) = N s := routed_unary hN hs hU0
    have hP : stopSplit w N t.length s = stopWeight w N t.length (s ++ [b]) :=
      routed_split_unary w hN (by simp at hsD; omega) hU0
    obtain ⟨hN', hall⟩ := ih (s ++ [b]) (by simp at hsD ⊢; omega)
      fun i hi b' hb' => by
        have := hU (i + 1) (by simp; omega) b' (by simpa using hb')
        simpa using this
    rw [hE] at hall
    refine ⟨by rw [show s ++ b :: t = s ++ [b] ++ t by simp, hN', hE], fun i hi => ?_⟩
    rcases i with _ | i
    · have h0 := hall 0 (Nat.zero_le _)
      simp only [Nat.sub_zero, List.take_zero, List.append_nil] at h0
      simp only [List.length_cons, Nat.sub_zero, List.take_zero, List.append_nil, stopWeight_succ,
        hP, h0]
      ring
    · have := hall i (by simp at hi; omega)
      simpa [Nat.add_sub_add_right] using this

/-- [proved-derived; formal-checked] **`chain_split`: a split of a summed rung.** A chain at the
summed rung `S = S_up + S_low` over a bottom split `X`, with its one KT mass `E > 0`, cut at a depth
into an upper part (rung `S_up`) and a lower part (rung `S_low`, over the same `X`), both
`S_up, S_low ≥ 1`. With Decision 32's ratio `β = w E/((1 − w) P)` at each part's summed rung:
* the cut changes no weight: the upper part over the lower part's weight
  `W_low = ladder S_low · E + (1 − ladder S_low) X` is the whole chain;
* the lower part keeps its counts at `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`, `β` the chain's;
* the upper part holds the same counts at
  `β_u = ladder S_up · E/((1 − ladder S_up) W_low) = (2^(S_up) − 1) 2^(S_low) β_ℓ/((2^(S_low) − 1)(β_ℓ + 1))`;
* above a leaf (`W_low = E`, `leaf_chain_is_one_node`) it is `β_u = 2^(S_up) − 1`. -/
theorem chain_split {E X : ℚ} (hE : 0 < E) (hX : 0 < X) {Su Sl : ℕ} (hu : 1 ≤ Su) (hl : 1 ≤ Sl) :
    ladder Su * E + (1 - ladder Su) * (ladder Sl * E + (1 - ladder Sl) * X) =
        ladder (Su + Sl) * E + (1 - ladder (Su + Sl)) * X ∧
      ladder Sl * E / ((1 - ladder Sl) * X) =
        ladder (Su + Sl) * E / ((1 - ladder (Su + Sl)) * X) * (2 ^ Sl - 1) /
          (2 ^ (Su + Sl) - 1) ∧
      ladder Su * E / ((1 - ladder Su) * (ladder Sl * E + (1 - ladder Sl) * X)) =
        (2 ^ Su - 1) * 2 ^ Sl * (ladder Sl * E / ((1 - ladder Sl) * X)) /
          ((2 ^ Sl - 1) * (ladder Sl * E / ((1 - ladder Sl) * X) + 1)) ∧
      ladder Su * E / ((1 - ladder Su) * E) = 2 ^ Su - 1 := by
  have p2 : ∀ S : ℕ, (2 : ℚ) ^ S = 1 / (1 / 2) ^ S := fun S => by
    rw [one_div_pow, one_div_one_div]
  have hu0 : (0 : ℚ) < (1 / 2) ^ Su := by positivity
  have hl0 : (0 : ℚ) < (1 / 2) ^ Sl := by positivity
  have hl1 : (1 / 2 : ℚ) ^ Sl < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hu1 : (1 / 2 : ℚ) ^ Su < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  simp only [one_sub_ladder]
  simp only [ladder, p2, pow_add]
  generalize (1 / 2 : ℚ) ^ Su = u at hu0 hu1 ⊢
  generalize (1 / 2 : ℚ) ^ Sl = l at hl0 hl1 ⊢
  have hl' : (1 : ℚ) - l ≠ 0 := by linarith
  have hu' : (1 : ℚ) - u ≠ 0 := by linarith
  have hul : (1 : ℚ) - u * l ≠ 0 := by nlinarith
  have hlu : (1 : ℚ) - l * u ≠ 0 := by nlinarith
  have hW : (1 - l) * E + l * X ≠ 0 := by nlinarith
  refine ⟨by ring, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp

/-- [proved-derived; formal-checked] **`chain_split_pass`: a split whose upper part has no rung is a
pass-through.** Where the address parts from a chain within the forced depths, the upper part's
summed rung is `S_up = 0` (every depth it spans forced, `w = 0`):
* the cut changes no weight: the upper part weighs its lower part,
  `ladder 0 · E + (1 − ladder 0) W_low = W_low`, the whole chain at `S = 0 + S_low`;
* its ratio is `β_u = ladder 0 · E/((1 − ladder 0) W_low) = 0` and its posterior stop weight
  `Λ = 0`: its face is its lower part's, passed through;
* the lower part keeps the chain's summed rung, so it keeps the chain's `β`. -/
theorem chain_split_pass (E X : ℚ) (Sl : ℕ) :
    ladder 0 * E + (1 - ladder 0) * (ladder Sl * E + (1 - ladder Sl) * X) =
        ladder (0 + Sl) * E + (1 - ladder (0 + Sl)) * X ∧
      ladder 0 * E / ((1 - ladder 0) * (ladder Sl * E + (1 - ladder Sl) * X)) = 0 ∧
      ladder 0 * E / (ladder 0 * E + (1 - ladder 0) * (ladder Sl * E + (1 - ladder Sl) * X)) = 0 ∧
      ladder (0 + Sl) * E / ((1 - ladder (0 + Sl)) * X) = ladder Sl * E / ((1 - ladder Sl) * X) := by
  have h0 : ladder 0 = 0 := by simp [ladder]
  rw [zero_add, h0]
  exact ⟨by ring, by simp, by simp, rfl⟩

end Chain

/-! ## 3. The compacted tree: stored where paths part and at the leaves -/

section Compact

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The compacted tree's weight** of the chain entered at node `s` with `m` levels
below it, carrying the rung `S` summed over the implicit nodes of the chain above `s`:
* at the declared depth (`m = 0`), the leaf's KT mass (a chain that ends at `D` is one KT node,
  `leaf_chain_is_one_node`);
* at an **implicit** node (exactly one reached child: a unary chain's node, a gluing that is unique;
  the root included, so a unary root is its chain's top), its rung joins the chain's sum and the
  chain continues into its child; no mass is read there;
* at a **kept** node (a node where paths part, a plural gluing; or the root while nothing has
  arrived, which reads the prior), one Decision 28 node at the summed rung `S' = S + j_d`:
  `ladder S' · E + (1 − ladder S') ∏_(reached b) W_b`, each reached child's chain entered afresh
  (`S = 0`); an absent child contributes `1`. A forced depth has rung `j_d = 0`. -/
def compactFrom (j : ℕ → ℕ) (N : TreeStanding Ltr A) : ℕ → ℕ → List Ltr → ℚ
  | 0, _, s => ktMass (N s)
  | m + 1, S, s =>
    if (reachedKids N s).card = 1 then
      ∑ b ∈ reachedKids N s, compactFrom j N m (S + j s.length) (s ++ [b])
    else
      ladder (S + j s.length) * ktMass (N s) +
        (1 - ladder (S + j s.length)) * ∏ b ∈ reachedKids N s, compactFrom j N m 0 (s ++ [b])

/-- [definition] **The compacted tree's root weight** at the declared depth `D`. -/
def compactWeight (j : ℕ → ℕ) (N : TreeStanding Ltr A) (D : ℕ) : ℚ := compactFrom j N D 0 []

/-- [definition] **The posterior stop weight of a kept node** at the summed rung `S` with its KT
mass `E` and split `X`: `Λ = ladder S · E/(ladder S · E + (1 − ladder S) X) = β/(1 + β)`,
`β = ladder S · E/((1 − ladder S) X)`. -/
def keptLam (S : ℕ) (E X : ℚ) : ℚ := ladder S * E / (ladder S * E + (1 - ladder S) * X)

/-- [definition] **The compacted tree's face along the opened path** `a`, entered at depth `d` with
`m` levels below it and the rung `S` summed above:
* at the declared depth, the leaf's KT face;
* at an implicit node that the address follows, the chain continues with the rung carried;
* otherwise (a kept node, or an implicit node the address parts from: the chain is cut there, and
  its upper part is one node at the summed rung over the lower part's weight, `chain_split`) the
  mixture `Λ k + (1 − Λ) q_below`, `Λ = keptLam S' E X`, where `q_below` is the reached child's
  compacted face entered afresh, or the uniform prior `1/|A|` at an absent child. -/
def compactFaceFrom (j : ℕ → ℕ) (N : TreeStanding Ltr A) (a : List Ltr) :
    ℕ → ℕ → ℕ → A → ℚ
  | 0, _, d => ktFace (N (a.take d))
  | m + 1, S, d =>
    if (reachedKids N (a.take d)).card = 1 ∧ (N (a.take (d + 1)) ≠ fun _ => 0) then
      compactFaceFrom j N a m (S + j d) (d + 1)
    else fun c =>
      keptLam (S + j d) (ktMass (N (a.take d)))
          (∏ b ∈ reachedKids N (a.take d), compactFrom j N m 0 (a.take d ++ [b])) *
          ktFace (N (a.take d)) c +
        (1 - keptLam (S + j d) (ktMass (N (a.take d)))
          (∏ b ∈ reachedKids N (a.take d), compactFrom j N m 0 (a.take d ++ [b]))) *
          if N (a.take (d + 1)) ≠ (fun _ => 0) then compactFaceFrom j N a m 0 (d + 1) c
          else 1 / Fintype.card A

/-- [definition] **The compacted tree's root face** at the address `a`, depth `D`. -/
def compactFace (j : ℕ → ℕ) (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) : A → ℚ :=
  compactFaceFrom j N a D 0 0

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The chain entered at `s` with the rung `S` summed above it is
one node at that rung over Decision 28's weight at `s`**: under routing,
`compactFrom S s = (1 − 2^(−S)) E_s + 2^(−S) W(s)`, `W` the stop law's weight on the dyadic ladder
(`chain_ratio_dyadic` node by node). -/
theorem compactFrom_eq (j : ℕ → ℕ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ m S (s : List Ltr), s.length + m = D →
      compactFrom j N m S s =
        (1 - (1 / 2 : ℚ) ^ S) * ktMass (N s) +
          (1 / 2 : ℚ) ^ S * stopWeight (fun d => ladder (j d)) N m s
  | 0, S, s, _ => by simp only [compactFrom, stopWeight]; ring
  | m + 1, S, s, hsm => by
    have hs : s.length < D := by omega
    have hkid : ∀ b ∈ reachedKids N s,
        compactFrom j N m 0 (s ++ [b]) = stopWeight (fun d => ladder (j d)) N m (s ++ [b]) :=
      fun b _ => by
        rw [compactFrom_eq j hN m 0 (s ++ [b]) (by simp; omega)]
        simp
    rw [compactFrom, stopWeight_succ]
    split_ifs with himp
    · obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp himp
      have hU : ∀ b, (N (s ++ [b]) ≠ fun _ => 0) → b = b0 := fun b hb => by
        have hmem : b ∈ reachedKids N s := mem_reachedKids.mpr hb
        rw [hb0] at hmem
        exact Finset.mem_singleton.mp hmem
      rw [hb0, Finset.sum_singleton, compactFrom_eq j hN m _ (s ++ [b0]) (by simp; omega),
        routed_unary hN hs hU, routed_split_unary _ hN (by omega) hU]
      simp only [ladder, pow_add]
      ring
    · rw [routed_split _ hN (by omega) _ hkid]
      simp only [ladder, pow_add]
      ring

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The compacted weight is Decision 28's weight** at the root,
for every routed standing, on the dyadic ladder `w_d = 1 − 2^(−j_d)`. -/
theorem compact_weight_eq (j : ℕ → ℕ) {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    compactWeight j N D = stopWeight (fun d => ladder (j d)) N D [] := by
  rw [compactWeight, compactFrom_eq j hN D 0 [] (by simp)]
  simp

/-- The mixture at an implicit node the address follows: carrying the node's rung down the chain
is the node's own mixture (the algebra of `compactFaceFrom_eq`'s chain step). -/
theorem follow_step_algebra {E k W q F h : ℚ} (hE : 0 < E) (hW : 0 < W) (hh0 : 0 < h)
    (hh1 : h ≤ 1) :
    ((1 - F * h) * E * k + F * h * W * q) / ((1 - F * h) * E + F * h * W) =
      ((1 - F) * E * k + F * ((1 - h) * E + h * W) *
          ((1 - h) * E / ((1 - h) * E + h * W) * k +
            (1 - (1 - h) * E / ((1 - h) * E + h * W)) * q)) /
        ((1 - F) * E + F * ((1 - h) * E + h * W)) := by
  have hV : (1 - h) * E + h * W ≠ 0 := by
    have := mul_nonneg (sub_nonneg.mpr hh1) hE.le
    have := mul_pos hh0 hW
    linarith
  have key : ((1 - h) * E + h * W) *
      ((1 - h) * E / ((1 - h) * E + h * W) * k +
        (1 - (1 - h) * E / ((1 - h) * E + h * W)) * q) = (1 - h) * E * k + h * W * q := by
    field_simp
    ring
  rw [mul_assoc F ((1 - h) * E + h * W), key]
  congr 1 <;> ring

/-- The mixture at a kept node (or where the address parts from a chain): one node at the summed
rung `S + j` is the node's own mixture under the rung `S` carried from above. -/
theorem kept_step_algebra {E k P q F h : ℚ} (hE : 0 < E) (hP : 0 < P) (hF0 : 0 < F)
    (hF1 : F ≤ 1) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    (1 - F * h) * E / ((1 - F * h) * E + F * h * P) * k +
        (1 - (1 - F * h) * E / ((1 - F * h) * E + F * h * P)) * q =
      ((1 - F) * E * k + F * ((1 - h) * E + h * P) *
          ((1 - h) * E / ((1 - h) * E + h * P) * k +
            (1 - (1 - h) * E / ((1 - h) * E + h * P)) * q)) /
        ((1 - F) * E + F * ((1 - h) * E + h * P)) := by
  rw [← follow_step_algebra hE hP hh0 hh1]
  have hU : (1 - F * h) * E + F * h * P ≠ 0 := by
    have := mul_nonneg (sub_nonneg.mpr (mul_le_one₀ hF1 hh0.le hh1)) hE.le
    have := mul_pos (mul_pos hF0 hh0) hP
    linarith
  field_simp
  ring

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The compacted face is Decision 28's face, node for node.**
Under routing, for an address reaching the declared depth and any rungs `j_d ≥ 0`, the compacted
path mixture entered at depth `d` with the rung `S` summed above is the chain's one-node mixture over
the tree's own quantities: `((1 − 2^(−S)) E k + 2^(−S) W q)/((1 − 2^(−S)) E + 2^(−S) W)`, `k`, `W`,
`q` the KT face, the weight and the path face of the stop law at that node. -/
theorem compactFaceFrom_eq [Nonempty A] (j : ℕ → ℕ) {D : ℕ}
    {N : TreeStanding Ltr A} (hN : Routed D N) {a : List Ltr} (ha : D ≤ a.length) (c : A) :
    ∀ m S d, d + m = D →
      compactFaceFrom j N a m S d c =
        ((1 - (1 / 2 : ℚ) ^ S) * ktMass (N (a.take d)) * kAt N a d c +
            (1 / 2 : ℚ) ^ S * stopWeight (fun d => ladder (j d)) N m (a.take d) *
              stopFace (fun d => ladder (j d)) N D a d c) /
          ((1 - (1 / 2 : ℚ) ^ S) * ktMass (N (a.take d)) +
            (1 / 2 : ℚ) ^ S * stopWeight (fun d => ladder (j d)) N m (a.take d)) := by
  have hw := ladder_stopLaw₀ j
  intro m
  induction m with
  | zero =>
    intro S d hd
    obtain rfl : d = D := by omega
    have hE := ktMass_pos (N (a.take d))
    have hF0 : (0 : ℚ) < (1 / 2) ^ S := by positivity
    have hF1 : (1 / 2 : ℚ) ^ S ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [stopFace, pathFace_deepest]
    simp only [compactFaceFrom, stopWeight, kAt]
    have hden : (1 - (1 / 2 : ℚ) ^ S) * ktMass (N (a.take d)) +
        (1 / 2 : ℚ) ^ S * ktMass (N (a.take d)) = ktMass (N (a.take d)) := by ring
    rw [show (1 - (1 / 2 : ℚ) ^ S) * ktMass (N (a.take d)) * ktFace (N (a.take d)) c +
        (1 / 2 : ℚ) ^ S * ktMass (N (a.take d)) * ktFace (N (a.take d)) c =
        ktMass (N (a.take d)) * ktFace (N (a.take d)) c by ring, hden,
      mul_div_cancel_left₀ _ hE.ne']
  | succ m ih =>
    intro S d hd
    have hdD : d < D := by omega
    have hda : d < a.length := by omega
    have hlen : (a.take d).length = d := by simp; omega
    have htake : a.take (d + 1) = a.take d ++ [a[d]] := by
      have := restrict_succ hda
      unfold LandmarkTree.restrict at this
      exact this
    have hW : stopWeight (fun d => ladder (j d)) N (m + 1) (a.take d) =
        ladder (j d) * ktMass (N (a.take d)) +
          (1 - ladder (j d)) * stopSplit (fun d => ladder (j d)) N m (a.take d) := by
      rw [stopWeight_succ, hlen]
    have hq : stopFace (fun d => ladder (j d)) N D a d c =
        stopLam (fun d => ladder (j d)) N D a d * kAt N a d c +
          (1 - stopLam (fun d => ladder (j d)) N D a d) *
            stopFace (fun d => ladder (j d)) N D a (d + 1) c :=
      pathFace_step _ _ hdD c
    have hlam : stopLam (fun d => ladder (j d)) N D a d =
        ladder (j d) * ktMass (N (a.take d)) /
          (ladder (j d) * ktMass (N (a.take d)) +
            (1 - ladder (j d)) * stopSplit (fun d => ladder (j d)) N m (a.take d)) := by
      unfold stopLam
      rw [show D - d - 1 = m by omega]
    have hF0 : (0 : ℚ) < (1 / 2) ^ S := by positivity
    have hF1 : (1 / 2 : ℚ) ^ S ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hh0 : (0 : ℚ) < (1 / 2) ^ (j d) := by positivity
    have hh1 : (1 / 2 : ℚ) ^ (j d) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hE := ktMass_pos (N (a.take d))
    rw [hW, hq, hlam]
    by_cases hcond : (reachedKids N (a.take d)).card = 1 ∧ (N (a.take (d + 1)) ≠ fun _ => 0)
    · -- the address follows an implicit node: the rung is carried down the chain
      rw [compactFaceFrom, if_pos hcond, ih (S + j d) (d + 1) (by omega)]
      obtain ⟨b0, hb0⟩ := Finset.card_eq_one.mp hcond.1
      have hmem : a[d] ∈ reachedKids N (a.take d) := mem_reachedKids.mpr (by
        rw [← htake]; exact hcond.2)
      have hU : ∀ b, (N (a.take d ++ [b]) ≠ fun _ => 0) → b = a[d] := fun b hb => by
        have hb' : b ∈ reachedKids N (a.take d) := mem_reachedKids.mpr hb
        rw [hb0] at hb' hmem
        rw [Finset.mem_singleton.mp hb', Finset.mem_singleton.mp hmem]
      have hE' : N (a.take (d + 1)) = N (a.take d) := by
        rw [htake]
        exact routed_unary hN (by omega) hU
      have hP : stopSplit (fun d => ladder (j d)) N m (a.take d) =
          stopWeight (fun d => ladder (j d)) N m (a.take (d + 1)) := by
        rw [htake]
        exact routed_split_unary _ hN (by omega) hU
      have hk : kAt N a (d + 1) c = kAt N a d c := by
        unfold kAt
        rw [hE']
      have hWt := stopWeight_pos₀ hw N m (a.take (d + 1))
      rw [hE', hk, hP]
      generalize stopWeight (fun d => ladder (j d)) N m (a.take (d + 1)) = W at hWt ⊢
      generalize stopFace (fun d => ladder (j d)) N D a (d + 1) c = q
      generalize kAt N a d c = k
      generalize ktMass (N (a.take d)) = E at hE ⊢
      simp only [one_sub_ladder]
      simp only [ladder, pow_add]
      exact follow_step_algebra hE hWt hh0 hh1
    · -- a kept node, or the address parts from a chain here
      rw [compactFaceFrom, if_neg hcond]
      have hX : ∏ b ∈ reachedKids N (a.take d), compactFrom j N m 0 (a.take d ++ [b]) =
          stopSplit (fun d => ladder (j d)) N m (a.take d) := by
        refine routed_split _ hN (by omega) _ fun b _ => ?_
        rw [compactFrom_eq j hN m 0 _ (by simp; omega)]
        simp
      have hbelow : (if N (a.take (d + 1)) ≠ (fun _ => 0) then
            compactFaceFrom j N a m 0 (d + 1) c else 1 / Fintype.card A) =
          stopFace (fun d => ladder (j d)) N D a (d + 1) c := by
        by_cases hk : N (a.take (d + 1)) = fun _ => 0
        · rw [if_neg (not_not.mpr hk)]
          symm
          refine pathFace_const _ _ D c _ (d + 1) (by omega) fun d' h1 h2 => ?_
          have e : a.take d' = a.take (d + 1) ++ (a.drop (d + 1)).take (d' - (d + 1)) := by
            rw [← List.take_add, show d + 1 + (d' - (d + 1)) = d' by omega]
          have hz : N (a.take d') = fun _ => 0 := by
            rw [e]
            exact routed_zero hN _ _ (by simp; omega) hk
          simp only [kAt, hz, ktFace_zero]
        · rw [if_pos hk, ih 0 (d + 1) (by omega)]
          have hWt := stopWeight_pos₀ hw N m (a.take (d + 1))
          simp only [pow_zero, sub_self, zero_mul, one_mul, zero_add]
          field_simp
      have hPpos := stopSplit_pos₀ hw N m (a.take d)
      rw [hX, hbelow]
      unfold keptLam
      generalize stopSplit (fun d => ladder (j d)) N m (a.take d) = P at hPpos ⊢
      generalize stopFace (fun d => ladder (j d)) N D a (d + 1) c = q
      rw [show ktFace (N (a.take d)) c = kAt N a d c from rfl]
      generalize kAt N a d c = k
      generalize ktMass (N (a.take d)) = E at hE ⊢
      simp only [one_sub_ladder]
      simp only [ladder, pow_add]
      exact kept_step_algebra hE hPpos hF0 hF1 hh0 hh1

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **The compacted root face is Decision 28's root face**, for
every routed standing, every address reaching the declared depth and any rungs `j_d ≥ 0`. -/
theorem compact_face_eq [Nonempty A] (j : ℕ → ℕ) {D : ℕ}
    {N : TreeStanding Ltr A} (hN : Routed D N) {a : List Ltr} (ha : D ≤ a.length) (c : A) :
    compactFace j N D a c = stopFace (fun d => ladder (j d)) N D a 0 c := by
  have hW := stopWeight_pos₀ (ladder_stopLaw₀ j) N D (a.take 0)
  rw [compactFace, compactFaceFrom_eq j hN ha c D 0 0 (by simp)]
  simp only [pow_zero, sub_self, zero_mul, one_mul, zero_add]
  field_simp

/-- [proved-derived; formal-checked] The stop law's root weight after a past is the prequential
code of its root faces (`stop_weight_step₀` at the root, from the empty standing's weight one), under
any law with forced depths. -/
theorem stop_weight_prequential [Nonempty A] {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (ctx : List A → List Ltr) (hctx : ∀ h, D ≤ (ctx h).length) :
    ∀ h, stopWeight w (standingOf ctx h) D [] =
      prequentialCode (fun h => stopFace w (standingOf ctx h) D (ctx h) 0) h
  | [] => by
    simp only [standingOf, prequentialCode]
    exact stop_unfounded w _ D [] fun _ => rfl
  | c :: h => by
    simp only [standingOf, prequentialCode]
    have hstep := stop_weight_step₀ hw (standingOf ctx h) (hctx h) c 0 (Nat.zero_le _)
    simp only [Nat.sub_zero, List.take_zero] at hstep
    rw [hstep, stop_weight_prequential hw D ctx hctx h]

/-- [proved-derived; formal-checked] **`compacted_is_decision_28`: the compacted tree is Decision
28's tree at the declared depth, code for code, exactly in `ℚ`.** On the dyadic ladder
`w_d = 1 − 2^(−j_d)` at any rungs `j_d ≥ 0` (a forced depth has rung `0`, `w = 0`, and always
splits), for every passage built by arrivals from the empty standing over addresses reaching the
declared depth `D` (a causal context, `standingOf`):
* **the weight**: the compacted root weight (the nodes where paths part and the leaves, each kept
  node one node at the rung summed over its implicit chain, a unary root folded into its chain) is
  the stop law's root weight `stopWeight` (every node founded at its first arrival);
* **the face**: the compacted path mixture over the kept nodes, read at each arrival before its
  deposit, is the stop law's root face `stopFace`, the prequential face of that arrival; it is
  positive and normalized;
* **the code**: the compacted root weight is the prequential code of its faces, and that code is the
  stop law's prequential code, so the two prequential code lengths `−log₂` are equal exactly. -/
theorem compacted_is_decision_28 [Nonempty A] (j : ℕ → ℕ) (D : ℕ)
    (ctx : List A → List Ltr) (hctx : ∀ h, D ≤ (ctx h).length) :
    (∀ h, compactWeight j (standingOf ctx h) D =
        stopWeight (fun d => ladder (j d)) (standingOf ctx h) D []) ∧
      (∀ h c, compactFace j (standingOf ctx h) D (ctx h) c =
        stopFace (fun d => ladder (j d)) (standingOf ctx h) D (ctx h) 0 c) ∧
      (∀ h, (∀ c, 0 < compactFace j (standingOf ctx h) D (ctx h) c) ∧
        ∑ c, compactFace j (standingOf ctx h) D (ctx h) c = 1) ∧
      ∀ h, compactWeight j (standingOf ctx h) D =
          prequentialCode (fun h => compactFace j (standingOf ctx h) D (ctx h)) h ∧
        prequentialCode (fun h => compactFace j (standingOf ctx h) D (ctx h)) h =
          prequentialCode
            (fun h => stopFace (fun d => ladder (j d)) (standingOf ctx h) D (ctx h) 0) h := by
  have hw := ladder_stopLaw₀ j
  have hR := routed_standingOf hctx
  have hweight : ∀ h, compactWeight j (standingOf ctx h) D =
      stopWeight (fun d => ladder (j d)) (standingOf ctx h) D [] := fun h =>
    compact_weight_eq j (hR h)
  have hface : ∀ h c, compactFace j (standingOf ctx h) D (ctx h) c =
      stopFace (fun d => ladder (j d)) (standingOf ctx h) D (ctx h) 0 c := fun h c =>
    compact_face_eq j (hR h) (hctx h) c
  have hfun : (fun h => compactFace j (standingOf ctx h) D (ctx h)) =
      fun h => stopFace (fun d => ladder (j d)) (standingOf ctx h) D (ctx h) 0 :=
    funext fun h => funext fun c => hface h c
  refine ⟨hweight, hface, fun h => ?_, fun h => ?_⟩
  · have hn := stopFace_normalized₀ hw (standingOf ctx h) D (ctx h) 0 (Nat.zero_le _)
    simp only [hface]
    exact hn
  · rw [hfun, hweight, stop_weight_prequential hw D ctx hctx h]
    exact ⟨rfl, rfl⟩

end Compact

/-! ## 4. The kept nodes: at most `2n − 1` over `n ≥ 1` arrivals -/

section Nodes

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The parting nodes** below `s` (`m` levels): the nodes above the declared depth,
on reached paths, with at least two reached children: where paths part (a plural gluing). -/
def partingNodes (N : TreeStanding Ltr A) : ℕ → List Ltr → Finset (List Ltr)
  | 0, _ => ∅
  | m + 1, s => (if 2 ≤ (reachedKids N s).card then {s} else ∅) ∪
      (reachedKids N s).biUnion fun b => partingNodes N m (s ++ [b])

/-- [definition] **The reached leaves** below `s` (`m` levels): the reached nodes at the declared
depth. -/
def leafNodes (N : TreeStanding Ltr A) : ℕ → List Ltr → Finset (List Ltr)
  | 0, s => if N s ≠ (fun _ => 0) then {s} else ∅
  | m + 1, s => (reachedKids N s).biUnion fun b => leafNodes N m (s ++ [b])

/-- [definition] **The kept nodes** of the compacted tree at the declared depth `D`: the parting
nodes and the reached leaves, and the root only while nothing has arrived (it reads the prior).
Every other reached node is implicit, the root included: one reached child, its counts its child's
(`routed_unary`), its rung carried in its chain's sum. -/
def keptNodes (N : TreeStanding Ltr A) (D : ℕ) : Finset (List Ltr) :=
  if N [] = (fun _ => 0) then {[]} else partingNodes N D [] ∪ leafNodes N D []

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- A node's one-letter extension along a longer word it prefixes is that word's restriction. -/
theorem prefix_step {s t : List Ltr} (hp : s <+: t) (hlt : s.length < t.length) :
    s ++ [t[s.length]] = t.take (s.length + 1) := by
  have e := restrict_succ hlt
  unfold LandmarkTree.restrict at e
  rw [e, ← List.prefix_iff_eq_take.mp hp]

omit [DecidableEq A] in
theorem leafNodes_prefix (N : TreeStanding Ltr A) :
    ∀ m (s t : List Ltr), t ∈ leafNodes N m s → s <+: t
  | 0, s, t, h => by
    simp only [leafNodes] at h
    split_ifs at h
    · obtain rfl := Finset.mem_singleton.mp h
      exact List.prefix_refl _
    · simp at h
  | m + 1, s, t, h => by
    simp only [leafNodes, Finset.mem_biUnion] at h
    obtain ⟨b, _, hb⟩ := h
    exact (List.prefix_append s [b]).trans (leafNodes_prefix N m _ t hb)

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- Families of nodes below distinct children are disjoint. -/
theorem kids_disjoint {s : List Ltr} {F : Ltr → Finset (List Ltr)}
    (hF : ∀ b t, t ∈ F b → s ++ [b] <+: t) {b b' : Ltr} (hbb : b ≠ b') : Disjoint (F b) (F b') := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  have e1 := List.prefix_iff_eq_take.mp (hF b t ht)
  have e2 := List.prefix_iff_eq_take.mp (hF b' t ht')
  simp only [List.length_append, List.length_singleton] at e1 e2
  rw [← e2] at e1
  exact hbb (List.singleton_inj.mp (List.append_cancel_left e1))

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **The reached leaves are the reached nodes at the declared
depth** (under routing). -/
theorem mem_leafNodes {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ m (s : List Ltr), s.length + m = D → ∀ t,
      t ∈ leafNodes N m s ↔ s <+: t ∧ t.length = D ∧ N t ≠ fun _ => 0
  | 0, s, hsm, t => by
    simp only [leafNodes]
    split_ifs with h0
    · rw [Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨List.prefix_refl _, by omega, h0⟩
      · rintro ⟨hp, hl, _⟩
        exact (hp.eq_of_length (by omega)).symm
    · simp only [Finset.notMem_empty, false_iff]
      rintro ⟨hp, hl, ht⟩
      rw [← hp.eq_of_length (by omega)] at ht
      exact ht (not_not.mp h0)
  | m + 1, s, hsm, t => by
    simp only [leafNodes, Finset.mem_biUnion, mem_reachedKids]
    constructor
    · rintro ⟨b, _, hb⟩
      obtain ⟨hp, hl, ht⟩ := (mem_leafNodes hN m (s ++ [b]) (by simp; omega) t).mp hb
      exact ⟨(List.prefix_append s [b]).trans hp, hl, ht⟩
    · rintro ⟨hp, hl, ht⟩
      have hlt : s.length < t.length := by omega
      refine ⟨t[s.length], ?_, (mem_leafNodes hN m _ (by simp; omega) t).mpr
        ⟨by rw [prefix_step hp hlt]; exact List.take_prefix _ _, hl, ht⟩⟩
      intro h0
      apply ht
      have e : t = (s ++ [t[s.length]]) ++ t.drop (s.length + 1) := by
        rw [prefix_step hp hlt, List.take_append_drop]
      rw [e]
      exact routed_zero hN _ _ (by rw [← e]; omega) h0

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **The parting nodes are the nodes above the declared depth with
at least two reached children** (under routing). -/
theorem mem_partingNodes {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ m (s : List Ltr), s.length + m = D → ∀ t,
      t ∈ partingNodes N m s ↔ s <+: t ∧ t.length < D ∧ 2 ≤ (reachedKids N t).card
  | 0, s, hsm, t => by
    simp only [partingNodes, Finset.notMem_empty, false_iff]
    rintro ⟨hp, hl, _⟩
    have := hp.length_le
    omega
  | m + 1, s, hsm, t => by
    simp only [partingNodes, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨b, _, hb⟩)
      · split_ifs at h with h2
        · obtain rfl := Finset.mem_singleton.mp h
          exact ⟨List.prefix_refl _, by omega, h2⟩
        · simp at h
      · obtain ⟨hp, hl, h2⟩ := (mem_partingNodes hN m (s ++ [b]) (by simp; omega) t).mp hb
        exact ⟨(List.prefix_append s [b]).trans hp, hl, h2⟩
    · rintro ⟨hp, hl, h2⟩
      by_cases hts : t = s
      · subst hts
        left
        simp [h2]
      · right
        have hlt : s.length < t.length :=
          lt_of_le_of_ne hp.length_le fun h => hts (hp.eq_of_length h).symm
        refine ⟨t[s.length], mem_reachedKids.mpr ?_, (mem_partingNodes hN m _ (by simp; omega) t).mpr
          ⟨by rw [prefix_step hp hlt]; exact List.take_prefix _ _, hl, h2⟩⟩
        intro h0
        obtain ⟨b', hb'⟩ := Finset.card_pos.mp (by omega : 0 < (reachedKids N t).card)
        apply mem_reachedKids.mp hb'
        have e : t ++ [b'] = (s ++ [t[s.length]]) ++ (t.drop (s.length + 1) ++ [b']) := by
          rw [prefix_step hp hlt, ← List.append_assoc, List.take_append_drop]
        rw [e]
        exact routed_zero hN _ _ (by rw [← e]; simp; omega) h0

omit [DecidableEq A] in
/-- Under routing, nothing below an unreached node is kept. -/
theorem nodes_of_zero {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) {m : ℕ} {s : List Ltr}
    (hsm : s.length + m = D) (h0 : N s = fun _ => 0) :
    partingNodes N m s = ∅ ∧ leafNodes N m s = ∅ := by
  cases m with
  | zero => simp [partingNodes, leafNodes, h0]
  | succ m =>
    have hR : reachedKids N s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro b hb
      exact mem_reachedKids.mp hb (routed_zero hN [b] s (by simp; omega) h0)
    simp [partingNodes, leafNodes, hR]

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **A reached subtree has fewer parting nodes than reached
leaves**: `#parting + 1 ≤ #leaves` (each parting node has at least two reached children, and every
reached node above the declared depth has at least one, under routing). -/
theorem parting_card_le {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ m (s : List Ltr), s.length + m = D → (N s ≠ fun _ => 0) →
      (partingNodes N m s).card + 1 ≤ (leafNodes N m s).card
  | 0, s, _, h0 => by simp [partingNodes, leafNodes, h0]
  | m + 1, s, hsm, h0 => by
    have hs : s.length < D := by omega
    have hr : 1 ≤ (reachedKids N s).card := by
      obtain ⟨c, hc⟩ : ∃ c, N s c ≠ 0 := by
        by_contra hne
        exact h0 (funext fun c => not_not.mp (not_exists.mp hne c))
      rw [hN s hs c] at hc
      obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      exact Finset.card_pos.mpr ⟨b, mem_reachedKids.mpr fun h' => hb (congrFun h' c)⟩
    have hL : (leafNodes N (m + 1) s).card =
        ∑ b ∈ reachedKids N s, (leafNodes N m (s ++ [b])).card := by
      rw [leafNodes]
      exact Finset.card_biUnion fun b _ b' _ hbb =>
        kids_disjoint (fun b t ht => leafNodes_prefix N m _ t ht) hbb
    have hP : (partingNodes N (m + 1) s).card ≤
        (if 2 ≤ (reachedKids N s).card then 1 else 0) +
          ∑ b ∈ reachedKids N s, (partingNodes N m (s ++ [b])).card := by
      rw [partingNodes]
      refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_biUnion_le)
      split_ifs <;> simp
    have hIH : ∑ b ∈ reachedKids N s, ((partingNodes N m (s ++ [b])).card + 1) ≤
        ∑ b ∈ reachedKids N s, (leafNodes N m (s ++ [b])).card :=
      Finset.sum_le_sum fun b hb =>
        parting_card_le hN m (s ++ [b]) (by simp; omega) (mem_reachedKids.mp hb)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hIH
    rw [hL]
    split_ifs at hP <;> omega

omit [DecidableEq A] in
/-- Under routing, the reached leaves below a node are at most its arrivals. -/
theorem leaf_card_le_total {D : ℕ} {N : TreeStanding Ltr A} (hN : Routed D N) :
    ∀ m (s : List Ltr), s.length + m = D → (leafNodes N m s).card ≤ ∑ c, N s c
  | 0, s, _ => by
    simp only [leafNodes]
    split_ifs with h0
    · obtain ⟨c, hc⟩ : ∃ c, N s c ≠ 0 := by
        by_contra hne
        exact h0 (funext fun c => not_not.mp (not_exists.mp hne c))
      rw [Finset.card_singleton]
      exact (Nat.one_le_iff_ne_zero.mpr hc).trans
        (Finset.single_le_sum (fun c _ => Nat.zero_le _) (mem_univ c))
    · simp
  | m + 1, s, hsm => by
    have hs : s.length < D := by omega
    rw [leafNodes]
    calc ((reachedKids N s).biUnion fun b => leafNodes N m (s ++ [b])).card
        ≤ ∑ b ∈ reachedKids N s, (leafNodes N m (s ++ [b])).card := Finset.card_biUnion_le
      _ ≤ ∑ b ∈ reachedKids N s, ∑ c, N (s ++ [b]) c :=
          Finset.sum_le_sum fun b _ => leaf_card_le_total hN m (s ++ [b]) (by simp; omega)
      _ ≤ ∑ b, ∑ c, N (s ++ [b]) c :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ c, N s c := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => (hN s hs c).symm

/-- [proved-derived; formal-checked] **`compacted_node_bound`: the compacted tree keeps at most
`2n − 1` nodes over `n ≥ 1` arrivals, at any depth.** For every passage built by arrivals from the
empty standing over addresses reaching the declared depth `D`, with `L` its distinct reached leaves
(the reached nodes at depth `D`) and `n` its arrivals:
* the parting nodes are the nodes above `D` with at least two reached children, and there are at
  most `L − 1` of them, so the parting nodes and the leaves are at most `2L − 1`;
* nothing has arrived exactly when no leaf is reached, and then the root alone is kept (it reads the
  prior); once something has arrived the kept nodes are the parting nodes and the leaves (a unary
  root folds into its chain), at most `2L − 1` for `L ≥ 1`;
* `L ≤ n`, so the compacted tree keeps at most `2n − 1` nodes for `n ≥ 1` and one for `n = 0`,
  whatever `D`. -/
theorem compacted_node_bound (D : ℕ) (ctx : List A → List Ltr)
    (hctx : ∀ h, D ≤ (ctx h).length) (h : List A) :
    (∀ t, t ∈ leafNodes (standingOf ctx h) D [] ↔
      t.length = D ∧ standingOf ctx h t ≠ fun _ => 0) ∧
      (∀ t, t ∈ partingNodes (standingOf ctx h) D [] ↔
        t.length < D ∧ 2 ≤ (reachedKids (standingOf ctx h) t).card) ∧
      (partingNodes (standingOf ctx h) D []).card ≤
        (leafNodes (standingOf ctx h) D []).card - 1 ∧
      (partingNodes (standingOf ctx h) D [] ∪ leafNodes (standingOf ctx h) D []).card ≤
        2 * (leafNodes (standingOf ctx h) D []).card - 1 ∧
      (1 ≤ (leafNodes (standingOf ctx h) D []).card ↔ h ≠ []) ∧
      (h = [] → keptNodes (standingOf ctx h) D = {[]}) ∧
      (h ≠ [] → keptNodes (standingOf ctx h) D =
        partingNodes (standingOf ctx h) D [] ∪ leafNodes (standingOf ctx h) D []) ∧
      (1 ≤ (leafNodes (standingOf ctx h) D []).card →
        (keptNodes (standingOf ctx h) D).card ≤ 2 * (leafNodes (standingOf ctx h) D []).card - 1) ∧
      (leafNodes (standingOf ctx h) D []).card ≤ h.length ∧
      (keptNodes (standingOf ctx h) D).card ≤ max 1 (2 * h.length - 1) := by
  have hN := routed_standingOf hctx h
  set N := standingOf ctx h with hNdef
  have hLn : (leafNodes N D []).card ≤ h.length := by
    have := leaf_card_le_total hN D [] (by simp)
    rwa [hNdef, standingOf_root_total] at this
  have hroot : N [] = (fun _ => 0) ↔ h = [] := by
    have htot : ∑ c, N [] c = h.length := by rw [hNdef, standingOf_root_total]
    constructor
    · intro h0
      rw [h0] at htot
      simpa [eq_comm] using htot
    · rintro rfl
      funext c
      exact (Finset.sum_eq_zero_iff.mp (by simpa using htot)) c (mem_univ c)
  have hPL : (h ≠ [] ∧ (partingNodes N D []).card + 1 ≤ (leafNodes N D []).card) ∨
      (h = [] ∧ partingNodes N D [] = ∅ ∧ leafNodes N D [] = ∅) := by
    by_cases h0 : N [] = fun _ => 0
    · exact Or.inr ⟨hroot.mp h0, nodes_of_zero hN (by simp) h0⟩
    · exact Or.inl ⟨fun he => h0 (hroot.mpr he), parting_card_le hN D [] (by simp) h0⟩
  have hU := Finset.card_union_le (partingNodes N D []) (leafNodes N D [])
  have hKe : h = [] → keptNodes N D = {[]} := fun he => by
    rw [keptNodes, if_pos (hroot.mpr he)]
  have hKn : h ≠ [] → keptNodes N D = partingNodes N D [] ∪ leafNodes N D [] := fun he => by
    rw [keptNodes, if_neg fun h0 => he (hroot.mp h0)]
  refine ⟨fun t => ?_, fun t => ?_, ?_, ?_, ?_, hKe, hKn, fun hL => ?_, hLn, ?_⟩
  · rw [mem_leafNodes hN D [] (by simp) t]
    simp
  · rw [mem_partingNodes hN D [] (by simp) t]
    simp
  · rcases hPL with ⟨-, hPL⟩ | ⟨-, hP0, -⟩
    · omega
    · rw [hP0]
      simp
  · rcases hPL with ⟨-, hPL⟩ | ⟨-, hP0, hL0⟩
    · omega
    · rw [hP0, hL0]
      simp
  · rcases hPL with ⟨he, hPL⟩ | ⟨he, -, hL0⟩
    · exact ⟨fun _ => he, fun _ => by omega⟩
    · rw [hL0]
      simp [he]
  · rcases hPL with ⟨he, hPL⟩ | ⟨-, -, hL0⟩
    · rw [hKn he]
      omega
    · rw [hL0] at hL
      simp at hL
  · rcases hPL with ⟨he, hPL⟩ | ⟨he, -, -⟩
    · rw [hKn he]
      have := le_max_right 1 (2 * h.length - 1)
      omega
    · rw [hKe he]
      simp

end Nodes

section Audit

#print axioms routed_arrive
#print axioms routed_standingOf
#print axioms chain_ratio
#print axioms chain_ratio_dyadic
#print axioms leaf_chain_is_one_node
#print axioms chain_split
#print axioms chain_split_pass
#print axioms compactFrom_eq
#print axioms compact_weight_eq
#print axioms compactFaceFrom_eq
#print axioms compact_face_eq
#print axioms stop_weight_prequential
#print axioms compacted_is_decision_28
#print axioms mem_leafNodes
#print axioms mem_partingNodes
#print axioms parting_card_le
#print axioms leaf_card_le_total
#print axioms compacted_node_bound

end Audit

end Holonics.HNN.LandmarkCompaction
