import Holonics.Compression.Landmark.Context.Tree
import Holonics.Foundation.Standing

/-!
# Compression.Landmark.Context.Standing: each pruned tree is a candidate standing, and the tree is their mixture

[definition; agent-inferred] The unity audit of September 27 (`research/records/2026-09-27_THE_
HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_
PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md`, §2). The receiving tree is the **shift navigator's
landmarks**: a source read cell by cell is a passage of the shift navigator, each tick pushing its
letter onto the address (`shift`, newest first), and a node is a context, the face where every path
ending in that context converges. This owner joins the tree to `Foundation/Standing`. The
computational object is the helical pair interaction's receiving tree; of the winding guide's six
general objects it touches the **tower thread** (a pruned tree restricts the address to its leaf,
a scale restriction) and **faces and placement** (the leaf's face); the rest stay attached.

```text
shift      shift b a = b :: a ;   transportWord shift w a = w ++ a
leaf       leafOf S a : the context at which the pruned tree S stops along the address a (a prefix of a)
source     a tree source over S reads its next-symbol face through the leaf:  θ(leafOf S a)(c)
standing   restrict D (always) ;  leafOf S (when S is closed under the shift)
mixture    W = Σ_S prior_w(S) ∏_t face(σ_(leafOf S (a_t)))(x_t)
```

[proved-derived; formal-checked] What is proved.

1. **The shift's words** (`transportWord_shift`): a word of the shift navigator prepends its letters.
   **The leaf** (`leafOf_take`, `leafOf_prefix`): the leaf context reads at most the tree's depth of
   the address and is a prefix of it.
2. **The address at the declared depth is a standing** (`address_standing`): for every tree source
   over a pruned tree `S` of depth `D`, `restrict D` is a `StandingLaw` on the shift navigator's
   words (`standingLaw_exists_iff_future_factors`): every future face of the source factors through
   the address restricted to `D` letters.
3. **The leaf-context map is a standing when the leaves are closed under the shift**
   (`ShiftClosed`, `leaf_standing`): when the leaf of `b :: a` is a function of `b` and the leaf of
   `a`, `leafOf S` itself is a `StandingLaw` on the shift navigator's words, the coarsest quotient
   that reads the present face.
4. **Each pruned tree's likelihood is its tree source's** (`ownLik_off`, `ownLik_arrive`,
   `tree_source_likelihood`): over a passage whose addresses reach the depth `D`, the product of a
   pruned tree's leaves' own weights under any node law is the sequential likelihood of the passage
   under the tree source over `S` whose face at each cell is the node law's face at the register of
   the leaf context the cell's address reaches.
5. **The tree is the mixture over the candidate standings** (`mixture_over_leaf_standings`): the
   tree's weight is the stop prior's weighted sum, over the pruned trees `S`, of the tree sources'
   likelihoods, each read through its leaf map (item 3's standing, and always through item 2's):
   `Tree.own_mixture_over_trees` read through item 4. Its dominance bound
   (`Tree.own_kraft_and_dominance`) is the code cost of choosing among the candidate standings.

[counterexample; formal-checked] **A leaf map that is not closed under the shift is not a
standing** (`unclosed_leaf_is_not_a_standing`): the depth-three tree over `Bool` that stops at
`[true]` and splits `[false, true]` sends `[true, false]` and `[true, true]` to one leaf `[true]`,
while their shifts by `false` reach the leaves `[false, true, false]` and `[false, true, true]`; a
source that separates those two faces has no standing through the leaf map. The address at the
declared depth (item 2) is its standing.

[proved-standard] Tree sources and the closure of a tree's leaves under the shift (the finite-state
tree sources, FSMX) are Willems, Shtarkov and Tjalkens (1995) and Rissanen (1983). The proofs here
are this owner's.

The Rust consumer is `crates/holonics/src/compression/landmark/context.rs`
(`compression::landmark::context`, whose module doc states the unification).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Standing

open Holonics.Foundation.Chronology (transportWord transportWord_nil transportWord_cons)
open Holonics.Foundation.Standing (StandingLaw causalSignature
  standingLaw_exists_iff_future_factors)
open Holonics.Compression.Landmark.Context.Tree

universe u v

/-! ## 1. The shift navigator and the leaf context -/

section Leaf

variable {Ltr : Type u}

/-- [definition] **The shift navigator** on addresses: a tick pushes its letter onto the address,
newest first. -/
def shift (b : Ltr) (a : List Ltr) : List Ltr := b :: a

/-- [proved-derived; formal-checked] A word of the shift navigator prepends its letters. -/
theorem transportWord_shift (w a : List Ltr) : transportWord shift w a = w ++ a := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [transportWord_cons, ih]; rfl

/-- [definition] **The leaf context** at which the pruned tree `S` stops along the address `a`:
the letters it reads before it reaches a leaf (or before the address runs out). -/
def leafOf : (m : ℕ) → PrunedTree Ltr m → List Ltr → List Ltr
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | m + 1, S, b :: a =>
    Option.elim (S : Option (Ltr → PrunedTree Ltr m)) [] fun f => b :: leafOf m (f b) a

/-- [proved-derived; formal-checked] The leaf reads at most the tree's depth of the address. -/
theorem leafOf_take : ∀ (m : ℕ) (S : PrunedTree Ltr m) (a : List Ltr),
    leafOf m S (a.take m) = leafOf m S a
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | m + 1, S, b :: a => by
    rw [List.take_succ_cons]
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [leafOf, Option.elim]
    | some f => simp only [leafOf, Option.elim, leafOf_take m (f b) a]

/-- [proved-derived; formal-checked] The leaf is a prefix of the address. -/
theorem leafOf_prefix : ∀ (m : ℕ) (S : PrunedTree Ltr m) (a : List Ltr), leafOf m S a <+: a
  | 0, _, _ => List.nil_prefix
  | _ + 1, _, [] => List.nil_prefix
  | m + 1, S, b :: a => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [leafOf, Option.elim]; exact List.nil_prefix
    | some f =>
      simp only [leafOf, Option.elim]
      exact (List.prefix_cons_inj b).mpr (leafOf_prefix m (f b) a)

/-- Two addresses that agree on their first `m` letters, prefixed by one word, reach one leaf. -/
theorem leafOf_append_congr (m : ℕ) (S : PrunedTree Ltr m) (w : List Ltr) {a a' : List Ltr}
    (h : a.take m = a'.take m) : leafOf m S (w ++ a) = leafOf m S (w ++ a') := by
  rw [← leafOf_take m S (w ++ a), ← leafOf_take m S (w ++ a'), List.take_append,
    List.take_append]
  have e : ∀ l : List Ltr, l.take (m - w.length) = (l.take m).take (m - w.length) := fun l => by
    rw [List.take_take, min_eq_left (Nat.sub_le m w.length)]
  rw [e a, e a', h]

end Leaf

/-! ## 2. The address and the leaf map are standings -/

section Standings

variable {Ltr : Type u} {A : Type v}

/-- [proved-derived; formal-checked] **`address_standing`: the address at the declared depth is a
standing.** For every tree source over a pruned tree `S` of depth `m` (its next-symbol face at the
address `a` is `θ (leafOf m S a)`), the address restricted to `m` letters is a `StandingLaw` on the
shift navigator's words: every admitted future face factors through it
(`standingLaw_exists_iff_future_factors`). -/
theorem address_standing (m : ℕ) (S : PrunedTree Ltr m) (θ : List Ltr → A → ℚ) :
    ∃ L : StandingLaw Ltr A (List Ltr) (List Ltr) ℚ,
      L.transport = shift ∧ L.observe = (fun c a => θ (leafOf m S a) c) ∧
        L.retain = restrict m := by
  refine (standingLaw_exists_iff_future_factors _ _ _).2 fun left right h => ?_
  funext request
  simp only [causalSignature, transportWord_shift]
  rw [leafOf_append_congr m S request.2 h]

/-- [definition] **A pruned tree's leaves are closed under the shift** when the leaf of `b :: a` is
a function of `b` and the leaf of `a` (a finite-state tree source). -/
def ShiftClosed (m : ℕ) (S : PrunedTree Ltr m) : Prop :=
  ∀ (b : Ltr) (a a' : List Ltr), leafOf m S a = leafOf m S a' →
    leafOf m S (b :: a) = leafOf m S (b :: a')

/-- Under the closure, one leaf stays one leaf along every word of the shift navigator. -/
theorem leafOf_append_closed {m : ℕ} {S : PrunedTree Ltr m} (hS : ShiftClosed m S) {a a' : List Ltr}
    (h : leafOf m S a = leafOf m S a') :
    ∀ w : List Ltr, leafOf m S (w ++ a) = leafOf m S (w ++ a')
  | [] => h
  | b :: w => hS b _ _ (leafOf_append_closed hS h w)

/-- [proved-derived; formal-checked] **`leaf_standing`: the leaf-context map is a standing when the
leaves are closed under the shift.** For every tree source over a shift-closed pruned tree `S`, the
leaf map `leafOf m S` is a `StandingLaw` on the shift navigator's words: the future faces factor
through the leaf the present address reaches. -/
theorem leaf_standing {m : ℕ} {S : PrunedTree Ltr m} (hS : ShiftClosed m S)
    (θ : List Ltr → A → ℚ) :
    ∃ L : StandingLaw Ltr A (List Ltr) (List Ltr) ℚ,
      L.transport = shift ∧ L.observe = (fun c a => θ (leafOf m S a) c) ∧
        L.retain = leafOf m S := by
  refine (standingLaw_exists_iff_future_factors _ _ _).2 fun left right h => ?_
  funext request
  simp only [causalSignature, transportWord_shift]
  rw [leafOf_append_closed hS h request.2]

end Standings

/-! ### A leaf map that is not closed is not a standing -/

/-- The depth-three tree over `Bool` that stops at `[true]`, stops at `[false, false]` and splits
`[false, true]` to the depth. -/
def unclosedTree : PrunedTree Bool 3 :=
  (some fun b => if b then (none : Option (Bool → PrunedTree Bool 1))
    else (some fun b' => if b' then (some fun _ => PUnit.unit : Option (Bool → PrunedTree Bool 0))
      else (none : Option (Bool → PrunedTree Bool 0)) : Option (Bool → PrunedTree Bool 1)) :
    Option (Bool → PrunedTree Bool 2))

/-- The tree source that separates the leaf `[false, true, false]`. -/
def unclosedSource (ℓ : List Bool) (_ : Bool) : ℚ := if ℓ = [false, true, false] then 1 else 0

/-- [counterexample; formal-checked] **`unclosed_leaf_is_not_a_standing`.** The addresses
`[true, false]` and `[true, true]` reach one leaf `[true]`, but after the shift by `false` they reach
`[false, true, false]` and `[false, true, true]`, which the source separates: no standing law of this
source retains the leaf map. -/
theorem unclosed_leaf_is_not_a_standing :
    leafOf 3 unclosedTree [true, false] = leafOf 3 unclosedTree [true, true] ∧
      ¬ ∃ L : StandingLaw Bool Bool (List Bool) (List Bool) ℚ,
        L.transport = shift ∧ L.observe = (fun c a => unclosedSource (leafOf 3 unclosedTree a) c) ∧
          L.retain = leafOf 3 unclosedTree := by
  have hleaf : leafOf 3 unclosedTree [true, false] = leafOf 3 unclosedTree [true, true] := by
    decide
  refine ⟨hleaf, fun hL => ?_⟩
  have hsig := (standingLaw_exists_iff_future_factors _ _ _).1 hL _ _ hleaf
  have hat := congrFun hsig (true, [false])
  simp only [causalSignature, transportWord_shift] at hat
  have h1 : leafOf 3 unclosedTree ([false] ++ [true, false]) = [false, true, false] := by decide
  have h2 : leafOf 3 unclosedTree ([false] ++ [true, true]) = [false, true, true] := by decide
  rw [h1, h2] at hat
  simp [unclosedSource] at hat

/-! ## 3. The tree is the mixture over the tree sources -/

section Mixture

variable {Ltr : Type u} [Fintype Ltr] [DecidableEq Ltr]

omit [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] An arrival that moves no own weight off the opened path moves no
pruned tree's likelihood off it. -/
theorem ownLik_off {E E' : List Ltr → ℚ} {a : List Ltr}
    (hoff : ∀ s, ¬ a.take s.length = s → E' s = E s) :
    ∀ (m : ℕ) (s : List Ltr) (S : PrunedTree Ltr m), ¬ a.take s.length = s →
      ownLik E' m s S = ownLik E m s S
  | 0, s, _, hs => hoff s hs
  | m + 1, s, S, hs => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [ownLik, Option.elim]; exact hoff s hs
    | some f =>
      simp only [ownLik, Option.elim]
      exact Finset.prod_congr rfl fun b _ =>
        ownLik_off hoff m (s ++ [b]) (f b) (off_path_descendant hs [b])

/-- [proved-derived; formal-checked] **An arrival moves a pruned tree's likelihood by the face at the
leaf the address reaches.** When the own weights agree off the opened path and move by a node's
face `e` on it, a pruned tree rooted on the path, with the address reaching its depth, multiplies
its likelihood by `e` at its leaf context. -/
theorem ownLik_arrive {E E' : List Ltr → ℚ} {a : List Ltr} (e : List Ltr → ℚ)
    (hoff : ∀ s, ¬ a.take s.length = s → E' s = E s)
    (hon : ∀ s, a.take s.length = s → E' s = E s * e s) :
    ∀ (m : ℕ) (s : List Ltr) (S : PrunedTree Ltr m), s.length + m ≤ a.length →
      a.take s.length = s →
        ownLik E' m s S = ownLik E m s S * e (s ++ leafOf m S (a.drop s.length))
  | 0, s, _, _, hs => by simp only [ownLik, leafOf, List.append_nil]; exact hon s hs
  | m + 1, s, S, hlen, hs => by
    have hlt : s.length < a.length := by omega
    have hdrop : a.drop s.length = a[s.length] :: a.drop (s.length + 1) :=
      List.drop_eq_getElem_cons hlt
    have hchild : a.take (s ++ [a[s.length]]).length = s ++ [a[s.length]] := by
      rw [List.length_append, List.length_singleton, List.take_add_one, hs,
        List.getElem?_eq_getElem hlt, Option.toList_some]
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none =>
      rw [hdrop]
      simp only [ownLik, leafOf, Option.elim, List.append_nil]
      exact hon s hs
    | some f =>
      rw [hdrop]
      simp only [ownLik, leafOf, Option.elim]
      have hrest : (s ++ [a[s.length]]).length = s.length + 1 := by simp
      refine prod_update_one _ _ a[s.length] _ ?_ fun b hb => ownLik_off hoff m _ (f b) ?_
      · rw [ownLik_arrive e hoff hon m (s ++ [a[s.length]]) (f a[s.length]) (by rw [hrest]; omega)
          hchild, hrest, List.append_assoc, List.singleton_append]
      · intro hb'
        have hlen' : (s ++ [b]).length = s.length + 1 := by simp
        rw [hlen', List.take_add_one, hs, List.getElem?_eq_getElem hlt, Option.toList_some] at hb'
        exact hb (List.singleton_inj.mp (List.append_cancel_left hb')).symm

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- A pruned tree's likelihood over unit own weights is one. -/
theorem ownLik_one [Fintype Ltr] :
    ∀ (m : ℕ) (s : List Ltr) (S : PrunedTree Ltr m), ownLik (fun _ => (1 : ℚ)) m s S = 1
  | 0, _, _ => rfl
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => rfl
    | some f =>
      simp only [ownLik, Option.elim]
      exact Finset.prod_eq_one fun b _ => ownLik_one m _ (f b)

variable {A : Type v} [Fintype A]

/-- [definition] **The tree source's likelihood of a passage** (newest first): each class read at
the node law's face of the register held by the leaf context its address reaches in the pruned tree
`S`, the register before the class arrives. -/
def treeSourceLik (L : NodeLaw A) (ctx : List A → List Ltr) (m : ℕ) (S : PrunedTree Ltr m) :
    List A → ℚ
  | [] => 1
  | c :: h => treeSourceLik L ctx m S h *
      L.face (lawState L (lawStandingOf L ctx h) (leafOf m S (ctx h))) c

/-- [proved-derived; formal-checked] **`tree_source_likelihood`: a pruned tree's likelihood is its
tree source's.** Over a passage whose addresses reach the depth `m`, the product of the pruned tree's
leaves' own weights under the node law is the likelihood of the passage under the tree source over
`S` read through the node law's leaf registers. -/
theorem tree_source_likelihood (L : NodeLaw A) (ctx : List A → List Ltr) (m : ℕ)
    (hctx : ∀ h, m ≤ (ctx h).length) (S : PrunedTree Ltr m) :
    ∀ h : List A, ownLik (lawOwn L (lawStandingOf L ctx h)) m [] S = treeSourceLik L ctx m S h
  | [] => by
    have e : lawOwn L (lawStandingOf L ctx ([] : List A)) = fun _ => (1 : ℚ) := by
      funext s
      rfl
    rw [e, ownLik_one, treeSourceLik]
  | c :: h => by
    have step := ownLik_arrive (E := lawOwn L (lawStandingOf L ctx h))
      (E' := lawOwn L (lawStandingOf L ctx (c :: h))) (a := ctx h)
      (fun s => L.face (lawState L (lawStandingOf L ctx h) s) c)
      (fun s hs => lawOwn_arrive_off L _ c hs)
      (fun s hs => by simp [lawStandingOf, lawOwn, lawArrive, hs])
      m [] S (by simpa using hctx h) (by simp)
    rw [step, tree_source_likelihood L ctx m hctx S h]
    simp only [List.nil_append, List.length_nil, List.drop_zero]
    rfl

/-- [proved-derived; formal-checked] **`mixture_over_leaf_standings`: the tree is the mixture over
the candidate standings.** Over a passage whose addresses reach the depth `D`, under any node law
and any stop-weight law, the tree's weight at the root is the stop prior's weighted sum over the
pruned trees `S` of the tree sources' likelihoods, each source reading its face through its leaf
map (a standing when `S` is shift-closed, `leaf_standing`, and always through the address at
depth `D`, `address_standing`): `Tree.own_mixture_over_trees` read through
`tree_source_likelihood`. -/
theorem mixture_over_leaf_standings (L : NodeLaw A) (w : ℕ → ℚ) (ctx : List A → List Ltr)
    (D : ℕ) (hctx : ∀ h, D ≤ (ctx h).length) (h : List A) :
    ownWeight w (lawOwn L (lawStandingOf L ctx h)) D [] =
      ∑ S : PrunedTree Ltr D, PrunedTree.prior w D 0 S * treeSourceLik L ctx D S h := by
  rw [own_mixture_over_trees w _ D [], List.length_nil]
  exact Finset.sum_congr rfl fun S _ => by rw [tree_source_likelihood L ctx D hctx S h]

end Mixture

section Audit

#print axioms transportWord_shift
#print axioms leafOf_take
#print axioms leafOf_prefix
#print axioms leafOf_append_congr
#print axioms address_standing
#print axioms leafOf_append_closed
#print axioms leaf_standing
#print axioms unclosed_leaf_is_not_a_standing
#print axioms ownLik_off
#print axioms ownLik_arrive
#print axioms ownLik_one
#print axioms tree_source_likelihood
#print axioms mixture_over_leaf_standings

end Audit

end Holonics.Compression.Landmark.Context.Standing
